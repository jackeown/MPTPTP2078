%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t37_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:52 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       : 1710 (7544 expanded)
%              Number of leaves         :  365 (3164 expanded)
%              Depth                    :   22
%              Number of atoms          : 9635 (34224 expanded)
%              Number of equality atoms :  104 ( 485 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5626,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f172,f179,f186,f193,f200,f207,f214,f227,f228,f243,f256,f269,f288,f292,f302,f312,f319,f320,f321,f328,f344,f357,f361,f374,f393,f403,f414,f432,f439,f453,f464,f472,f504,f518,f532,f547,f557,f565,f576,f590,f597,f615,f622,f636,f643,f651,f658,f666,f692,f696,f796,f861,f864,f866,f876,f892,f923,f926,f927,f930,f933,f942,f952,f966,f1001,f1015,f1022,f1029,f1036,f1044,f1045,f1055,f1069,f1077,f1078,f1082,f1093,f1106,f1123,f1138,f1154,f1161,f1170,f1177,f1185,f1195,f1200,f1227,f1236,f1243,f1263,f1277,f1299,f1313,f1332,f1340,f1352,f1364,f1375,f1380,f1392,f1400,f1504,f1521,f1522,f1533,f1558,f1566,f1573,f1585,f1609,f1623,f1643,f1662,f1669,f1681,f1688,f1696,f1705,f1714,f1754,f1764,f1773,f1783,f1784,f1801,f1833,f1840,f1852,f1854,f1858,f1910,f1914,f1996,f2015,f2020,f2091,f2097,f2102,f2109,f2118,f2126,f2152,f2158,f2168,f2254,f2268,f2327,f2338,f2355,f2368,f2405,f2419,f2439,f2457,f2464,f2475,f2482,f2490,f2500,f2509,f2613,f2627,f2650,f2658,f2665,f2672,f2679,f2688,f2705,f2720,f2728,f2732,f2742,f2750,f2751,f2755,f2780,f2794,f2859,f2873,f2890,f2903,f3012,f3384,f3401,f3409,f3431,f3442,f3468,f3476,f3483,f3492,f3527,f3574,f3577,f3591,f3609,f3615,f3618,f3622,f3636,f3640,f3641,f3662,f3667,f3671,f3680,f3705,f3973,f3978,f3993,f4004,f4011,f4063,f4068,f4072,f4085,f4086,f4090,f4101,f4131,f4139,f4146,f4155,f4165,f4182,f4196,f4209,f4230,f4232,f4236,f4244,f4263,f4275,f4292,f4313,f4318,f4322,f4331,f4383,f4466,f4468,f4469,f4470,f4498,f4630,f4635,f4642,f4667,f4678,f4685,f4693,f4700,f4724,f4736,f4743,f4753,f4763,f4777,f4791,f4800,f4813,f4836,f4847,f4868,f4898,f4906,f4913,f4922,f4936,f4967,f4973,f4980,f4994,f4995,f5023,f5330,f5437,f5461,f5481,f5496,f5502,f5525,f5610,f5615,f5625])).

fof(f5625,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_438 ),
    inference(avatar_split_clause,[],[f5624,f3566,f838,f225,f163,f853,f847,f835,f280])).

fof(f280,plain,
    ( spl15_31
  <=> ~ l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_31])])).

fof(f835,plain,
    ( spl15_110
  <=> v2_struct_0(sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_110])])).

fof(f847,plain,
    ( spl15_115
  <=> ~ v7_waybel_0(sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_115])])).

fof(f853,plain,
    ( spl15_117
  <=> ~ l1_waybel_0(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_117])])).

fof(f163,plain,
    ( spl15_1
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f225,plain,
    ( spl15_18
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f838,plain,
    ( spl15_112
  <=> v4_orders_2(sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_112])])).

fof(f3566,plain,
    ( spl15_438
  <=> v2_struct_0(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_438])])).

fof(f5624,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_438 ),
    inference(subsumption_resolution,[],[f5623,f226])).

fof(f226,plain,
    ( sP0(sK5)
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f225])).

fof(f5623,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_1
    | ~ spl15_112
    | ~ spl15_438 ),
    inference(subsumption_resolution,[],[f5622,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f163])).

fof(f5622,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_112
    | ~ spl15_438 ),
    inference(subsumption_resolution,[],[f5621,f839])).

fof(f839,plain,
    ( v4_orders_2(sK7(sK5))
    | ~ spl15_112 ),
    inference(avatar_component_clause,[],[f838])).

fof(f5621,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_438 ),
    inference(duplicate_literal_removal,[],[f5620])).

fof(f5620,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ sP0(sK5)
    | ~ spl15_438 ),
    inference(resolution,[],[f5616,f105])).

fof(f105,plain,(
    ! [X0,X3] :
      ( m2_yellow_6(sK4(X0,X3),X0,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,sK3(X0)) )
          & l1_waybel_0(sK3(X0),X0)
          & v7_waybel_0(sK3(X0))
          & v4_orders_2(sK3(X0))
          & ~ v2_struct_0(sK3(X0)) ) )
      & ( ! [X3] :
            ( ( v3_yellow_6(sK4(X0,X3),X0)
              & m2_yellow_6(sK4(X0,X3),X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f76,f78,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v3_yellow_6(X2,X0)
            | ~ m2_yellow_6(X2,X0,sK3(X0)) )
        & l1_waybel_0(sK3(X0),X0)
        & v7_waybel_0(sK3(X0))
        & v4_orders_2(sK3(X0))
        & ~ v2_struct_0(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK4(X0,X3),X0)
        & m2_yellow_6(sK4(X0,X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( v3_yellow_6(X2,X0)
              & m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f5616,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK4(sK5,sK7(sK5)),X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_438 ),
    inference(resolution,[],[f3567,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_m2_yellow_6)).

fof(f3567,plain,
    ( v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ spl15_438 ),
    inference(avatar_component_clause,[],[f3566])).

fof(f5615,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | ~ spl15_18
    | ~ spl15_112
    | spl15_589 ),
    inference(avatar_split_clause,[],[f5614,f5608,f838,f225,f853,f847,f835])).

fof(f5608,plain,
    ( spl15_589
  <=> ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_589])])).

fof(f5614,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_589 ),
    inference(subsumption_resolution,[],[f5613,f226])).

fof(f5613,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ sP0(sK5)
    | ~ spl15_112
    | ~ spl15_589 ),
    inference(subsumption_resolution,[],[f5611,f839])).

fof(f5611,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ sP0(sK5)
    | ~ spl15_589 ),
    inference(resolution,[],[f5609,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( v3_yellow_6(sK4(X0,X3),X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f5609,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | ~ spl15_589 ),
    inference(avatar_component_clause,[],[f5608])).

fof(f5610,plain,
    ( spl15_438
    | ~ spl15_589
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_440
    | ~ spl15_586 ),
    inference(avatar_split_clause,[],[f5586,f5523,f3569,f3557,f3545,f177,f170,f163,f5608,f3566])).

fof(f170,plain,
    ( spl15_2
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f177,plain,
    ( spl15_4
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f3545,plain,
    ( spl15_432
  <=> l1_waybel_0(sK4(sK5,sK7(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_432])])).

fof(f3557,plain,
    ( spl15_436
  <=> v7_waybel_0(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_436])])).

fof(f3569,plain,
    ( spl15_440
  <=> v4_orders_2(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_440])])).

fof(f5523,plain,
    ( spl15_586
  <=> k10_yellow_6(sK5,sK4(sK5,sK7(sK5))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_586])])).

fof(f5586,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_440
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5585,f164])).

fof(f5585,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_440
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5584,f171])).

fof(f171,plain,
    ( v2_pre_topc(sK5)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f170])).

fof(f5584,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_4
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_440
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5583,f178])).

fof(f178,plain,
    ( l1_pre_topc(sK5)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f177])).

fof(f5583,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_440
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5582,f3570])).

fof(f3570,plain,
    ( v4_orders_2(sK4(sK5,sK7(sK5)))
    | ~ spl15_440 ),
    inference(avatar_component_clause,[],[f3569])).

fof(f5582,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_432
    | ~ spl15_436
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5581,f3558])).

fof(f3558,plain,
    ( v7_waybel_0(sK4(sK5,sK7(sK5)))
    | ~ spl15_436 ),
    inference(avatar_component_clause,[],[f3557])).

fof(f5581,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_432
    | ~ spl15_586 ),
    inference(subsumption_resolution,[],[f5573,f3546])).

fof(f3546,plain,
    ( l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ spl15_432 ),
    inference(avatar_component_clause,[],[f3545])).

fof(f5573,plain,
    ( ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_586 ),
    inference(trivial_inequality_removal,[],[f5572])).

fof(f5572,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK4(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_586 ),
    inference(superposition,[],[f134,f5524])).

fof(f5524,plain,
    ( k10_yellow_6(sK5,sK4(sK5,sK7(sK5))) = k1_xboole_0
    | ~ spl15_586 ),
    inference(avatar_component_clause,[],[f5523])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k10_yellow_6(X0,X1) != k1_xboole_0
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k10_yellow_6(X0,X1) = k1_xboole_0 )
            & ( k10_yellow_6(X0,X1) != k1_xboole_0
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',d19_yellow_6)).

fof(f5525,plain,
    ( spl15_586
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_434 ),
    inference(avatar_split_clause,[],[f5507,f3554,f401,f391,f5523])).

fof(f391,plain,
    ( spl15_54
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f401,plain,
    ( spl15_56
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_56])])).

fof(f3554,plain,
    ( spl15_434
  <=> v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_434])])).

fof(f5507,plain,
    ( k10_yellow_6(sK5,sK4(sK5,sK7(sK5))) = k1_xboole_0
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_434 ),
    inference(forward_demodulation,[],[f5503,f402])).

fof(f402,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_56 ),
    inference(avatar_component_clause,[],[f401])).

fof(f5503,plain,
    ( k10_yellow_6(sK5,sK4(sK5,sK7(sK5))) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_434 ),
    inference(resolution,[],[f3555,f395])).

fof(f395,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK10(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl15_54 ),
    inference(resolution,[],[f392,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t8_boole)).

fof(f392,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f391])).

fof(f3555,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,sK7(sK5))))
    | ~ spl15_434 ),
    inference(avatar_component_clause,[],[f3554])).

fof(f5502,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | spl15_441 ),
    inference(avatar_split_clause,[],[f5501,f3572,f838,f225,f163,f853,f847,f835,f280])).

fof(f3572,plain,
    ( spl15_441
  <=> ~ v4_orders_2(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_441])])).

fof(f5501,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_441 ),
    inference(subsumption_resolution,[],[f5500,f226])).

fof(f5500,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_1
    | ~ spl15_112
    | ~ spl15_441 ),
    inference(subsumption_resolution,[],[f5499,f164])).

fof(f5499,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_112
    | ~ spl15_441 ),
    inference(subsumption_resolution,[],[f5498,f839])).

fof(f5498,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_441 ),
    inference(resolution,[],[f3573,f735])).

fof(f735,plain,(
    ! [X0,X1] :
      ( v4_orders_2(sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f734])).

fof(f734,plain,(
    ! [X0,X1] :
      ( v4_orders_2(sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f146,f105])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3573,plain,
    ( ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | ~ spl15_441 ),
    inference(avatar_component_clause,[],[f3572])).

fof(f5496,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | spl15_437 ),
    inference(avatar_split_clause,[],[f5449,f3560,f838,f225,f163,f853,f847,f835,f280])).

fof(f3560,plain,
    ( spl15_437
  <=> ~ v7_waybel_0(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_437])])).

fof(f5449,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_437 ),
    inference(subsumption_resolution,[],[f5448,f226])).

fof(f5448,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_1
    | ~ spl15_112
    | ~ spl15_437 ),
    inference(subsumption_resolution,[],[f5447,f164])).

fof(f5447,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_112
    | ~ spl15_437 ),
    inference(subsumption_resolution,[],[f5446,f839])).

fof(f5446,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ sP0(sK5)
    | ~ spl15_437 ),
    inference(resolution,[],[f3561,f737])).

fof(f737,plain,(
    ! [X0,X1] :
      ( v7_waybel_0(sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f736])).

fof(f736,plain,(
    ! [X0,X1] :
      ( v7_waybel_0(sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f147,f105])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f3561,plain,
    ( ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | ~ spl15_437 ),
    inference(avatar_component_clause,[],[f3560])).

fof(f5481,plain,
    ( spl15_36
    | spl15_584
    | ~ spl15_290 ),
    inference(avatar_split_clause,[],[f1863,f1856,f5479,f307])).

fof(f307,plain,
    ( spl15_36
  <=> sP1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f5479,plain,
    ( spl15_584
  <=> ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ m1_subset_1(X4,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_584])])).

fof(f1856,plain,
    ( spl15_290
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r3_waybel_9(sK5,sK7(sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_290])])).

fof(f1863,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ m1_subset_1(X4,u1_struct_0(sK5))
        | sP1(sK5) )
    | ~ spl15_290 ),
    inference(duplicate_literal_removal,[],[f1862])).

fof(f1862,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ m1_subset_1(X4,u1_struct_0(sK5))
        | sP1(sK5)
        | ~ m1_subset_1(X4,u1_struct_0(sK5)) )
    | ~ spl15_290 ),
    inference(resolution,[],[f1857,f132])).

fof(f132,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK7(X0),X2)
      | sP1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ( ! [X2] :
              ( ~ r3_waybel_9(X0,sK7(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(sK7(X0),X0)
          & v7_waybel_0(sK7(X0))
          & v4_orders_2(sK7(X0))
          & ~ v2_struct_0(sK7(X0)) ) )
      & ( ! [X3] :
            ( ( r3_waybel_9(X0,X3,sK8(X0,X3))
              & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f88,f90,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK7(X0),X0)
        & v7_waybel_0(sK7(X0))
        & v4_orders_2(sK7(X0))
        & ~ v2_struct_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK8(X0,X3))
        & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) ) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1857,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK7(sK5),X0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) )
    | ~ spl15_290 ),
    inference(avatar_component_clause,[],[f1856])).

fof(f5461,plain,
    ( spl15_582
    | ~ spl15_4
    | ~ spl15_432 ),
    inference(avatar_split_clause,[],[f5452,f3545,f177,f5459])).

fof(f5459,plain,
    ( spl15_582
  <=> l1_orders_2(sK4(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_582])])).

fof(f5452,plain,
    ( l1_orders_2(sK4(sK5,sK7(sK5)))
    | ~ spl15_4
    | ~ spl15_432 ),
    inference(resolution,[],[f3546,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | l1_orders_2(X0) )
    | ~ spl15_4 ),
    inference(resolution,[],[f231,f178])).

fof(f231,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X2)
      | l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X2) ) ),
    inference(resolution,[],[f122,f121])).

fof(f121,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_l1_pre_topc)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_l1_waybel_0)).

fof(f5437,plain,
    ( spl15_18
    | spl15_127 ),
    inference(avatar_split_clause,[],[f924,f903,f225])).

fof(f903,plain,
    ( spl15_127
  <=> ~ v4_orders_2(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_127])])).

fof(f924,plain,
    ( sP0(sK5)
    | ~ spl15_127 ),
    inference(resolution,[],[f904,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v4_orders_2(sK3(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f904,plain,
    ( ~ v4_orders_2(sK3(sK5))
    | ~ spl15_127 ),
    inference(avatar_component_clause,[],[f903])).

fof(f5330,plain,
    ( ~ spl15_131
    | ~ spl15_129
    | spl15_124
    | ~ spl15_12
    | ~ spl15_126
    | ~ spl15_460
    | ~ spl15_576 ),
    inference(avatar_split_clause,[],[f5101,f4959,f3976,f900,f205,f897,f909,f915])).

fof(f915,plain,
    ( spl15_131
  <=> ~ l1_waybel_0(sK3(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_131])])).

fof(f909,plain,
    ( spl15_129
  <=> ~ v7_waybel_0(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_129])])).

fof(f897,plain,
    ( spl15_124
  <=> v2_struct_0(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_124])])).

fof(f205,plain,
    ( spl15_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_12])])).

fof(f900,plain,
    ( spl15_126
  <=> v4_orders_2(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_126])])).

fof(f3976,plain,
    ( spl15_460
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | r2_hidden(sK8(sK5,X0),k10_yellow_6(sK5,sK9(sK5,X0,sK8(sK5,X0))))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_460])])).

fof(f4959,plain,
    ( spl15_576
  <=> k10_yellow_6(sK5,sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_576])])).

fof(f5101,plain,
    ( v2_struct_0(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_12
    | ~ spl15_126
    | ~ spl15_460
    | ~ spl15_576 ),
    inference(subsumption_resolution,[],[f5100,f901])).

fof(f901,plain,
    ( v4_orders_2(sK3(sK5))
    | ~ spl15_126 ),
    inference(avatar_component_clause,[],[f900])).

fof(f5100,plain,
    ( v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_12
    | ~ spl15_460
    | ~ spl15_576 ),
    inference(subsumption_resolution,[],[f5037,f206])).

fof(f206,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl15_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f5037,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_460
    | ~ spl15_576 ),
    inference(superposition,[],[f3984,f4960])).

fof(f4960,plain,
    ( k10_yellow_6(sK5,sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) = k1_xboole_0
    | ~ spl15_576 ),
    inference(avatar_component_clause,[],[f4959])).

fof(f3984,plain,
    ( ! [X6] :
        ( ~ v1_xboole_0(k10_yellow_6(sK5,sK9(sK5,X6,sK8(sK5,X6))))
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5) )
    | ~ spl15_460 ),
    inference(resolution,[],[f3977,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t7_boole)).

fof(f3977,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK5,X0),k10_yellow_6(sK5,sK9(sK5,X0,sK8(sK5,X0))))
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_460 ),
    inference(avatar_component_clause,[],[f3976])).

fof(f5023,plain,
    ( ~ spl15_131
    | ~ spl15_129
    | spl15_124
    | spl15_1
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_444
    | ~ spl15_574 ),
    inference(avatar_split_clause,[],[f5022,f4953,f3638,f900,f177,f163,f897,f909,f915])).

fof(f3638,plain,
    ( spl15_444
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | m2_yellow_6(sK9(sK5,X0,sK8(sK5,X0)),sK5,X0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_444])])).

fof(f4953,plain,
    ( spl15_574
  <=> v2_struct_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_574])])).

fof(f5022,plain,
    ( v2_struct_0(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_1
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_444
    | ~ spl15_574 ),
    inference(subsumption_resolution,[],[f5021,f901])).

fof(f5021,plain,
    ( ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_1
    | ~ spl15_4
    | ~ spl15_444
    | ~ spl15_574 ),
    inference(duplicate_literal_removal,[],[f5017])).

fof(f5017,plain,
    ( ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ spl15_1
    | ~ spl15_4
    | ~ spl15_444
    | ~ spl15_574 ),
    inference(resolution,[],[f5016,f3639])).

fof(f3639,plain,
    ( ! [X0] :
        ( m2_yellow_6(sK9(sK5,X0,sK8(sK5,X0)),sK5,X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_444 ),
    inference(avatar_component_clause,[],[f3638])).

fof(f5016,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5,X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_1
    | ~ spl15_4
    | ~ spl15_574 ),
    inference(subsumption_resolution,[],[f5014,f164])).

fof(f5014,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m2_yellow_6(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5,X0)
        | v2_struct_0(sK5)
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_4
    | ~ spl15_574 ),
    inference(resolution,[],[f5012,f178])).

fof(f5012,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ m2_yellow_6(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),X2,X1)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X1,X2) )
    | ~ spl15_574 ),
    inference(resolution,[],[f4996,f121])).

fof(f4996,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ m2_yellow_6(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),X0,X1)
        | v2_struct_0(X0) )
    | ~ spl15_574 ),
    inference(resolution,[],[f4954,f145])).

fof(f4954,plain,
    ( v2_struct_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ spl15_574 ),
    inference(avatar_component_clause,[],[f4953])).

fof(f4995,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | ~ spl15_126
    | ~ spl15_448
    | spl15_573 ),
    inference(avatar_split_clause,[],[f4985,f4947,f3665,f900,f915,f909,f897])).

fof(f3665,plain,
    ( spl15_448
  <=> ! [X3] :
        ( ~ l1_waybel_0(X3,sK5)
        | v4_orders_2(sK9(sK5,X3,sK8(sK5,X3)))
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_448])])).

fof(f4947,plain,
    ( spl15_573
  <=> ~ v4_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_573])])).

fof(f4985,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_126
    | ~ spl15_448
    | ~ spl15_573 ),
    inference(subsumption_resolution,[],[f4982,f901])).

fof(f4982,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_448
    | ~ spl15_573 ),
    inference(resolution,[],[f4948,f3666])).

fof(f3666,plain,
    ( ! [X3] :
        ( v4_orders_2(sK9(sK5,X3,sK8(sK5,X3)))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | ~ spl15_448 ),
    inference(avatar_component_clause,[],[f3665])).

fof(f4948,plain,
    ( ~ v4_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ spl15_573 ),
    inference(avatar_component_clause,[],[f4947])).

fof(f4994,plain,
    ( spl15_580
    | ~ spl15_4
    | ~ spl15_578 ),
    inference(avatar_split_clause,[],[f4986,f4962,f177,f4992])).

fof(f4992,plain,
    ( spl15_580
  <=> l1_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_580])])).

fof(f4962,plain,
    ( spl15_578
  <=> l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_578])])).

fof(f4986,plain,
    ( l1_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ spl15_4
    | ~ spl15_578 ),
    inference(resolution,[],[f4963,f271])).

fof(f4963,plain,
    ( l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5)
    | ~ spl15_578 ),
    inference(avatar_component_clause,[],[f4962])).

fof(f4980,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | ~ spl15_126
    | ~ spl15_450
    | spl15_579 ),
    inference(avatar_split_clause,[],[f4979,f4965,f3669,f900,f915,f909,f897])).

fof(f3669,plain,
    ( spl15_450
  <=> ! [X1] :
        ( ~ l1_waybel_0(X1,sK5)
        | l1_waybel_0(sK9(sK5,X1,sK8(sK5,X1)),sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_450])])).

fof(f4965,plain,
    ( spl15_579
  <=> ~ l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_579])])).

fof(f4979,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_126
    | ~ spl15_450
    | ~ spl15_579 ),
    inference(subsumption_resolution,[],[f4976,f901])).

fof(f4976,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_450
    | ~ spl15_579 ),
    inference(resolution,[],[f4966,f3670])).

fof(f3670,plain,
    ( ! [X1] :
        ( l1_waybel_0(sK9(sK5,X1,sK8(sK5,X1)),sK5)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1) )
    | ~ spl15_450 ),
    inference(avatar_component_clause,[],[f3669])).

fof(f4966,plain,
    ( ~ l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5)
    | ~ spl15_579 ),
    inference(avatar_component_clause,[],[f4965])).

fof(f4973,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | ~ spl15_126
    | ~ spl15_446
    | spl15_571 ),
    inference(avatar_split_clause,[],[f4972,f4941,f3660,f900,f915,f909,f897])).

fof(f3660,plain,
    ( spl15_446
  <=> ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | v7_waybel_0(sK9(sK5,X2,sK8(sK5,X2)))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_446])])).

fof(f4941,plain,
    ( spl15_571
  <=> ~ v7_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_571])])).

fof(f4972,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_126
    | ~ spl15_446
    | ~ spl15_571 ),
    inference(subsumption_resolution,[],[f4969,f901])).

fof(f4969,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_446
    | ~ spl15_571 ),
    inference(resolution,[],[f4942,f3661])).

fof(f3661,plain,
    ( ! [X2] :
        ( v7_waybel_0(sK9(sK5,X2,sK8(sK5,X2)))
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2) )
    | ~ spl15_446 ),
    inference(avatar_component_clause,[],[f3660])).

fof(f4942,plain,
    ( ~ v7_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ spl15_571 ),
    inference(avatar_component_clause,[],[f4941])).

fof(f4967,plain,
    ( ~ spl15_129
    | spl15_124
    | ~ spl15_131
    | ~ spl15_571
    | ~ spl15_573
    | spl15_574
    | spl15_576
    | ~ spl15_579
    | ~ spl15_126
    | ~ spl15_444
    | ~ spl15_452 ),
    inference(avatar_split_clause,[],[f3692,f3678,f3638,f900,f4965,f4959,f4953,f4947,f4941,f915,f897,f909])).

fof(f3678,plain,
    ( spl15_452
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ m2_yellow_6(X0,sK5,sK3(sK5))
        | k10_yellow_6(sK5,X0) = k1_xboole_0
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_452])])).

fof(f3692,plain,
    ( ~ l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5)
    | k10_yellow_6(sK5,sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) = k1_xboole_0
    | v2_struct_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ v7_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ spl15_126
    | ~ spl15_444
    | ~ spl15_452 ),
    inference(subsumption_resolution,[],[f3684,f901])).

fof(f3684,plain,
    ( ~ l1_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))),sK5)
    | k10_yellow_6(sK5,sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5)))) = k1_xboole_0
    | v2_struct_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ v7_waybel_0(sK9(sK5,sK3(sK5),sK8(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | v2_struct_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | ~ v7_waybel_0(sK3(sK5))
    | ~ spl15_444
    | ~ spl15_452 ),
    inference(resolution,[],[f3679,f3639])).

fof(f3679,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK5,sK3(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | k10_yellow_6(sK5,X0) = k1_xboole_0
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_452 ),
    inference(avatar_component_clause,[],[f3678])).

fof(f4936,plain,
    ( spl15_568
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(avatar_split_clause,[],[f4929,f4845,f4716,f4099,f3694,f1241,f940,f921,f177,f170,f163,f4934])).

fof(f4934,plain,
    ( spl15_568
  <=> r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_568])])).

fof(f921,plain,
    ( spl15_132
  <=> v7_waybel_0(sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_132])])).

fof(f940,plain,
    ( spl15_134
  <=> v4_orders_2(sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_134])])).

fof(f1241,plain,
    ( spl15_194
  <=> l1_waybel_0(sK11(sK5,sK3(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_194])])).

fof(f3694,plain,
    ( spl15_455
  <=> ~ v2_struct_0(sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_455])])).

fof(f4099,plain,
    ( spl15_476
  <=> m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_476])])).

fof(f4716,plain,
    ( spl15_538
  <=> m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_538])])).

fof(f4845,plain,
    ( spl15_556
  <=> r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_556])])).

fof(f4929,plain,
    ( r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4928,f3695])).

fof(f3695,plain,
    ( ~ v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_455 ),
    inference(avatar_component_clause,[],[f3694])).

fof(f4928,plain,
    ( v2_struct_0(sK11(sK5,sK3(sK5)))
    | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4927,f941])).

fof(f941,plain,
    ( v4_orders_2(sK11(sK5,sK3(sK5)))
    | ~ spl15_134 ),
    inference(avatar_component_clause,[],[f940])).

fof(f4927,plain,
    ( ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4926,f922])).

fof(f922,plain,
    ( v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_132 ),
    inference(avatar_component_clause,[],[f921])).

fof(f4926,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4923,f1242])).

fof(f1242,plain,
    ( l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ spl15_194 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f4923,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_476
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(resolution,[],[f4851,f4100])).

fof(f4100,plain,
    ( m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,sK11(sK5,sK3(sK5)))
    | ~ spl15_476 ),
    inference(avatar_component_clause,[],[f4099])).

fof(f4851,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK5,X0,o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4848,f4717])).

fof(f4717,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_538 ),
    inference(avatar_component_clause,[],[f4716])).

fof(f4848,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
        | ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK5,X0,o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_556 ),
    inference(resolution,[],[f4846,f1708])).

fof(f1708,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ m2_yellow_6(X0,sK5,X2)
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | r3_waybel_9(sK5,X2,X1) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1707,f164])).

fof(f1707,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ m2_yellow_6(X0,sK5,X2)
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | r3_waybel_9(sK5,X2,X1)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1706,f178])).

fof(f1706,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ m2_yellow_6(X0,sK5,X2)
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK5)
        | r3_waybel_9(sK5,X2,X1)
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f139,f171])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r3_waybel_9(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t31_waybel_9)).

fof(f4846,plain,
    ( r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_556 ),
    inference(avatar_component_clause,[],[f4845])).

fof(f4922,plain,
    ( spl15_566
    | ~ spl15_4
    | ~ spl15_564 ),
    inference(avatar_split_clause,[],[f4914,f4911,f177,f4920])).

fof(f4920,plain,
    ( spl15_566
  <=> l1_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_566])])).

fof(f4911,plain,
    ( spl15_564
  <=> l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_564])])).

fof(f4914,plain,
    ( l1_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ spl15_4
    | ~ spl15_564 ),
    inference(resolution,[],[f4912,f271])).

fof(f4912,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ spl15_564 ),
    inference(avatar_component_clause,[],[f4911])).

fof(f4913,plain,
    ( ~ spl15_31
    | spl15_564
    | spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | spl15_545
    | ~ spl15_558 ),
    inference(avatar_split_clause,[],[f4881,f4866,f4738,f4144,f4137,f4129,f163,f4911,f280])).

fof(f4129,plain,
    ( spl15_478
  <=> v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_478])])).

fof(f4137,plain,
    ( spl15_480
  <=> v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_480])])).

fof(f4144,plain,
    ( spl15_482
  <=> l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_482])])).

fof(f4738,plain,
    ( spl15_545
  <=> ~ v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_545])])).

fof(f4866,plain,
    ( spl15_558
  <=> m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_558])])).

fof(f4881,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4880,f164])).

fof(f4880,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4879,f4739])).

fof(f4739,plain,
    ( ~ v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_545 ),
    inference(avatar_component_clause,[],[f4738])).

fof(f4879,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4878,f4138])).

fof(f4138,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_480 ),
    inference(avatar_component_clause,[],[f4137])).

fof(f4878,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4877,f4130])).

fof(f4130,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_478 ),
    inference(avatar_component_clause,[],[f4129])).

fof(f4877,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4870,f4145])).

fof(f4145,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ spl15_482 ),
    inference(avatar_component_clause,[],[f4144])).

fof(f4870,plain,
    ( l1_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_558 ),
    inference(resolution,[],[f4867,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4867,plain,
    ( m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_558 ),
    inference(avatar_component_clause,[],[f4866])).

fof(f4906,plain,
    ( ~ spl15_31
    | spl15_562
    | spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | spl15_545
    | ~ spl15_558 ),
    inference(avatar_split_clause,[],[f4891,f4866,f4738,f4144,f4137,f4129,f163,f4904,f280])).

fof(f4904,plain,
    ( spl15_562
  <=> v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_562])])).

fof(f4891,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4890,f164])).

fof(f4890,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4889,f4739])).

fof(f4889,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4888,f4138])).

fof(f4888,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4887,f4130])).

fof(f4887,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4872,f4145])).

fof(f4872,plain,
    ( v4_orders_2(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_558 ),
    inference(resolution,[],[f4867,f146])).

fof(f4898,plain,
    ( ~ spl15_31
    | spl15_560
    | spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | spl15_545
    | ~ spl15_558 ),
    inference(avatar_split_clause,[],[f4886,f4866,f4738,f4144,f4137,f4129,f163,f4896,f280])).

fof(f4896,plain,
    ( spl15_560
  <=> v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_560])])).

fof(f4886,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4885,f164])).

fof(f4885,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_545
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4884,f4739])).

fof(f4884,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4883,f4138])).

fof(f4883,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_478
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4882,f4130])).

fof(f4882,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_482
    | ~ spl15_558 ),
    inference(subsumption_resolution,[],[f4871,f4145])).

fof(f4871,plain,
    ( v7_waybel_0(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_558 ),
    inference(resolution,[],[f4867,f147])).

fof(f4868,plain,
    ( spl15_558
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_538
    | spl15_545
    | ~ spl15_556 ),
    inference(avatar_split_clause,[],[f4861,f4845,f4738,f4716,f4144,f4137,f4129,f177,f170,f163,f4866])).

fof(f4861,plain,
    ( m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_538
    | ~ spl15_545
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4860,f4739])).

fof(f4860,plain,
    ( v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4859,f4138])).

fof(f4859,plain,
    ( ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_482
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4858,f4130])).

fof(f4858,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_482
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4857,f4145])).

fof(f4857,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_538
    | ~ spl15_556 ),
    inference(subsumption_resolution,[],[f4850,f4717])).

fof(f4850,plain,
    ( ~ m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | m2_yellow_6(sK9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))),sK5,sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_556 ),
    inference(resolution,[],[f4846,f1444])).

fof(f1444,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X0,X1),sK5,X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1443,f164])).

fof(f1443,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X0,X1),sK5,X0)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1442,f178])).

fof(f1442,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | m2_yellow_6(sK9(sK5,X0,X1),sK5,X0)
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f137,f171])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m2_yellow_6(sK9(X0,X1,X2),X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK9(X0,X1,X2)))
                & m2_yellow_6(sK9(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f50,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK9(X0,X1,X2)))
        & m2_yellow_6(sK9(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t32_waybel_9)).

fof(f4847,plain,
    ( spl15_556
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_528
    | ~ spl15_538
    | spl15_545 ),
    inference(avatar_split_clause,[],[f4834,f4738,f4716,f4659,f4144,f4137,f4129,f177,f170,f163,f4845])).

fof(f4659,plain,
    ( spl15_528
  <=> r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_528])])).

fof(f4834,plain,
    ( r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_528
    | ~ spl15_538
    | ~ spl15_545 ),
    inference(subsumption_resolution,[],[f4833,f4739])).

fof(f4833,plain,
    ( v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_528
    | ~ spl15_538 ),
    inference(subsumption_resolution,[],[f4832,f4138])).

fof(f4832,plain,
    ( ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_478
    | ~ spl15_482
    | ~ spl15_528
    | ~ spl15_538 ),
    inference(subsumption_resolution,[],[f4831,f4130])).

fof(f4831,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_482
    | ~ spl15_528
    | ~ spl15_538 ),
    inference(subsumption_resolution,[],[f4830,f4145])).

fof(f4830,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_528
    | ~ spl15_538 ),
    inference(subsumption_resolution,[],[f4824,f4717])).

fof(f4824,plain,
    ( ~ m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK3(sK5))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_528 ),
    inference(resolution,[],[f4660,f1322])).

fof(f1322,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK5,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1321,f164])).

fof(f1321,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK5,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,X0)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1320,f178])).

fof(f1320,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK5,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK5)
        | r3_waybel_9(sK5,X1,X0)
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f136,f171])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r3_waybel_9(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t29_waybel_9)).

fof(f4660,plain,
    ( r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_528 ),
    inference(avatar_component_clause,[],[f4659])).

fof(f4836,plain,
    ( spl15_530
    | spl15_546
    | ~ spl15_164
    | ~ spl15_540 ),
    inference(avatar_split_clause,[],[f4754,f4719,f1080,f4761,f4665])).

fof(f4665,plain,
    ( spl15_530
  <=> v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_530])])).

fof(f4761,plain,
    ( spl15_546
  <=> r2_hidden(sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_546])])).

fof(f1080,plain,
    ( spl15_164
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_xboole_0)
        | r2_hidden(sK10(X1),u1_struct_0(sK5))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_164])])).

fof(f4719,plain,
    ( spl15_540
  <=> m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_540])])).

fof(f4754,plain,
    ( r2_hidden(sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))),u1_struct_0(sK5))
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_164
    | ~ spl15_540 ),
    inference(resolution,[],[f4720,f1081])).

fof(f1081,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_xboole_0)
        | r2_hidden(sK10(X1),u1_struct_0(sK5))
        | v1_xboole_0(X1) )
    | ~ spl15_164 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f4720,plain,
    ( m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0)
    | ~ spl15_540 ),
    inference(avatar_component_clause,[],[f4719])).

fof(f4813,plain,
    ( ~ spl15_555
    | ~ spl15_552 ),
    inference(avatar_split_clause,[],[f4804,f4798,f4811])).

fof(f4811,plain,
    ( spl15_555
  <=> ~ r2_hidden(u1_struct_0(sK5),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_555])])).

fof(f4798,plain,
    ( spl15_552
  <=> r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_552])])).

fof(f4804,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_552 ),
    inference(resolution,[],[f4799,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',antisymmetry_r2_hidden)).

fof(f4799,plain,
    ( r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_552 ),
    inference(avatar_component_clause,[],[f4798])).

fof(f4800,plain,
    ( spl15_552
    | spl15_147
    | ~ spl15_538 ),
    inference(avatar_split_clause,[],[f4793,f4716,f1004,f4798])).

fof(f1004,plain,
    ( spl15_147
  <=> ~ v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_147])])).

fof(f4793,plain,
    ( r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_147
    | ~ spl15_538 ),
    inference(subsumption_resolution,[],[f4792,f1005])).

fof(f1005,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_147 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f4792,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_538 ),
    inference(resolution,[],[f4717,f143])).

fof(f143,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t2_subset)).

fof(f4791,plain,
    ( ~ spl15_551
    | ~ spl15_546 ),
    inference(avatar_split_clause,[],[f4782,f4761,f4789])).

fof(f4789,plain,
    ( spl15_551
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_551])])).

fof(f4782,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))))
    | ~ spl15_546 ),
    inference(resolution,[],[f4762,f141])).

fof(f4762,plain,
    ( r2_hidden(sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))),u1_struct_0(sK5))
    | ~ spl15_546 ),
    inference(avatar_component_clause,[],[f4761])).

fof(f4777,plain,
    ( spl15_548
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_530 ),
    inference(avatar_split_clause,[],[f4768,f4665,f401,f391,f4775])).

fof(f4775,plain,
    ( spl15_548
  <=> k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_548])])).

fof(f4768,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))) = k1_xboole_0
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_530 ),
    inference(forward_demodulation,[],[f4764,f402])).

fof(f4764,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_530 ),
    inference(resolution,[],[f4666,f395])).

fof(f4666,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_530 ),
    inference(avatar_component_clause,[],[f4665])).

fof(f4763,plain,
    ( spl15_546
    | ~ spl15_164
    | spl15_531
    | ~ spl15_540 ),
    inference(avatar_split_clause,[],[f4756,f4719,f4662,f1080,f4761])).

fof(f4662,plain,
    ( spl15_531
  <=> ~ v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_531])])).

fof(f4756,plain,
    ( r2_hidden(sK10(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5))))),u1_struct_0(sK5))
    | ~ spl15_164
    | ~ spl15_531
    | ~ spl15_540 ),
    inference(subsumption_resolution,[],[f4754,f4663])).

fof(f4663,plain,
    ( ~ v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_531 ),
    inference(avatar_component_clause,[],[f4662])).

fof(f4753,plain,
    ( ~ spl15_31
    | spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(avatar_split_clause,[],[f4752,f4741,f4099,f3694,f1241,f940,f921,f163,f280])).

fof(f4741,plain,
    ( spl15_544
  <=> v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_544])])).

fof(f4752,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(subsumption_resolution,[],[f4751,f164])).

fof(f4751,plain,
    ( ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(subsumption_resolution,[],[f4750,f3695])).

fof(f4750,plain,
    ( v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(subsumption_resolution,[],[f4749,f941])).

fof(f4749,plain,
    ( ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(subsumption_resolution,[],[f4748,f922])).

fof(f4748,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_194
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(subsumption_resolution,[],[f4746,f1242])).

fof(f4746,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_476
    | ~ spl15_544 ),
    inference(resolution,[],[f4744,f4100])).

fof(f4744,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_544 ),
    inference(resolution,[],[f4742,f145])).

fof(f4742,plain,
    ( v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_544 ),
    inference(avatar_component_clause,[],[f4741])).

fof(f4743,plain,
    ( spl15_544
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | spl15_541 ),
    inference(avatar_split_clause,[],[f4729,f4722,f4144,f4137,f4129,f964,f177,f170,f163,f4741])).

fof(f964,plain,
    ( spl15_140
  <=> k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_140])])).

fof(f4722,plain,
    ( spl15_541
  <=> ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_541])])).

fof(f4729,plain,
    ( v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_482
    | ~ spl15_541 ),
    inference(subsumption_resolution,[],[f4728,f4145])).

fof(f4728,plain,
    ( v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_478
    | ~ spl15_480
    | ~ spl15_541 ),
    inference(subsumption_resolution,[],[f4727,f4138])).

fof(f4727,plain,
    ( ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_478
    | ~ spl15_541 ),
    inference(subsumption_resolution,[],[f4725,f4130])).

fof(f4725,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_541 ),
    inference(resolution,[],[f4723,f968])).

fof(f968,plain,
    ( ! [X0] :
        ( m1_subset_1(k10_yellow_6(sK5,X0),k1_xboole_0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140 ),
    inference(superposition,[],[f869,f965])).

fof(f965,plain,
    ( k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK5))
    | ~ spl15_140 ),
    inference(avatar_component_clause,[],[f964])).

fof(f869,plain,
    ( ! [X0] :
        ( m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f868,f164])).

fof(f868,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f867,f178])).

fof(f867,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f144,f171])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_k10_yellow_6)).

fof(f4723,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0)
    | ~ spl15_541 ),
    inference(avatar_component_clause,[],[f4722])).

fof(f4736,plain,
    ( ~ spl15_543
    | spl15_541 ),
    inference(avatar_split_clause,[],[f4726,f4722,f4734])).

fof(f4734,plain,
    ( spl15_543
  <=> ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_543])])).

fof(f4726,plain,
    ( ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0)
    | ~ spl15_541 ),
    inference(resolution,[],[f4723,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t1_subset)).

fof(f4724,plain,
    ( spl15_538
    | ~ spl15_541
    | ~ spl15_140
    | ~ spl15_528 ),
    inference(avatar_split_clause,[],[f4707,f4659,f964,f4722,f4716])).

fof(f4707,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_xboole_0)
    | m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_528 ),
    inference(superposition,[],[f4670,f965])).

fof(f4670,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(X0))
        | m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),X0) )
    | ~ spl15_528 ),
    inference(resolution,[],[f4660,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t4_subset)).

fof(f4700,plain,
    ( ~ spl15_537
    | ~ spl15_528 ),
    inference(avatar_split_clause,[],[f4672,f4659,f4698])).

fof(f4698,plain,
    ( spl15_537
  <=> ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_537])])).

fof(f4672,plain,
    ( ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_528 ),
    inference(resolution,[],[f4660,f141])).

fof(f4693,plain,
    ( ~ spl15_535
    | spl15_533 ),
    inference(avatar_split_clause,[],[f4686,f4683,f4691])).

fof(f4691,plain,
    ( spl15_535
  <=> ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_535])])).

fof(f4683,plain,
    ( spl15_533
  <=> ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_533])])).

fof(f4686,plain,
    ( ~ r2_hidden(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_533 ),
    inference(resolution,[],[f4684,f142])).

fof(f4684,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_533 ),
    inference(avatar_component_clause,[],[f4683])).

fof(f4685,plain,
    ( ~ spl15_533
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_528 ),
    inference(avatar_split_clause,[],[f4677,f4659,f401,f391,f4683])).

fof(f4677,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_528 ),
    inference(forward_demodulation,[],[f4669,f402])).

fof(f4669,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_528 ),
    inference(resolution,[],[f4660,f394])).

fof(f394,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl15_54 ),
    inference(resolution,[],[f392,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t5_subset)).

fof(f4678,plain,
    ( ~ spl15_531
    | ~ spl15_528 ),
    inference(avatar_split_clause,[],[f4673,f4659,f4662])).

fof(f4673,plain,
    ( ~ v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_528 ),
    inference(resolution,[],[f4660,f151])).

fof(f4667,plain,
    ( spl15_528
    | spl15_530
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476 ),
    inference(avatar_split_clause,[],[f4109,f4099,f3694,f1241,f940,f921,f177,f170,f163,f4665,f4659])).

fof(f4109,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4108,f1242])).

fof(f4108,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4107,f3695])).

fof(f4107,plain,
    ( v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4106,f941])).

fof(f4106,plain,
    ( ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4102,f922])).

fof(f4102,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK3(sK5)),sK11(sK5,sK11(sK5,sK3(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK3(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_476 ),
    inference(resolution,[],[f4100,f1843])).

fof(f1843,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(X1,sK5,X0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | r2_hidden(o_3_4_yellow19(sK5,X0,X1),k10_yellow_6(sK5,X1)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1842,f164])).

fof(f1842,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ m2_yellow_6(X1,sK5,X0)
        | v2_struct_0(sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | r2_hidden(o_3_4_yellow19(sK5,X0,X1),k10_yellow_6(sK5,X1)) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1841,f178])).

fof(f1841,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | ~ m2_yellow_6(X1,sK5,X0)
        | v2_struct_0(sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | r2_hidden(o_3_4_yellow19(sK5,X0,X1),k10_yellow_6(sK5,X1)) )
    | ~ spl15_2 ),
    inference(resolution,[],[f1219,f171])).

fof(f1219,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ m2_yellow_6(X0,X1,X2)
      | v2_struct_0(X1)
      | v1_xboole_0(k10_yellow_6(X1,X0))
      | r2_hidden(o_3_4_yellow19(X1,X2,X0),k10_yellow_6(X1,X0)) ) ),
    inference(resolution,[],[f152,f143])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(o_3_4_yellow19(X0,X1,X2),k10_yellow_6(X0,X2))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(o_3_4_yellow19(X0,X1,X2),k10_yellow_6(X0,X2))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(o_3_4_yellow19(X0,X1,X2),k10_yellow_6(X0,X2))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m2_yellow_6(X2,X0,X1)
        & l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_3_4_yellow19(X0,X1,X2),k10_yellow_6(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_o_3_4_yellow19)).

fof(f4642,plain,
    ( ~ spl15_31
    | spl15_526
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(avatar_split_clause,[],[f4624,f3991,f307,f177,f170,f163,f4640,f280])).

fof(f4640,plain,
    ( spl15_526
  <=> ! [X3,X4] :
        ( ~ v7_waybel_0(X3)
        | l1_waybel_0(sK9(sK5,X4,sK8(sK5,X3)),sK5)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X4,sK5)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ m2_yellow_6(X3,sK5,X4)
        | ~ l1_waybel_0(X3,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_526])])).

fof(f3991,plain,
    ( spl15_462
  <=> ! [X1,X0] :
        ( ~ m2_yellow_6(X0,sK5,X1)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | r3_waybel_9(sK5,X1,sK8(sK5,X0))
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_462])])).

fof(f4624,plain,
    ( ! [X4,X3] :
        ( ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ m2_yellow_6(X3,sK5,X4)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ v7_waybel_0(X4)
        | ~ l1_waybel_0(X4,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | l1_waybel_0(sK9(sK5,X4,sK8(sK5,X3)),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(subsumption_resolution,[],[f4621,f164])).

fof(f4621,plain,
    ( ! [X4,X3] :
        ( ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ m2_yellow_6(X3,sK5,X4)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ v7_waybel_0(X4)
        | ~ l1_waybel_0(X4,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | l1_waybel_0(sK9(sK5,X4,sK8(sK5,X3)),sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(duplicate_literal_removal,[],[f4616])).

fof(f4616,plain,
    ( ! [X4,X3] :
        ( ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ m2_yellow_6(X3,sK5,X4)
        | v2_struct_0(X4)
        | ~ v4_orders_2(X4)
        | ~ v7_waybel_0(X4)
        | ~ l1_waybel_0(X4,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | l1_waybel_0(sK9(sK5,X4,sK8(sK5,X3)),sK5)
        | ~ l1_waybel_0(X4,sK5)
        | ~ v7_waybel_0(X4)
        | ~ v4_orders_2(X4)
        | v2_struct_0(X4)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(resolution,[],[f4584,f148])).

fof(f4584,plain,
    ( ! [X0,X1] :
        ( m2_yellow_6(sK9(sK5,X1,sK8(sK5,X0)),sK5,X1)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ m2_yellow_6(X0,sK5,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(subsumption_resolution,[],[f4583,f308])).

fof(f308,plain,
    ( sP1(sK5)
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f307])).

fof(f4583,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ m2_yellow_6(X0,sK5,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X1,sK8(sK5,X0)),sK5,X1)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_462 ),
    inference(duplicate_literal_removal,[],[f4581])).

fof(f4581,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ m2_yellow_6(X0,sK5,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X1,sK8(sK5,X0)),sK5,X1)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_462 ),
    inference(resolution,[],[f4079,f126])).

fof(f126,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK8(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f4079,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(sK8(sK5,X5),u1_struct_0(sK5))
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ m2_yellow_6(X5,sK5,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5)
        | v2_struct_0(X5)
        | m2_yellow_6(sK9(sK5,X6,sK8(sK5,X5)),sK5,X6) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_462 ),
    inference(duplicate_literal_removal,[],[f4077])).

fof(f4077,plain,
    ( ! [X6,X5] :
        ( v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ m2_yellow_6(X5,sK5,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5)
        | ~ m1_subset_1(sK8(sK5,X5),u1_struct_0(sK5))
        | ~ l1_waybel_0(X6,sK5)
        | ~ v7_waybel_0(X6)
        | ~ v4_orders_2(X6)
        | v2_struct_0(X6)
        | m2_yellow_6(sK9(sK5,X6,sK8(sK5,X5)),sK5,X6) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_462 ),
    inference(resolution,[],[f3992,f1444])).

fof(f3992,plain,
    ( ! [X0,X1] :
        ( r3_waybel_9(sK5,X1,sK8(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ m2_yellow_6(X0,sK5,X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5) )
    | ~ spl15_462 ),
    inference(avatar_component_clause,[],[f3991])).

fof(f4635,plain,
    ( ~ spl15_31
    | spl15_524
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(avatar_split_clause,[],[f4626,f3991,f307,f177,f170,f163,f4633,f280])).

fof(f4633,plain,
    ( spl15_524
  <=> ! [X7,X8] :
        ( ~ v7_waybel_0(X7)
        | v4_orders_2(sK9(sK5,X8,sK8(sK5,X7)))
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X8,sK5)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ m2_yellow_6(X7,sK5,X8)
        | ~ l1_waybel_0(X7,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_524])])).

fof(f4626,plain,
    ( ! [X8,X7] :
        ( ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ m2_yellow_6(X7,sK5,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,sK5)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | v4_orders_2(sK9(sK5,X8,sK8(sK5,X7)))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(subsumption_resolution,[],[f4619,f164])).

fof(f4619,plain,
    ( ! [X8,X7] :
        ( ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ m2_yellow_6(X7,sK5,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,sK5)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | v4_orders_2(sK9(sK5,X8,sK8(sK5,X7)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(duplicate_literal_removal,[],[f4618])).

fof(f4618,plain,
    ( ! [X8,X7] :
        ( ~ v7_waybel_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ m2_yellow_6(X7,sK5,X8)
        | v2_struct_0(X8)
        | ~ v4_orders_2(X8)
        | ~ v7_waybel_0(X8)
        | ~ l1_waybel_0(X8,sK5)
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | v4_orders_2(sK9(sK5,X8,sK8(sK5,X7)))
        | ~ l1_waybel_0(X8,sK5)
        | ~ v7_waybel_0(X8)
        | ~ v4_orders_2(X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(resolution,[],[f4584,f146])).

fof(f4630,plain,
    ( ~ spl15_31
    | spl15_522
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(avatar_split_clause,[],[f4625,f3991,f307,f177,f170,f163,f4628,f280])).

fof(f4628,plain,
    ( spl15_522
  <=> ! [X5,X6] :
        ( ~ v7_waybel_0(X5)
        | v7_waybel_0(sK9(sK5,X6,sK8(sK5,X5)))
        | ~ v4_orders_2(X5)
        | v2_struct_0(X5)
        | ~ l1_waybel_0(X6,sK5)
        | ~ v7_waybel_0(X6)
        | ~ v4_orders_2(X6)
        | v2_struct_0(X6)
        | ~ m2_yellow_6(X5,sK5,X6)
        | ~ l1_waybel_0(X5,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_522])])).

fof(f4625,plain,
    ( ! [X6,X5] :
        ( ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ m2_yellow_6(X5,sK5,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5)
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | v7_waybel_0(sK9(sK5,X6,sK8(sK5,X5)))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(subsumption_resolution,[],[f4620,f164])).

fof(f4620,plain,
    ( ! [X6,X5] :
        ( ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ m2_yellow_6(X5,sK5,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5)
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | v7_waybel_0(sK9(sK5,X6,sK8(sK5,X5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(duplicate_literal_removal,[],[f4617])).

fof(f4617,plain,
    ( ! [X6,X5] :
        ( ~ v7_waybel_0(X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ m2_yellow_6(X5,sK5,X6)
        | v2_struct_0(X6)
        | ~ v4_orders_2(X6)
        | ~ v7_waybel_0(X6)
        | ~ l1_waybel_0(X6,sK5)
        | v2_struct_0(X5)
        | ~ v4_orders_2(X5)
        | v7_waybel_0(sK9(sK5,X6,sK8(sK5,X5)))
        | ~ l1_waybel_0(X6,sK5)
        | ~ v7_waybel_0(X6)
        | ~ v4_orders_2(X6)
        | v2_struct_0(X6)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_36
    | ~ spl15_462 ),
    inference(resolution,[],[f4584,f147])).

fof(f4498,plain,
    ( ~ spl15_521
    | ~ spl15_516 ),
    inference(avatar_split_clause,[],[f4489,f4375,f4496])).

fof(f4496,plain,
    ( spl15_521
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_521])])).

fof(f4375,plain,
    ( spl15_516
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_516])])).

fof(f4489,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))))
    | ~ spl15_516 ),
    inference(resolution,[],[f4376,f141])).

fof(f4376,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))),u1_struct_0(sK5))
    | ~ spl15_516 ),
    inference(avatar_component_clause,[],[f4375])).

fof(f4470,plain,
    ( spl15_148
    | spl15_83
    | ~ spl15_164 ),
    inference(avatar_split_clause,[],[f4464,f1080,f555,f1013])).

fof(f1013,plain,
    ( spl15_148
  <=> r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_148])])).

fof(f555,plain,
    ( spl15_83
  <=> ~ v1_xboole_0(sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_83])])).

fof(f4464,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | ~ spl15_83
    | ~ spl15_164 ),
    inference(subsumption_resolution,[],[f1085,f556])).

fof(f556,plain,
    ( ~ v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl15_83 ),
    inference(avatar_component_clause,[],[f555])).

fof(f1085,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl15_164 ),
    inference(resolution,[],[f1081,f140])).

fof(f140,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f22,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_m1_subset_1)).

fof(f4469,plain,
    ( ~ spl15_147
    | ~ spl15_490 ),
    inference(avatar_split_clause,[],[f4201,f4180,f1004])).

fof(f4180,plain,
    ( spl15_490
  <=> r2_hidden(sK10(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_490])])).

fof(f4201,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_490 ),
    inference(resolution,[],[f4181,f151])).

fof(f4181,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | ~ spl15_490 ),
    inference(avatar_component_clause,[],[f4180])).

fof(f4468,plain,
    ( ~ spl15_146
    | ~ spl15_490 ),
    inference(avatar_contradiction_clause,[],[f4467])).

fof(f4467,plain,
    ( $false
    | ~ spl15_146
    | ~ spl15_490 ),
    inference(subsumption_resolution,[],[f1008,f4201])).

fof(f1008,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_146 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl15_146
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_146])])).

fof(f4466,plain,
    ( spl15_83
    | spl15_149
    | ~ spl15_164 ),
    inference(avatar_contradiction_clause,[],[f4465])).

fof(f4465,plain,
    ( $false
    | ~ spl15_83
    | ~ spl15_149
    | ~ spl15_164 ),
    inference(subsumption_resolution,[],[f1011,f4464])).

fof(f1011,plain,
    ( ~ r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | ~ spl15_149 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f1010,plain,
    ( spl15_149
  <=> ~ r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_149])])).

fof(f4383,plain,
    ( spl15_516
    | spl15_518
    | spl15_488
    | ~ spl15_140
    | spl15_147
    | ~ spl15_486 ),
    inference(avatar_split_clause,[],[f4167,f4163,f1004,f964,f4174,f4381,f4375])).

fof(f4381,plain,
    ( spl15_518
  <=> v1_xboole_0(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_518])])).

fof(f4174,plain,
    ( spl15_488
  <=> v1_xboole_0(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_488])])).

fof(f4163,plain,
    ( spl15_486
  <=> m1_subset_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_486])])).

fof(f4167,plain,
    ( v1_xboole_0(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))
    | v1_xboole_0(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))))
    | r2_hidden(sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))),u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_486 ),
    inference(resolution,[],[f4164,f1206])).

fof(f1206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(X0)
        | v1_xboole_0(sK10(k1_zfmisc_1(X0)))
        | r2_hidden(sK10(sK10(k1_zfmisc_1(X0))),u1_struct_0(sK5)) )
    | ~ spl15_140
    | ~ spl15_147 ),
    inference(subsumption_resolution,[],[f1201,f1005])).

fof(f1201,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK10(k1_zfmisc_1(X0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(u1_struct_0(sK5))
        | r2_hidden(sK10(sK10(k1_zfmisc_1(X0))),u1_struct_0(sK5)) )
    | ~ spl15_140 ),
    inference(resolution,[],[f977,f143])).

fof(f977,plain,
    ( ! [X4] :
        ( m1_subset_1(sK10(sK10(k1_zfmisc_1(X4))),u1_struct_0(sK5))
        | v1_xboole_0(sK10(k1_zfmisc_1(X4)))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X4,k1_xboole_0) )
    | ~ spl15_140 ),
    inference(superposition,[],[f669,f965])).

fof(f669,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK10(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | m1_subset_1(sK10(sK10(k1_zfmisc_1(X1))),X2) ) ),
    inference(resolution,[],[f487,f153])).

fof(f487,plain,(
    ! [X0] :
      ( r2_hidden(sK10(sK10(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK10(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f476,f140])).

fof(f476,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r2_hidden(sK10(X0),X1) ) ),
    inference(resolution,[],[f473,f143])).

fof(f473,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f153,f375])).

fof(f375,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f143,f140])).

fof(f4164,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))),k1_xboole_0)
    | ~ spl15_486 ),
    inference(avatar_component_clause,[],[f4163])).

fof(f4331,plain,
    ( spl15_398
    | spl15_514
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_500 ),
    inference(avatar_split_clause,[],[f4253,f4242,f1571,f1564,f1556,f177,f170,f163,f4329,f2851])).

fof(f2851,plain,
    ( spl15_398
  <=> v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_398])])).

fof(f4329,plain,
    ( spl15_514
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_514])])).

fof(f1556,plain,
    ( spl15_240
  <=> v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_240])])).

fof(f1564,plain,
    ( spl15_242
  <=> v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_242])])).

fof(f1571,plain,
    ( spl15_244
  <=> l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_244])])).

fof(f4242,plain,
    ( spl15_500
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_500])])).

fof(f4253,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_500 ),
    inference(subsumption_resolution,[],[f4252,f1565])).

fof(f1565,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_242 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f4252,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_500 ),
    inference(subsumption_resolution,[],[f4251,f1557])).

fof(f1557,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_240 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f4251,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_244
    | ~ spl15_500 ),
    inference(subsumption_resolution,[],[f4249,f1572])).

fof(f1572,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ spl15_244 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f4249,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_500 ),
    inference(duplicate_literal_removal,[],[f4246])).

fof(f4246,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_500 ),
    inference(resolution,[],[f4243,f1576])).

fof(f1576,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,k10_yellow_6(sK5,sK9(sK5,X0,X1))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1575,f164])).

fof(f1575,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(X1,k10_yellow_6(sK5,sK9(sK5,X0,X1)))
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1574,f178])).

fof(f1574,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK5,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | r2_hidden(X1,k10_yellow_6(sK5,sK9(sK5,X0,X1)))
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f138,f171])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r2_hidden(X2,k10_yellow_6(X0,sK9(X0,X1,X2)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f4243,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) )
    | ~ spl15_500 ),
    inference(avatar_component_clause,[],[f4242])).

fof(f4322,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_512
    | spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(avatar_split_clause,[],[f4301,f4290,f900,f163,f4320,f915,f909,f897,f280])).

fof(f4320,plain,
    ( spl15_512
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | l1_waybel_0(sK9(sK5,sK3(sK5),X2),sK5)
        | ~ r2_hidden(X2,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_512])])).

fof(f4290,plain,
    ( spl15_506
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | m2_yellow_6(sK9(sK5,sK3(sK5),X3),sK5,sK3(sK5))
        | ~ r2_hidden(X3,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_506])])).

fof(f4301,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK3(sK5),X2),sK5)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4300,f164])).

fof(f4300,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK3(sK5),X2),sK5)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4295,f901])).

fof(f4295,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK3(sK5),X2),sK5)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_506 ),
    inference(resolution,[],[f4291,f148])).

fof(f4291,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK9(sK5,sK3(sK5),X3),sK5,sK3(sK5))
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl15_506 ),
    inference(avatar_component_clause,[],[f4290])).

fof(f4318,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_510
    | spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(avatar_split_clause,[],[f4305,f4290,f900,f163,f4316,f915,f909,f897,f280])).

fof(f4316,plain,
    ( spl15_510
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK5))
        | v4_orders_2(sK9(sK5,sK3(sK5),X4))
        | ~ r2_hidden(X4,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_510])])).

fof(f4305,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK5))
        | ~ r2_hidden(X4,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK3(sK5),X4))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4304,f164])).

fof(f4304,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK5))
        | ~ r2_hidden(X4,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK3(sK5),X4))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4297,f901])).

fof(f4297,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK5))
        | ~ r2_hidden(X4,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK3(sK5),X4))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_506 ),
    inference(resolution,[],[f4291,f146])).

fof(f4313,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_508
    | spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(avatar_split_clause,[],[f4303,f4290,f900,f163,f4311,f915,f909,f897,f280])).

fof(f4311,plain,
    ( spl15_508
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | v7_waybel_0(sK9(sK5,sK3(sK5),X3))
        | ~ r2_hidden(X3,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_508])])).

fof(f4303,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK3(sK5),X3))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4302,f164])).

fof(f4302,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK3(sK5),X3))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_126
    | ~ spl15_506 ),
    inference(subsumption_resolution,[],[f4296,f901])).

fof(f4296,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK3(sK5),X3))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_506 ),
    inference(resolution,[],[f4291,f147])).

fof(f4292,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_506
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_502 ),
    inference(avatar_split_clause,[],[f4271,f4261,f900,f177,f170,f163,f4290,f915,f909,f897])).

fof(f4261,plain,
    ( spl15_502
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK5))
        | r3_waybel_9(sK5,sK3(sK5),X0)
        | ~ r2_hidden(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_502])])).

fof(f4271,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | m2_yellow_6(sK9(sK5,sK3(sK5),X3),sK5,sK3(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_502 ),
    inference(subsumption_resolution,[],[f4267,f901])).

fof(f4267,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | m2_yellow_6(sK9(sK5,sK3(sK5),X3),sK5,sK3(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_502 ),
    inference(duplicate_literal_removal,[],[f4266])).

fof(f4266,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | m2_yellow_6(sK9(sK5,sK3(sK5),X3),sK5,sK3(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_502 ),
    inference(resolution,[],[f4262,f1444])).

fof(f4262,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK3(sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl15_502 ),
    inference(avatar_component_clause,[],[f4261])).

fof(f4275,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_504
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_502 ),
    inference(avatar_split_clause,[],[f4270,f4261,f900,f177,f170,f163,f4273,f915,f909,f897])).

fof(f4273,plain,
    ( spl15_504
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK3(sK5),X2)))
        | ~ r2_hidden(X2,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_504])])).

fof(f4270,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK3(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_126
    | ~ spl15_502 ),
    inference(subsumption_resolution,[],[f4268,f901])).

fof(f4268,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK3(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_502 ),
    inference(duplicate_literal_removal,[],[f4265])).

fof(f4265,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK3(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_502 ),
    inference(resolution,[],[f4262,f1576])).

fof(f4263,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_502
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_464 ),
    inference(avatar_split_clause,[],[f4259,f4002,f900,f874,f177,f170,f163,f4261,f915,f909,f897])).

fof(f874,plain,
    ( spl15_120
  <=> m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_120])])).

fof(f4002,plain,
    ( spl15_464
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_464])])).

fof(f4259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | r3_waybel_9(sK5,sK3(sK5),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4257,f901])).

fof(f4257,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ l1_waybel_0(sK3(sK5),sK5)
        | ~ v7_waybel_0(sK3(sK5))
        | ~ v4_orders_2(sK3(sK5))
        | v2_struct_0(sK3(sK5))
        | r3_waybel_9(sK5,sK3(sK5),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_464 ),
    inference(resolution,[],[f4017,f875])).

fof(f875,plain,
    ( m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,sK3(sK5))
    | ~ spl15_120 ),
    inference(avatar_component_clause,[],[f874])).

fof(f4017,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_464 ),
    inference(duplicate_literal_removal,[],[f4012])).

fof(f4012,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_464 ),
    inference(resolution,[],[f4003,f1708])).

fof(f4003,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0)
        | ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) )
    | ~ spl15_464 ),
    inference(avatar_component_clause,[],[f4002])).

fof(f4244,plain,
    ( spl15_398
    | spl15_500
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f3580,f2792,f1571,f1564,f1556,f177,f170,f163,f4242,f2851])).

fof(f2792,plain,
    ( spl15_396
  <=> k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_396])])).

fof(f3580,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f3579,f1565])).

fof(f3579,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f3578,f1557])).

fof(f3578,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2802,f1572])).

fof(f2802,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | r3_waybel_9(sK5,sK11(sK5,sK11(sK5,sK7(sK5))),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(superposition,[],[f1322,f2793])).

fof(f2793,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))) = k1_xboole_0
    | ~ spl15_396 ),
    inference(avatar_component_clause,[],[f2792])).

fof(f4236,plain,
    ( ~ spl15_123
    | ~ spl15_119
    | spl15_498
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_190
    | spl15_233
    | ~ spl15_324 ),
    inference(avatar_split_clause,[],[f3605,f2266,f1496,f1225,f177,f170,f163,f4234,f856,f887])).

fof(f887,plain,
    ( spl15_123
  <=> ~ v4_orders_2(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_123])])).

fof(f856,plain,
    ( spl15_119
  <=> ~ v7_waybel_0(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_119])])).

fof(f4234,plain,
    ( spl15_498
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r3_waybel_9(sK5,sK11(sK5,sK7(sK5)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_498])])).

fof(f1225,plain,
    ( spl15_190
  <=> l1_waybel_0(sK11(sK5,sK7(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_190])])).

fof(f1496,plain,
    ( spl15_233
  <=> ~ v2_struct_0(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_233])])).

fof(f2266,plain,
    ( spl15_324
  <=> k10_yellow_6(sK5,sK11(sK5,sK7(sK5))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_324])])).

fof(f3605,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK7(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f3581,f1497])).

fof(f1497,plain,
    ( ~ v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_233 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f3581,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
        | v2_struct_0(sK11(sK5,sK7(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK7(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_190
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2276,f1226])).

fof(f1226,plain,
    ( l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ spl15_190 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f2276,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
        | v2_struct_0(sK11(sK5,sK7(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK7(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_324 ),
    inference(superposition,[],[f1322,f2267])).

fof(f2267,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK7(sK5))) = k1_xboole_0
    | ~ spl15_324 ),
    inference(avatar_component_clause,[],[f2266])).

fof(f4232,plain,
    ( spl15_36
    | spl15_410
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f3603,f177,f170,f163,f3010,f307])).

fof(f3010,plain,
    ( spl15_410
  <=> ! [X7] :
        ( v2_struct_0(X7)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5))
        | ~ v4_orders_2(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(X7)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ l1_waybel_0(X7,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_410])])).

fof(f3603,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3602,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK7(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f3602,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3601,f129])).

fof(f129,plain,(
    ! [X0] :
      ( v4_orders_2(sK7(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f3601,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3600,f130])).

fof(f130,plain,(
    ! [X0] :
      ( v7_waybel_0(sK7(X0))
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f3600,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2381,f131])).

fof(f131,plain,(
    ! [X0] :
      ( l1_waybel_0(sK7(X0),X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f2381,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f2376,f132])).

fof(f2376,plain,
    ( ! [X0,X1] :
        ( r3_waybel_9(sK5,X1,sK10(k10_yellow_6(sK5,X0)))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2375,f869])).

fof(f2375,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK10(k10_yellow_6(sK5,X0)))
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2371])).

fof(f2371,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK10(k10_yellow_6(sK5,X0)))
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1734,f473])).

fof(f1734,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK10(k10_yellow_6(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK10(k10_yellow_6(sK5,X0))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1733,f1708])).

fof(f1733,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,X0,sK10(k10_yellow_6(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1732,f869])).

fof(f1732,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK5,X0,sK10(k10_yellow_6(sK5,X0)))
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1730])).

fof(f1730,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK5,X0,sK10(k10_yellow_6(sK5,X0)))
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1341,f473])).

fof(f1341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK10(k10_yellow_6(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r3_waybel_9(sK5,X0,sK10(k10_yellow_6(sK5,X0)))
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1322,f375])).

fof(f4230,plain,
    ( spl15_36
    | spl15_496
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f3599,f177,f170,f163,f4228,f307])).

fof(f4228,plain,
    ( spl15_496
  <=> ! [X7] :
        ( ~ v4_orders_2(X7)
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ l1_waybel_0(X7,sK5)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_496])])).

fof(f3599,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3598,f883])).

fof(f883,plain,
    ( ! [X0] :
        ( m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0)))),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0))))
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f869,f669])).

fof(f3598,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7)))),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3597,f128])).

fof(f3597,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7)))),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3596,f129])).

fof(f3596,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7)))),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3595,f130])).

fof(f3595,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7)))),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f3515,f131])).

fof(f3515,plain,
    ( ! [X7] :
        ( ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7))))
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v7_waybel_0(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X7)))),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1902,f132])).

fof(f1902,plain,
    ( ! [X0,X1] :
        ( r3_waybel_9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0)))))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0))))
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1895,f883])).

fof(f1895,plain,
    ( ! [X0,X1] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0))))
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0)))),u1_struct_0(sK5))
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X0))))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1343,f1708])).

fof(f1343,plain,
    ( ! [X1] :
        ( r3_waybel_9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1)))))
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1)))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1342,f883])).

fof(f1342,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1)))),u1_struct_0(sK5))
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1)))))
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1)))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1322,f487])).

fof(f4209,plain,
    ( ~ spl15_495
    | ~ spl15_490 ),
    inference(avatar_split_clause,[],[f4200,f4180,f4207])).

fof(f4207,plain,
    ( spl15_495
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_495])])).

fof(f4200,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))))
    | ~ spl15_490 ),
    inference(resolution,[],[f4181,f141])).

fof(f4196,plain,
    ( spl15_492
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_488 ),
    inference(avatar_split_clause,[],[f4187,f4174,f401,f391,f4194])).

fof(f4194,plain,
    ( spl15_492
  <=> k1_xboole_0 = o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_492])])).

fof(f4187,plain,
    ( k1_xboole_0 = o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_488 ),
    inference(forward_demodulation,[],[f4183,f402])).

fof(f4183,plain,
    ( o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_488 ),
    inference(resolution,[],[f4175,f395])).

fof(f4175,plain,
    ( v1_xboole_0(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))
    | ~ spl15_488 ),
    inference(avatar_component_clause,[],[f4174])).

fof(f4182,plain,
    ( spl15_488
    | spl15_490
    | ~ spl15_164
    | ~ spl15_486 ),
    inference(avatar_split_clause,[],[f4168,f4163,f1080,f4180,f4174])).

fof(f4168,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5)))),u1_struct_0(sK5))
    | v1_xboole_0(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))))
    | ~ spl15_164
    | ~ spl15_486 ),
    inference(resolution,[],[f4164,f1081])).

fof(f4165,plain,
    ( spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_486
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_456 ),
    inference(avatar_split_clause,[],[f4158,f3703,f900,f874,f177,f170,f163,f4163,f915,f909,f897])).

fof(f3703,plain,
    ( spl15_456
  <=> k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_456])])).

fof(f4158,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))),k1_xboole_0)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f4156,f901])).

fof(f4156,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK3(sK5),sK11(sK5,sK3(sK5))),k1_xboole_0)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_120
    | ~ spl15_456 ),
    inference(resolution,[],[f3960,f875])).

fof(f3960,plain,
    ( ! [X7] :
        ( ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X7)
        | m1_subset_1(o_3_4_yellow19(sK5,X7,sK11(sK5,sK3(sK5))),k1_xboole_0)
        | ~ l1_waybel_0(X7,sK5)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3959,f164])).

fof(f3959,plain,
    ( ! [X7] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X7,sK11(sK5,sK3(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3958,f171])).

fof(f3958,plain,
    ( ! [X7] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X7,sK11(sK5,sK3(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_4
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3754,f178])).

fof(f3754,plain,
    ( ! [X7] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X7,sK11(sK5,sK3(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,X7)
        | ~ l1_waybel_0(X7,sK5)
        | ~ v7_waybel_0(X7)
        | ~ v4_orders_2(X7)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_456 ),
    inference(superposition,[],[f152,f3704])).

fof(f3704,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0
    | ~ spl15_456 ),
    inference(avatar_component_clause,[],[f3703])).

fof(f4155,plain,
    ( spl15_484
    | ~ spl15_4
    | ~ spl15_482 ),
    inference(avatar_split_clause,[],[f4147,f4144,f177,f4153])).

fof(f4153,plain,
    ( spl15_484
  <=> l1_orders_2(sK11(sK5,sK11(sK5,sK3(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_484])])).

fof(f4147,plain,
    ( l1_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ spl15_4
    | ~ spl15_482 ),
    inference(resolution,[],[f4145,f271])).

fof(f4146,plain,
    ( ~ spl15_31
    | spl15_482
    | spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476 ),
    inference(avatar_split_clause,[],[f4114,f4099,f3694,f1241,f940,f921,f163,f4144,f280])).

fof(f4114,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4113,f164])).

fof(f4113,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4112,f3695])).

fof(f4112,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4111,f941])).

fof(f4111,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4110,f922])).

fof(f4110,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4103,f1242])).

fof(f4103,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_476 ),
    inference(resolution,[],[f4100,f148])).

fof(f4139,plain,
    ( ~ spl15_31
    | spl15_480
    | spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476 ),
    inference(avatar_split_clause,[],[f4124,f4099,f3694,f1241,f940,f921,f163,f4137,f280])).

fof(f4124,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4123,f164])).

fof(f4123,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4122,f3695])).

fof(f4122,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4121,f941])).

fof(f4121,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4120,f922])).

fof(f4120,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4105,f1242])).

fof(f4105,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_476 ),
    inference(resolution,[],[f4100,f146])).

fof(f4131,plain,
    ( ~ spl15_31
    | spl15_478
    | spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_476 ),
    inference(avatar_split_clause,[],[f4119,f4099,f3694,f1241,f940,f921,f163,f4129,f280])).

fof(f4119,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4118,f164])).

fof(f4118,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4117,f3695])).

fof(f4117,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4116,f941])).

fof(f4116,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4115,f922])).

fof(f4115,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_194
    | ~ spl15_476 ),
    inference(subsumption_resolution,[],[f4104,f1242])).

fof(f4104,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK3(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_476 ),
    inference(resolution,[],[f4100,f147])).

fof(f4101,plain,
    ( spl15_476
    | ~ spl15_31
    | spl15_1
    | ~ spl15_194
    | ~ spl15_474 ),
    inference(avatar_split_clause,[],[f4094,f4088,f1241,f163,f280,f4099])).

fof(f4088,plain,
    ( spl15_474
  <=> ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK3(sK5))),X0,sK11(sK5,sK3(sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_474])])).

fof(f4094,plain,
    ( ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,sK11(sK5,sK3(sK5)))
    | ~ spl15_1
    | ~ spl15_194
    | ~ spl15_474 ),
    inference(subsumption_resolution,[],[f4092,f164])).

fof(f4092,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK3(sK5))),sK5,sK11(sK5,sK3(sK5)))
    | ~ spl15_194
    | ~ spl15_474 ),
    inference(resolution,[],[f4089,f1242])).

fof(f4089,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK3(sK5))),X0,sK11(sK5,sK3(sK5))) )
    | ~ spl15_474 ),
    inference(avatar_component_clause,[],[f4088])).

fof(f4090,plain,
    ( spl15_454
    | spl15_474
    | ~ spl15_132
    | ~ spl15_134 ),
    inference(avatar_split_clause,[],[f3625,f940,f921,f4088,f3697])).

fof(f3697,plain,
    ( spl15_454
  <=> v2_struct_0(sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_454])])).

fof(f3625,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK3(sK5))),X0,sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_132
    | ~ spl15_134 ),
    inference(subsumption_resolution,[],[f3624,f941])).

fof(f3624,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK3(sK5))),X0,sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_132 ),
    inference(resolution,[],[f922,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m2_yellow_6(sK11(X0,X1),X0,X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m2_yellow_6(sK11(X0,X1),X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f62,f97])).

fof(f97,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
     => m2_yellow_6(sK11(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_yellow_6(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_m2_yellow_6)).

fof(f4086,plain,
    ( spl15_110
    | ~ spl15_113
    | ~ spl15_115
    | ~ spl15_117
    | spl15_290
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f1811,f1799,f177,f170,f163,f1856,f853,f847,f841,f835])).

fof(f841,plain,
    ( spl15_113
  <=> ~ v4_orders_2(sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_113])])).

fof(f1799,plain,
    ( spl15_282
  <=> k10_yellow_6(sK5,sK7(sK5)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_282])])).

fof(f1811,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | r3_waybel_9(sK5,sK7(sK5),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_282 ),
    inference(superposition,[],[f1322,f1800])).

fof(f1800,plain,
    ( k10_yellow_6(sK5,sK7(sK5)) = k1_xboole_0
    | ~ spl15_282 ),
    inference(avatar_component_clause,[],[f1799])).

fof(f4085,plain,
    ( ~ spl15_19
    | spl15_472
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f1880,f177,f170,f163,f4083,f222])).

fof(f222,plain,
    ( spl15_19
  <=> ~ sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_19])])).

fof(f4083,plain,
    ( spl15_472
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),k10_yellow_6(sK5,sK4(sK5,X0)))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_472])])).

fof(f1880,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1877])).

fof(f1877,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1843,f105])).

fof(f4072,plain,
    ( ~ spl15_31
    | spl15_470
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_464 ),
    inference(avatar_split_clause,[],[f4049,f4002,f3694,f1241,f940,f921,f177,f170,f163,f4070,f280])).

fof(f4070,plain,
    ( spl15_470
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ r2_hidden(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_470])])).

fof(f4049,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4048,f164])).

fof(f4048,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4047,f3695])).

fof(f4047,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4046,f941])).

fof(f4046,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4045,f922])).

fof(f4045,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4037,f1242])).

fof(f4037,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK5))
        | ~ r2_hidden(X1,k1_xboole_0)
        | l1_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X1),sK5)
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(resolution,[],[f4025,f148])).

fof(f4025,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5)))
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4024,f3695])).

fof(f4024,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4023,f941])).

fof(f4023,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4022,f922])).

fof(f4022,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_194
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4015,f1242])).

fof(f4015,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_464 ),
    inference(duplicate_literal_removal,[],[f4014])).

fof(f4014,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | m2_yellow_6(sK9(sK5,sK11(sK5,sK3(sK5)),X3),sK5,sK11(sK5,sK3(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_464 ),
    inference(resolution,[],[f4003,f1444])).

fof(f4068,plain,
    ( ~ spl15_31
    | spl15_468
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_464 ),
    inference(avatar_split_clause,[],[f4059,f4002,f3694,f1241,f940,f921,f177,f170,f163,f4066,f280])).

fof(f4066,plain,
    ( spl15_468
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ r2_hidden(X3,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_468])])).

fof(f4059,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4058,f164])).

fof(f4058,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4057,f3695])).

fof(f4057,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4056,f941])).

fof(f4056,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4055,f922])).

fof(f4055,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4039,f1242])).

fof(f4039,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_hidden(X3,k1_xboole_0)
        | v4_orders_2(sK9(sK5,sK11(sK5,sK3(sK5)),X3))
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(resolution,[],[f4025,f146])).

fof(f4063,plain,
    ( ~ spl15_31
    | spl15_466
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | spl15_455
    | ~ spl15_464 ),
    inference(avatar_split_clause,[],[f4054,f4002,f3694,f1241,f940,f921,f177,f170,f163,f4061,f280])).

fof(f4061,plain,
    ( spl15_466
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ r2_hidden(X2,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_466])])).

fof(f4054,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4053,f164])).

fof(f4053,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4052,f3695])).

fof(f4052,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4051,f941])).

fof(f4051,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4050,f922])).

fof(f4050,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(subsumption_resolution,[],[f4038,f1242])).

fof(f4038,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ r2_hidden(X2,k1_xboole_0)
        | v7_waybel_0(sK9(sK5,sK11(sK5,sK3(sK5)),X2))
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_455
    | ~ spl15_464 ),
    inference(resolution,[],[f4025,f147])).

fof(f4011,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_129
    | ~ spl15_131
    | spl15_1
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_454 ),
    inference(avatar_split_clause,[],[f4010,f3697,f900,f874,f163,f915,f909,f897,f280])).

fof(f4010,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_454 ),
    inference(subsumption_resolution,[],[f4009,f164])).

fof(f4009,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_120
    | ~ spl15_126
    | ~ spl15_454 ),
    inference(subsumption_resolution,[],[f4007,f901])).

fof(f4007,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_120
    | ~ spl15_454 ),
    inference(resolution,[],[f4005,f875])).

fof(f4005,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK11(sK5,sK3(sK5)),X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_454 ),
    inference(resolution,[],[f3698,f145])).

fof(f3698,plain,
    ( v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_454 ),
    inference(avatar_component_clause,[],[f3697])).

fof(f4004,plain,
    ( spl15_454
    | spl15_464
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(avatar_split_clause,[],[f3784,f3703,f1241,f940,f921,f177,f170,f163,f4002,f3697])).

fof(f3784,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3783,f941])).

fof(f3783,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3782,f922])).

fof(f3782,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3712,f1242])).

fof(f3712,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
        | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
        | v2_struct_0(sK11(sK5,sK3(sK5)))
        | r3_waybel_9(sK5,sK11(sK5,sK3(sK5)),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_456 ),
    inference(superposition,[],[f1322,f3704])).

fof(f3993,plain,
    ( ~ spl15_37
    | spl15_462
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f3592,f177,f170,f163,f3991,f310])).

fof(f310,plain,
    ( spl15_37
  <=> ~ sP1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_37])])).

fof(f3592,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK8(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1715,f126])).

fof(f1715,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK8(sK5,X0),u1_struct_0(sK5))
        | ~ m2_yellow_6(X0,sK5,X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | r3_waybel_9(sK5,X1,sK8(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1708,f127])).

fof(f127,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK8(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f3978,plain,
    ( ~ spl15_37
    | spl15_460
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f3593,f177,f170,f163,f3976,f310])).

fof(f3593,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(sK8(sK5,X0),k10_yellow_6(sK5,sK9(sK5,X0,sK8(sK5,X0))))
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1587,f126])).

fof(f1587,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK5,X0),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(sK8(sK5,X0),k10_yellow_6(sK5,sK9(sK5,X0,sK8(sK5,X0))))
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1586])).

fof(f1586,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK5,X0),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(sK8(sK5,X0),k10_yellow_6(sK5,sK9(sK5,X0,sK8(sK5,X0))))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1576,f127])).

fof(f3973,plain,
    ( spl15_454
    | ~ spl15_459
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(avatar_split_clause,[],[f3966,f3703,f1241,f940,f921,f177,f170,f163,f3971,f3697])).

fof(f3971,plain,
    ( spl15_459
  <=> ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_459])])).

fof(f3966,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3965,f164])).

fof(f3965,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3964,f171])).

fof(f3964,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_4
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3963,f178])).

fof(f3963,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3962,f941])).

fof(f3962,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_132
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3961,f922])).

fof(f3961,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_194
    | ~ spl15_456 ),
    inference(subsumption_resolution,[],[f3756,f1242])).

fof(f3756,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_456 ),
    inference(trivial_inequality_removal,[],[f3755])).

fof(f3755,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK11(sK5,sK3(sK5)),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_456 ),
    inference(superposition,[],[f134,f3704])).

fof(f3705,plain,
    ( spl15_454
    | spl15_456
    | ~ spl15_120
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_452 ),
    inference(avatar_split_clause,[],[f3689,f3678,f1241,f940,f921,f874,f3703,f3697])).

fof(f3689,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_120
    | ~ spl15_132
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_452 ),
    inference(subsumption_resolution,[],[f3688,f922])).

fof(f3688,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_120
    | ~ spl15_134
    | ~ spl15_194
    | ~ spl15_452 ),
    inference(subsumption_resolution,[],[f3687,f941])).

fof(f3687,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_120
    | ~ spl15_194
    | ~ spl15_452 ),
    inference(subsumption_resolution,[],[f3681,f1242])).

fof(f3681,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | k10_yellow_6(sK5,sK11(sK5,sK3(sK5))) = k1_xboole_0
    | v2_struct_0(sK11(sK5,sK3(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK3(sK5)))
    | ~ v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ spl15_120
    | ~ spl15_452 ),
    inference(resolution,[],[f3679,f875])).

fof(f3680,plain,
    ( spl15_18
    | spl15_452
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f1220,f177,f170,f163,f3678,f225])).

fof(f1220,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | k10_yellow_6(sK5,X0) = k1_xboole_0
        | sP0(sK5)
        | ~ m2_yellow_6(X0,sK5,sK3(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1116,f111])).

fof(f111,plain,(
    ! [X2,X0] :
      ( ~ v3_yellow_6(X2,X0)
      | sP0(X0)
      | ~ m2_yellow_6(X2,X0,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f1116,plain,
    ( ! [X0] :
        ( v3_yellow_6(X0,sK5)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | k10_yellow_6(sK5,X0) = k1_xboole_0 )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1115,f164])).

fof(f1115,plain,
    ( ! [X0] :
        ( k10_yellow_6(sK5,X0) = k1_xboole_0
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v3_yellow_6(X0,sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1114,f178])).

fof(f1114,plain,
    ( ! [X0] :
        ( k10_yellow_6(sK5,X0) = k1_xboole_0
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK5)
        | v3_yellow_6(X0,sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_2 ),
    inference(resolution,[],[f135,f171])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k10_yellow_6(X0,X1) = k1_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v3_yellow_6(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f3671,plain,
    ( ~ spl15_31
    | spl15_450
    | spl15_1
    | ~ spl15_444 ),
    inference(avatar_split_clause,[],[f3656,f3638,f163,f3669,f280])).

fof(f3656,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK8(sK5,X1)),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_444 ),
    inference(subsumption_resolution,[],[f3654,f164])).

fof(f3654,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK8(sK5,X1)),sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(duplicate_literal_removal,[],[f3649])).

fof(f3649,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK8(sK5,X1)),sK5)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(resolution,[],[f3639,f148])).

fof(f3667,plain,
    ( ~ spl15_31
    | spl15_448
    | spl15_1
    | ~ spl15_444 ),
    inference(avatar_split_clause,[],[f3658,f3638,f163,f3665,f280])).

fof(f3658,plain,
    ( ! [X3] :
        ( ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK8(sK5,X3)))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_444 ),
    inference(subsumption_resolution,[],[f3652,f164])).

fof(f3652,plain,
    ( ! [X3] :
        ( ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK8(sK5,X3)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(duplicate_literal_removal,[],[f3651])).

fof(f3651,plain,
    ( ! [X3] :
        ( ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK8(sK5,X3)))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(resolution,[],[f3639,f146])).

fof(f3662,plain,
    ( ~ spl15_31
    | spl15_446
    | spl15_1
    | ~ spl15_444 ),
    inference(avatar_split_clause,[],[f3657,f3638,f163,f3660,f280])).

fof(f3657,plain,
    ( ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK8(sK5,X2)))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_444 ),
    inference(subsumption_resolution,[],[f3653,f164])).

fof(f3653,plain,
    ( ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK8(sK5,X2)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(duplicate_literal_removal,[],[f3650])).

fof(f3650,plain,
    ( ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK8(sK5,X2)))
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_444 ),
    inference(resolution,[],[f3639,f147])).

fof(f3641,plain,
    ( spl15_108
    | spl15_36
    | spl15_1
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f788,f177,f163,f307,f794])).

fof(f794,plain,
    ( spl15_108
  <=> m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_108])])).

fof(f788,plain,
    ( sP1(sK5)
    | m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,sK7(sK5))
    | ~ spl15_1
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f786,f164])).

fof(f786,plain,
    ( v2_struct_0(sK5)
    | sP1(sK5)
    | m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,sK7(sK5))
    | ~ spl15_4 ),
    inference(resolution,[],[f784,f178])).

fof(f784,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | sP1(X0)
      | m2_yellow_6(sK11(X0,sK7(X0)),X0,sK7(X0)) ) ),
    inference(resolution,[],[f782,f121])).

fof(f782,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m2_yellow_6(sK11(X0,sK7(X0)),X0,sK7(X0))
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(duplicate_literal_removal,[],[f781])).

fof(f781,plain,(
    ! [X0] :
      ( m2_yellow_6(sK11(X0,sK7(X0)),X0,sK7(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | sP1(X0)
      | sP1(X0) ) ),
    inference(resolution,[],[f743,f131])).

fof(f743,plain,(
    ! [X2,X3] :
      ( ~ l1_waybel_0(sK7(X2),X3)
      | m2_yellow_6(sK11(X3,sK7(X2)),X3,sK7(X2))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | sP1(X2) ) ),
    inference(subsumption_resolution,[],[f742,f128])).

fof(f742,plain,(
    ! [X2,X3] :
      ( ~ l1_waybel_0(sK7(X2),X3)
      | m2_yellow_6(sK11(X3,sK7(X2)),X3,sK7(X2))
      | v2_struct_0(sK7(X2))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | sP1(X2) ) ),
    inference(subsumption_resolution,[],[f739,f129])).

fof(f739,plain,(
    ! [X2,X3] :
      ( ~ l1_waybel_0(sK7(X2),X3)
      | m2_yellow_6(sK11(X3,sK7(X2)),X3,sK7(X2))
      | ~ v4_orders_2(sK7(X2))
      | v2_struct_0(sK7(X2))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | sP1(X2) ) ),
    inference(resolution,[],[f149,f130])).

fof(f3640,plain,
    ( ~ spl15_37
    | spl15_444
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f3594,f177,f170,f163,f3638,f310])).

fof(f3594,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X0,sK8(sK5,X0)),sK5,X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1446,f126])).

fof(f1446,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK5,X0),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X0,sK8(sK5,X0)),sK5,X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1445])).

fof(f1445,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK8(sK5,X0),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | m2_yellow_6(sK9(sK5,X0,sK8(sK5,X0)),sK5,X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ sP1(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1444,f127])).

fof(f3636,plain,
    ( spl15_442
    | ~ spl15_4
    | ~ spl15_194 ),
    inference(avatar_split_clause,[],[f3627,f1241,f177,f3634])).

fof(f3634,plain,
    ( spl15_442
  <=> l1_orders_2(sK11(sK5,sK3(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_442])])).

fof(f3627,plain,
    ( l1_orders_2(sK11(sK5,sK3(sK5)))
    | ~ spl15_4
    | ~ spl15_194 ),
    inference(resolution,[],[f1242,f271])).

fof(f3622,plain,
    ( spl15_19
    | ~ spl15_124 ),
    inference(avatar_contradiction_clause,[],[f3621])).

fof(f3621,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_124 ),
    inference(subsumption_resolution,[],[f3619,f223])).

fof(f223,plain,
    ( ~ sP0(sK5)
    | ~ spl15_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f3619,plain,
    ( sP0(sK5)
    | ~ spl15_124 ),
    inference(resolution,[],[f898,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f898,plain,
    ( v2_struct_0(sK3(sK5))
    | ~ spl15_124 ),
    inference(avatar_component_clause,[],[f897])).

fof(f3618,plain,
    ( spl15_19
    | spl15_131 ),
    inference(avatar_contradiction_clause,[],[f3617])).

fof(f3617,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_131 ),
    inference(subsumption_resolution,[],[f3616,f223])).

fof(f3616,plain,
    ( sP0(sK5)
    | ~ spl15_131 ),
    inference(resolution,[],[f916,f110])).

fof(f110,plain,(
    ! [X0] :
      ( l1_waybel_0(sK3(X0),X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f916,plain,
    ( ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ spl15_131 ),
    inference(avatar_component_clause,[],[f915])).

fof(f3615,plain,
    ( spl15_19
    | spl15_129 ),
    inference(avatar_contradiction_clause,[],[f3614])).

fof(f3614,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_129 ),
    inference(subsumption_resolution,[],[f3613,f223])).

fof(f3613,plain,
    ( sP0(sK5)
    | ~ spl15_129 ),
    inference(resolution,[],[f910,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v7_waybel_0(sK3(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f910,plain,
    ( ~ v7_waybel_0(sK3(sK5))
    | ~ spl15_129 ),
    inference(avatar_component_clause,[],[f909])).

fof(f3609,plain,
    ( spl15_36
    | spl15_113 ),
    inference(avatar_split_clause,[],[f862,f841,f307])).

fof(f862,plain,
    ( sP1(sK5)
    | ~ spl15_113 ),
    inference(resolution,[],[f842,f129])).

fof(f842,plain,
    ( ~ v4_orders_2(sK7(sK5))
    | ~ spl15_113 ),
    inference(avatar_component_clause,[],[f841])).

fof(f3591,plain,
    ( spl15_37
    | ~ spl15_110 ),
    inference(avatar_contradiction_clause,[],[f3590])).

fof(f3590,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_110 ),
    inference(subsumption_resolution,[],[f3588,f311])).

fof(f311,plain,
    ( ~ sP1(sK5)
    | ~ spl15_37 ),
    inference(avatar_component_clause,[],[f310])).

fof(f3588,plain,
    ( sP1(sK5)
    | ~ spl15_110 ),
    inference(resolution,[],[f836,f128])).

fof(f836,plain,
    ( v2_struct_0(sK7(sK5))
    | ~ spl15_110 ),
    inference(avatar_component_clause,[],[f835])).

fof(f3577,plain,
    ( ~ spl15_115
    | spl15_110
    | ~ spl15_117
    | ~ spl15_112
    | ~ spl15_214
    | spl15_433 ),
    inference(avatar_split_clause,[],[f3576,f3548,f1350,f838,f853,f835,f847])).

fof(f1350,plain,
    ( spl15_214
  <=> ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | l1_waybel_0(sK4(sK5,X2),sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_214])])).

fof(f3548,plain,
    ( spl15_433
  <=> ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_433])])).

fof(f3576,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | v2_struct_0(sK7(sK5))
    | ~ v7_waybel_0(sK7(sK5))
    | ~ spl15_112
    | ~ spl15_214
    | ~ spl15_433 ),
    inference(subsumption_resolution,[],[f3575,f839])).

fof(f3575,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | v2_struct_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | ~ v7_waybel_0(sK7(sK5))
    | ~ spl15_214
    | ~ spl15_433 ),
    inference(resolution,[],[f3549,f1351])).

fof(f1351,plain,
    ( ! [X2] :
        ( l1_waybel_0(sK4(sK5,X2),sK5)
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2) )
    | ~ spl15_214 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f3549,plain,
    ( ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ spl15_433 ),
    inference(avatar_component_clause,[],[f3548])).

fof(f3574,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | ~ spl15_433
    | spl15_434
    | ~ spl15_437
    | spl15_438
    | ~ spl15_441
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_410 ),
    inference(avatar_split_clause,[],[f3026,f3010,f838,f225,f177,f170,f163,f3572,f3566,f3560,f3554,f3548,f853,f847,f835])).

fof(f3026,plain,
    ( ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,sK7(sK5))))
    | ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_112
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f3025,f226])).

fof(f3025,plain,
    ( ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,sK7(sK5))))
    | ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ sP0(sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f3023,f839])).

fof(f3023,plain,
    ( ~ v4_orders_2(sK4(sK5,sK7(sK5)))
    | v2_struct_0(sK4(sK5,sK7(sK5)))
    | ~ v7_waybel_0(sK4(sK5,sK7(sK5)))
    | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,sK7(sK5))))
    | ~ l1_waybel_0(sK4(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ sP0(sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_410 ),
    inference(resolution,[],[f3019,f105])).

fof(f3019,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK5,sK7(sK5))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_410 ),
    inference(subsumption_resolution,[],[f3018,f869])).

fof(f3018,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m2_yellow_6(X0,sK5,sK7(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) )
    | ~ spl15_410 ),
    inference(duplicate_literal_removal,[],[f3013])).

fof(f3013,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m2_yellow_6(X0,sK5,sK7(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_410 ),
    inference(resolution,[],[f3011,f473])).

fof(f3011,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5))
        | v2_struct_0(X7)
        | ~ v4_orders_2(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ v7_waybel_0(X7)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ l1_waybel_0(X7,sK5) )
    | ~ spl15_410 ),
    inference(avatar_component_clause,[],[f3010])).

fof(f3527,plain,
    ( ~ spl15_31
    | spl15_430
    | spl15_1
    | ~ spl15_18
    | ~ spl15_412 ),
    inference(avatar_split_clause,[],[f3508,f3382,f225,f163,f3525,f280])).

fof(f3525,plain,
    ( spl15_430
  <=> ! [X0] :
        ( r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK4(sK5,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_430])])).

fof(f3382,plain,
    ( spl15_412
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | ~ v4_orders_2(sK4(sK5,X0))
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_412])])).

fof(f3508,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_412 ),
    inference(subsumption_resolution,[],[f3507,f226])).

fof(f3507,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_412 ),
    inference(subsumption_resolution,[],[f3506,f164])).

fof(f3506,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_412 ),
    inference(duplicate_literal_removal,[],[f3505])).

fof(f3505,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_412 ),
    inference(resolution,[],[f3383,f735])).

fof(f3383,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5) )
    | ~ spl15_412 ),
    inference(avatar_component_clause,[],[f3382])).

fof(f3492,plain,
    ( spl15_428
    | ~ spl15_4
    | ~ spl15_426 ),
    inference(avatar_split_clause,[],[f3484,f3481,f177,f3490])).

fof(f3490,plain,
    ( spl15_428
  <=> l1_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_428])])).

fof(f3481,plain,
    ( spl15_426
  <=> l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_426])])).

fof(f3484,plain,
    ( l1_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_4
    | ~ spl15_426 ),
    inference(resolution,[],[f3482,f271])).

fof(f3482,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | ~ spl15_426 ),
    inference(avatar_component_clause,[],[f3481])).

fof(f3483,plain,
    ( ~ spl15_31
    | spl15_398
    | spl15_426
    | spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(avatar_split_clause,[],[f3453,f3440,f1571,f1564,f1556,f163,f3481,f2851,f280])).

fof(f3440,plain,
    ( spl15_420
  <=> m2_yellow_6(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5,sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_420])])).

fof(f3453,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3452,f164])).

fof(f3452,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3451,f1565])).

fof(f3451,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3450,f1557])).

fof(f3450,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3444,f1572])).

fof(f3444,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_420 ),
    inference(resolution,[],[f3441,f148])).

fof(f3441,plain,
    ( m2_yellow_6(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5,sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_420 ),
    inference(avatar_component_clause,[],[f3440])).

fof(f3476,plain,
    ( ~ spl15_31
    | spl15_398
    | spl15_424
    | spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(avatar_split_clause,[],[f3461,f3440,f1571,f1564,f1556,f163,f3474,f2851,f280])).

fof(f3474,plain,
    ( spl15_424
  <=> v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_424])])).

fof(f3461,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3460,f164])).

fof(f3460,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3459,f1565])).

fof(f3459,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3458,f1557])).

fof(f3458,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3446,f1572])).

fof(f3446,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_420 ),
    inference(resolution,[],[f3441,f146])).

fof(f3468,plain,
    ( ~ spl15_31
    | spl15_398
    | spl15_422
    | spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(avatar_split_clause,[],[f3457,f3440,f1571,f1564,f1556,f163,f3466,f2851,f280])).

fof(f3466,plain,
    ( spl15_422
  <=> v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_422])])).

fof(f3457,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3456,f164])).

fof(f3456,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3455,f1565])).

fof(f3455,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3454,f1557])).

fof(f3454,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_244
    | ~ spl15_420 ),
    inference(subsumption_resolution,[],[f3445,f1572])).

fof(f3445,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_420 ),
    inference(resolution,[],[f3441,f147])).

fof(f3442,plain,
    ( spl15_420
    | ~ spl15_31
    | spl15_1
    | ~ spl15_244
    | ~ spl15_418 ),
    inference(avatar_split_clause,[],[f3435,f3429,f1571,f163,f280,f3440])).

fof(f3429,plain,
    ( spl15_418
  <=> ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK11(sK5,sK7(sK5)))),X0,sK11(sK5,sK11(sK5,sK7(sK5)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_418])])).

fof(f3435,plain,
    ( ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5,sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_1
    | ~ spl15_244
    | ~ spl15_418 ),
    inference(subsumption_resolution,[],[f3433,f164])).

fof(f3433,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))),sK5,sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_244
    | ~ spl15_418 ),
    inference(resolution,[],[f3430,f1572])).

fof(f3430,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK11(sK5,sK7(sK5)))),X0,sK11(sK5,sK11(sK5,sK7(sK5)))) )
    | ~ spl15_418 ),
    inference(avatar_component_clause,[],[f3429])).

fof(f3431,plain,
    ( spl15_398
    | ~ spl15_243
    | spl15_418
    | ~ spl15_240 ),
    inference(avatar_split_clause,[],[f1559,f1556,f3429,f1561,f2851])).

fof(f1561,plain,
    ( spl15_243
  <=> ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_243])])).

fof(f1559,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK11(sK5,sK7(sK5)))),X0,sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
        | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_240 ),
    inference(resolution,[],[f1557,f149])).

fof(f3409,plain,
    ( ~ spl15_31
    | spl15_416
    | spl15_1
    | ~ spl15_18
    | ~ spl15_414 ),
    inference(avatar_split_clause,[],[f3405,f3399,f225,f163,f3407,f280])).

fof(f3407,plain,
    ( spl15_416
  <=> ! [X0] :
        ( v2_struct_0(sK4(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_416])])).

fof(f3399,plain,
    ( spl15_414
  <=> ! [X0] :
        ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | v2_struct_0(sK4(sK5,X0))
        | ~ v4_orders_2(sK4(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_414])])).

fof(f3405,plain,
    ( ! [X0] :
        ( v2_struct_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f3404,f226])).

fof(f3404,plain,
    ( ! [X0] :
        ( v2_struct_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_414 ),
    inference(subsumption_resolution,[],[f3403,f164])).

fof(f3403,plain,
    ( ! [X0] :
        ( v2_struct_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_414 ),
    inference(duplicate_literal_removal,[],[f3402])).

fof(f3402,plain,
    ( ! [X0] :
        ( v2_struct_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_414 ),
    inference(resolution,[],[f3400,f735])).

fof(f3400,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_414 ),
    inference(avatar_component_clause,[],[f3399])).

fof(f3401,plain,
    ( ~ spl15_31
    | spl15_414
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | spl15_147
    | ~ spl15_214 ),
    inference(avatar_split_clause,[],[f3397,f1350,f1004,f964,f225,f177,f170,f163,f3399,f280])).

fof(f3397,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f3396,f226])).

fof(f3396,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f3395,f164])).

fof(f3395,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_214 ),
    inference(duplicate_literal_removal,[],[f3394])).

fof(f3394,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_214 ),
    inference(resolution,[],[f2390,f737])).

fof(f2390,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK4(sK5,X0))
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f2388,f1351])).

fof(f2388,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v7_waybel_0(sK4(sK5,X0))
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_waybel_0(sK4(sK5,X0),sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147 ),
    inference(resolution,[],[f2174,f968])).

fof(f2174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k10_yellow_6(sK5,sK4(sK5,X0)),k1_xboole_0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140
    | ~ spl15_147 ),
    inference(subsumption_resolution,[],[f2173,f1005])).

fof(f2173,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(k10_yellow_6(sK5,sK4(sK5,X0)),k1_xboole_0)
        | v1_xboole_0(u1_struct_0(sK5))
        | r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140 ),
    inference(resolution,[],[f2162,f143])).

fof(f2162,plain,
    ( ! [X0] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(k10_yellow_6(sK5,sK4(sK5,X0)),k1_xboole_0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_140 ),
    inference(superposition,[],[f1889,f965])).

fof(f1889,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k10_yellow_6(sK5,sK4(sK5,X2)),k1_zfmisc_1(X3))
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X2)))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | m1_subset_1(o_3_4_yellow19(sK5,X2,sK4(sK5,X2)),X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18 ),
    inference(resolution,[],[f1886,f153])).

fof(f1886,plain,
    ( ! [X0] :
        ( r2_hidden(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f1880,f226])).

fof(f3384,plain,
    ( ~ spl15_31
    | spl15_412
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(avatar_split_clause,[],[f2504,f1350,f225,f177,f170,f163,f3382,f280])).

fof(f2504,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f2503,f226])).

fof(f2503,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f2502,f164])).

fof(f2502,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(duplicate_literal_removal,[],[f2501])).

fof(f2501,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0)))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(resolution,[],[f1893,f737])).

fof(f1893,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK4(sK5,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f1887,f1351])).

fof(f1887,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,sK4(sK5,X0)))
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(o_3_4_yellow19(sK5,X0,sK4(sK5,X0)),u1_struct_0(sK5))
        | ~ l1_waybel_0(sK4(sK5,X0),sK5)
        | ~ v7_waybel_0(sK4(sK5,X0))
        | ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | r3_waybel_9(sK5,sK4(sK5,X0),o_3_4_yellow19(sK5,X0,sK4(sK5,X0))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_18 ),
    inference(resolution,[],[f1886,f1322])).

fof(f3012,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_410
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_37
    | ~ spl15_112 ),
    inference(avatar_split_clause,[],[f2387,f838,f310,f177,f170,f163,f3010,f853,f847,f835])).

fof(f2387,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_37
    | ~ spl15_112 ),
    inference(subsumption_resolution,[],[f2386,f311])).

fof(f2386,plain,
    ( ! [X7] :
        ( v2_struct_0(X7)
        | ~ l1_waybel_0(X7,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X7))
        | ~ v7_waybel_0(X7)
        | ~ m2_yellow_6(X7,sK5,sK7(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | ~ v4_orders_2(X7)
        | sP1(sK5)
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X7)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112 ),
    inference(subsumption_resolution,[],[f2381,f839])).

fof(f2903,plain,
    ( ~ spl15_409
    | ~ spl15_406 ),
    inference(avatar_split_clause,[],[f2894,f2888,f2901])).

fof(f2901,plain,
    ( spl15_409
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_409])])).

fof(f2888,plain,
    ( spl15_406
  <=> r2_hidden(sK10(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5))))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_406])])).

fof(f2894,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5))))))
    | ~ spl15_406 ),
    inference(resolution,[],[f2889,f141])).

fof(f2889,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5))))),u1_struct_0(sK5))
    | ~ spl15_406 ),
    inference(avatar_component_clause,[],[f2888])).

fof(f2890,plain,
    ( spl15_404
    | spl15_406
    | ~ spl15_164
    | ~ spl15_402 ),
    inference(avatar_split_clause,[],[f2876,f2871,f1080,f2888,f2882])).

fof(f2882,plain,
    ( spl15_404
  <=> v1_xboole_0(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_404])])).

fof(f2871,plain,
    ( spl15_402
  <=> m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_402])])).

fof(f2876,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5))))),u1_struct_0(sK5))
    | v1_xboole_0(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_164
    | ~ spl15_402 ),
    inference(resolution,[],[f2872,f1081])).

fof(f2872,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | ~ spl15_402 ),
    inference(avatar_component_clause,[],[f2871])).

fof(f2873,plain,
    ( spl15_402
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f2866,f2792,f1531,f1496,f1225,f890,f859,f177,f170,f163,f2871])).

fof(f859,plain,
    ( spl15_118
  <=> v7_waybel_0(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_118])])).

fof(f890,plain,
    ( spl15_122
  <=> v4_orders_2(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_122])])).

fof(f1531,plain,
    ( spl15_238
  <=> m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_238])])).

fof(f2866,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2865,f1497])).

fof(f2865,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2864,f891])).

fof(f891,plain,
    ( v4_orders_2(sK11(sK5,sK7(sK5)))
    | ~ spl15_122 ),
    inference(avatar_component_clause,[],[f890])).

fof(f2864,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_190
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2863,f860])).

fof(f860,plain,
    ( v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_118 ),
    inference(avatar_component_clause,[],[f859])).

fof(f2863,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_190
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2862,f1226])).

fof(f2862,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_238
    | ~ spl15_396 ),
    inference(resolution,[],[f2840,f1532])).

fof(f1532,plain,
    ( m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,sK11(sK5,sK7(sK5)))
    | ~ spl15_238 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f2840,plain,
    ( ! [X5] :
        ( ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,X5)
        | m1_subset_1(o_3_4_yellow19(sK5,X5,sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
        | ~ l1_waybel_0(X5,sK5)
        | ~ v7_waybel_0(X5)
        | ~ v4_orders_2(X5)
        | v2_struct_0(X5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2839,f164])).

fof(f2839,plain,
    ( ! [X5] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X5,sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ v7_waybel_0(X5)
        | ~ v4_orders_2(X5)
        | v2_struct_0(X5)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2838,f171])).

fof(f2838,plain,
    ( ! [X5] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X5,sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ v7_waybel_0(X5)
        | ~ v4_orders_2(X5)
        | v2_struct_0(X5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_4
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2831,f178])).

fof(f2831,plain,
    ( ! [X5] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X5,sK11(sK5,sK11(sK5,sK7(sK5)))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,X5)
        | ~ l1_waybel_0(X5,sK5)
        | ~ v7_waybel_0(X5)
        | ~ v4_orders_2(X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_396 ),
    inference(superposition,[],[f152,f2793])).

fof(f2859,plain,
    ( spl15_398
    | ~ spl15_401
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(avatar_split_clause,[],[f2846,f2792,f1571,f1564,f1556,f177,f170,f163,f2857,f2851])).

fof(f2857,plain,
    ( spl15_401
  <=> ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_401])])).

fof(f2846,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2845,f164])).

fof(f2845,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2844,f171])).

fof(f2844,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_4
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2843,f178])).

fof(f2843,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_242
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2842,f1565])).

fof(f2842,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_240
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2841,f1557])).

fof(f2841,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_244
    | ~ spl15_396 ),
    inference(subsumption_resolution,[],[f2833,f1572])).

fof(f2833,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_396 ),
    inference(trivial_inequality_removal,[],[f2832])).

fof(f2832,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_396 ),
    inference(superposition,[],[f134,f2793])).

fof(f2794,plain,
    ( spl15_396
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_394 ),
    inference(avatar_split_clause,[],[f2785,f2778,f401,f391,f2792])).

fof(f2778,plain,
    ( spl15_394
  <=> v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_394])])).

fof(f2785,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))) = k1_xboole_0
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_394 ),
    inference(forward_demodulation,[],[f2781,f402])).

fof(f2781,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_394 ),
    inference(resolution,[],[f2779,f395])).

fof(f2779,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_394 ),
    inference(avatar_component_clause,[],[f2778])).

fof(f2780,plain,
    ( spl15_392
    | spl15_394
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_238 ),
    inference(avatar_split_clause,[],[f1885,f1531,f1496,f1225,f890,f859,f177,f170,f163,f2778,f2772])).

fof(f2772,plain,
    ( spl15_392
  <=> r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_392])])).

fof(f1885,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1884,f1226])).

fof(f1884,plain,
    ( ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1883,f1497])).

fof(f1883,plain,
    ( v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1882,f891])).

fof(f1882,plain,
    ( ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1876,f860])).

fof(f1876,plain,
    ( ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | r2_hidden(o_3_4_yellow19(sK5,sK11(sK5,sK7(sK5)),sK11(sK5,sK11(sK5,sK7(sK5)))),k10_yellow_6(sK5,sK11(sK5,sK11(sK5,sK7(sK5)))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_238 ),
    inference(resolution,[],[f1843,f1532])).

fof(f2755,plain,
    ( spl15_360
    | spl15_390
    | ~ spl15_364 ),
    inference(avatar_split_clause,[],[f2640,f2625,f2753,f2605])).

fof(f2605,plain,
    ( spl15_360
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_360])])).

fof(f2753,plain,
    ( spl15_390
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_390])])).

fof(f2625,plain,
    ( spl15_364
  <=> k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_364])])).

fof(f2640,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(X0))
        | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) )
    | ~ spl15_364 ),
    inference(superposition,[],[f473,f2626])).

fof(f2626,plain,
    ( k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_364 ),
    inference(avatar_component_clause,[],[f2625])).

fof(f2751,plain,
    ( spl15_142
    | ~ spl15_389
    | ~ spl15_140
    | ~ spl15_384 ),
    inference(avatar_split_clause,[],[f2735,f2730,f964,f2748,f993])).

fof(f993,plain,
    ( spl15_142
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_142])])).

fof(f2748,plain,
    ( spl15_389
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_389])])).

fof(f2730,plain,
    ( spl15_384
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_384])])).

fof(f2735,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_384 ),
    inference(superposition,[],[f2733,f965])).

fof(f2733,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_384 ),
    inference(resolution,[],[f2731,f142])).

fof(f2731,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_384 ),
    inference(avatar_component_clause,[],[f2730])).

fof(f2750,plain,
    ( ~ spl15_389
    | spl15_387 ),
    inference(avatar_split_clause,[],[f2743,f2740,f2748])).

fof(f2740,plain,
    ( spl15_387
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_387])])).

fof(f2743,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_387 ),
    inference(resolution,[],[f2741,f142])).

fof(f2741,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_387 ),
    inference(avatar_component_clause,[],[f2740])).

fof(f2742,plain,
    ( spl15_142
    | ~ spl15_387
    | ~ spl15_140
    | ~ spl15_384 ),
    inference(avatar_split_clause,[],[f2734,f2730,f964,f2740,f993])).

fof(f2734,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_384 ),
    inference(superposition,[],[f2731,f965])).

fof(f2732,plain,
    ( spl15_378
    | spl15_384
    | ~ spl15_370 ),
    inference(avatar_split_clause,[],[f2690,f2663,f2730,f2712])).

fof(f2712,plain,
    ( spl15_378
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_378])])).

fof(f2663,plain,
    ( spl15_370
  <=> r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_370])])).

fof(f2690,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))) )
    | ~ spl15_370 ),
    inference(resolution,[],[f2667,f473])).

fof(f2667,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_370 ),
    inference(resolution,[],[f2664,f153])).

fof(f2664,plain,
    ( r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_370 ),
    inference(avatar_component_clause,[],[f2663])).

fof(f2728,plain,
    ( ~ spl15_383
    | spl15_381 ),
    inference(avatar_split_clause,[],[f2721,f2718,f2726])).

fof(f2726,plain,
    ( spl15_383
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_383])])).

fof(f2718,plain,
    ( spl15_381
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_381])])).

fof(f2721,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_381 ),
    inference(resolution,[],[f2719,f142])).

fof(f2719,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_381 ),
    inference(avatar_component_clause,[],[f2718])).

fof(f2720,plain,
    ( spl15_378
    | ~ spl15_381
    | spl15_373 ),
    inference(avatar_split_clause,[],[f2680,f2677,f2718,f2712])).

fof(f2677,plain,
    ( spl15_373
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_373])])).

fof(f2680,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))
    | ~ spl15_373 ),
    inference(resolution,[],[f2678,f473])).

fof(f2678,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_373 ),
    inference(avatar_component_clause,[],[f2677])).

fof(f2705,plain,
    ( spl15_142
    | ~ spl15_377
    | ~ spl15_140
    | ~ spl15_370 ),
    inference(avatar_split_clause,[],[f2692,f2663,f964,f2703,f993])).

fof(f2703,plain,
    ( spl15_377
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_377])])).

fof(f2692,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_370 ),
    inference(superposition,[],[f2667,f965])).

fof(f2688,plain,
    ( ~ spl15_375
    | spl15_373 ),
    inference(avatar_split_clause,[],[f2681,f2677,f2686])).

fof(f2686,plain,
    ( spl15_375
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_375])])).

fof(f2681,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_373 ),
    inference(resolution,[],[f2678,f142])).

fof(f2679,plain,
    ( ~ spl15_373
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_370 ),
    inference(avatar_split_clause,[],[f2671,f2663,f401,f391,f2677])).

fof(f2671,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_370 ),
    inference(forward_demodulation,[],[f2666,f402])).

fof(f2666,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_370 ),
    inference(resolution,[],[f2664,f394])).

fof(f2672,plain,
    ( ~ spl15_361
    | ~ spl15_370 ),
    inference(avatar_split_clause,[],[f2670,f2663,f2602])).

fof(f2602,plain,
    ( spl15_361
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_361])])).

fof(f2670,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_370 ),
    inference(resolution,[],[f2664,f151])).

fof(f2665,plain,
    ( spl15_360
    | spl15_370
    | ~ spl15_364 ),
    inference(avatar_split_clause,[],[f2642,f2625,f2663,f2605])).

fof(f2642,plain,
    ( r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_364 ),
    inference(superposition,[],[f375,f2626])).

fof(f2658,plain,
    ( spl15_360
    | ~ spl15_369
    | ~ spl15_364 ),
    inference(avatar_split_clause,[],[f2641,f2625,f2656,f2605])).

fof(f2656,plain,
    ( spl15_369
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_369])])).

fof(f2641,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))),k1_xboole_0)
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_364 ),
    inference(superposition,[],[f377,f2626])).

fof(f377,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK10(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f375,f141])).

fof(f2650,plain,
    ( spl15_366
    | ~ spl15_364 ),
    inference(avatar_split_clause,[],[f2643,f2625,f2648])).

fof(f2648,plain,
    ( spl15_366
  <=> m1_subset_1(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_366])])).

fof(f2643,plain,
    ( m1_subset_1(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_364 ),
    inference(superposition,[],[f140,f2626])).

fof(f2627,plain,
    ( spl15_364
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_362 ),
    inference(avatar_split_clause,[],[f2618,f2611,f401,f391,f2625])).

fof(f2611,plain,
    ( spl15_362
  <=> v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_362])])).

fof(f2618,plain,
    ( k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_362 ),
    inference(forward_demodulation,[],[f2614,f402])).

fof(f2614,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl15_54
    | ~ spl15_362 ),
    inference(resolution,[],[f2612,f395])).

fof(f2612,plain,
    ( v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))))
    | ~ spl15_362 ),
    inference(avatar_component_clause,[],[f2611])).

fof(f2613,plain,
    ( spl15_358
    | spl15_360
    | spl15_362
    | spl15_83
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f2590,f964,f555,f2611,f2605,f2599])).

fof(f2599,plain,
    ( spl15_358
  <=> m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_358])])).

fof(f2590,plain,
    ( v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f2589,f965])).

fof(f2589,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(subsumption_resolution,[],[f2588,f556])).

fof(f2588,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))))
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f2587,f965])).

fof(f2587,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))))
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f2578,f965])).

fof(f2578,plain,
    ( m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_xboole_0)))))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5)))))))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))))
    | ~ spl15_140 ),
    inference(superposition,[],[f2027,f965])).

fof(f2027,plain,(
    ! [X3] :
      ( m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(X3))))))),X3)
      | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(X3))))))
      | v1_xboole_0(sK10(k1_zfmisc_1(X3)))
      | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(k1_zfmisc_1(X3))))))) ) ),
    inference(resolution,[],[f1451,f140])).

fof(f1451,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(X1)))))
      | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X1)
      | m1_subset_1(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(X1))))),X2) ) ),
    inference(resolution,[],[f715,f153])).

fof(f715,plain,(
    ! [X2] :
      ( r2_hidden(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(X2))))),X2)
      | v1_xboole_0(X2)
      | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(X2)))))
      | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(X2)))) ) ),
    inference(resolution,[],[f488,f140])).

fof(f488,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | v1_xboole_0(X2)
      | r2_hidden(sK10(sK10(X1)),X2)
      | v1_xboole_0(sK10(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f476,f473])).

fof(f2509,plain,
    ( spl15_344
    | spl15_356
    | ~ spl15_340 ),
    inference(avatar_split_clause,[],[f2429,f2417,f2507,f2449])).

fof(f2449,plain,
    ( spl15_344
  <=> v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_344])])).

fof(f2507,plain,
    ( spl15_356
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_356])])).

fof(f2417,plain,
    ( spl15_340
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_340])])).

fof(f2429,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) )
    | ~ spl15_340 ),
    inference(superposition,[],[f473,f2418])).

fof(f2418,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_340 ),
    inference(avatar_component_clause,[],[f2417])).

fof(f2500,plain,
    ( spl15_142
    | ~ spl15_355
    | ~ spl15_140
    | ~ spl15_348 ),
    inference(avatar_split_clause,[],[f2492,f2462,f964,f2498,f993])).

fof(f2498,plain,
    ( spl15_355
  <=> ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_355])])).

fof(f2462,plain,
    ( spl15_348
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_348])])).

fof(f2492,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_348 ),
    inference(superposition,[],[f2470,f965])).

fof(f2470,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_348 ),
    inference(resolution,[],[f2463,f153])).

fof(f2463,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_348 ),
    inference(avatar_component_clause,[],[f2462])).

fof(f2490,plain,
    ( ~ spl15_353
    | spl15_351 ),
    inference(avatar_split_clause,[],[f2483,f2480,f2488])).

fof(f2488,plain,
    ( spl15_353
  <=> ~ r2_hidden(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_353])])).

fof(f2480,plain,
    ( spl15_351
  <=> ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_351])])).

fof(f2483,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_351 ),
    inference(resolution,[],[f2481,f142])).

fof(f2481,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_351 ),
    inference(avatar_component_clause,[],[f2480])).

fof(f2482,plain,
    ( ~ spl15_351
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_348 ),
    inference(avatar_split_clause,[],[f2474,f2462,f401,f391,f2480])).

fof(f2474,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_348 ),
    inference(forward_demodulation,[],[f2469,f402])).

fof(f2469,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_348 ),
    inference(resolution,[],[f2463,f394])).

fof(f2475,plain,
    ( ~ spl15_345
    | ~ spl15_348 ),
    inference(avatar_split_clause,[],[f2473,f2462,f2446])).

fof(f2446,plain,
    ( spl15_345
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_345])])).

fof(f2473,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_348 ),
    inference(resolution,[],[f2463,f151])).

fof(f2464,plain,
    ( spl15_344
    | spl15_348
    | ~ spl15_340 ),
    inference(avatar_split_clause,[],[f2431,f2417,f2462,f2449])).

fof(f2431,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_340 ),
    inference(superposition,[],[f375,f2418])).

fof(f2457,plain,
    ( spl15_344
    | ~ spl15_347
    | ~ spl15_340 ),
    inference(avatar_split_clause,[],[f2430,f2417,f2455,f2449])).

fof(f2455,plain,
    ( spl15_347
  <=> ~ r2_hidden(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_347])])).

fof(f2430,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_340 ),
    inference(superposition,[],[f377,f2418])).

fof(f2439,plain,
    ( spl15_342
    | ~ spl15_340 ),
    inference(avatar_split_clause,[],[f2432,f2417,f2437])).

fof(f2437,plain,
    ( spl15_342
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_342])])).

fof(f2432,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_340 ),
    inference(superposition,[],[f140,f2418])).

fof(f2419,plain,
    ( spl15_340
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_338 ),
    inference(avatar_split_clause,[],[f2410,f2403,f401,f391,f2417])).

fof(f2403,plain,
    ( spl15_338
  <=> v1_xboole_0(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_338])])).

fof(f2410,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_338 ),
    inference(forward_demodulation,[],[f2406,f402])).

fof(f2406,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_54
    | ~ spl15_338 ),
    inference(resolution,[],[f2404,f395])).

fof(f2404,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))))
    | ~ spl15_338 ),
    inference(avatar_component_clause,[],[f2403])).

fof(f2405,plain,
    ( spl15_336
    | spl15_338
    | spl15_330
    | ~ spl15_140
    | spl15_147
    | ~ spl15_328 ),
    inference(avatar_split_clause,[],[f2340,f2336,f1004,f964,f2347,f2403,f2397])).

fof(f2397,plain,
    ( spl15_336
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_336])])).

fof(f2347,plain,
    ( spl15_330
  <=> v1_xboole_0(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_330])])).

fof(f2336,plain,
    ( spl15_328
  <=> m1_subset_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_328])])).

fof(f2340,plain,
    ( v1_xboole_0(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))
    | v1_xboole_0(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))))
    | r2_hidden(sK10(sK10(k1_zfmisc_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))),u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_147
    | ~ spl15_328 ),
    inference(resolution,[],[f2337,f1206])).

fof(f2337,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k1_xboole_0)
    | ~ spl15_328 ),
    inference(avatar_component_clause,[],[f2336])).

fof(f2368,plain,
    ( ~ spl15_335
    | ~ spl15_332 ),
    inference(avatar_split_clause,[],[f2359,f2353,f2366])).

fof(f2366,plain,
    ( spl15_335
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_335])])).

fof(f2353,plain,
    ( spl15_332
  <=> r2_hidden(sK10(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_332])])).

fof(f2359,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))))
    | ~ spl15_332 ),
    inference(resolution,[],[f2354,f141])).

fof(f2354,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),u1_struct_0(sK5))
    | ~ spl15_332 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2355,plain,
    ( spl15_330
    | spl15_332
    | ~ spl15_164
    | ~ spl15_328 ),
    inference(avatar_split_clause,[],[f2341,f2336,f1080,f2353,f2347])).

fof(f2341,plain,
    ( r2_hidden(sK10(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5)))),u1_struct_0(sK5))
    | v1_xboole_0(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))))
    | ~ spl15_164
    | ~ spl15_328 ),
    inference(resolution,[],[f2337,f1081])).

fof(f2338,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_328
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108
    | ~ spl15_112
    | ~ spl15_324 ),
    inference(avatar_split_clause,[],[f2331,f2266,f838,f794,f177,f170,f163,f2336,f853,f847,f835])).

fof(f2331,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k1_xboole_0)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108
    | ~ spl15_112
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2329,f839])).

fof(f2329,plain,
    ( m1_subset_1(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k1_xboole_0)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108
    | ~ spl15_324 ),
    inference(resolution,[],[f2313,f795])).

fof(f795,plain,
    ( m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,sK7(sK5))
    | ~ spl15_108 ),
    inference(avatar_component_clause,[],[f794])).

fof(f2313,plain,
    ( ! [X3] :
        ( ~ m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,X3)
        | m1_subset_1(o_3_4_yellow19(sK5,X3,sK11(sK5,sK7(sK5))),k1_xboole_0)
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2312,f164])).

fof(f2312,plain,
    ( ! [X3] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X3,sK11(sK5,sK7(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | v2_struct_0(sK5) )
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2311,f171])).

fof(f2311,plain,
    ( ! [X3] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X3,sK11(sK5,sK7(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_4
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2303,f178])).

fof(f2303,plain,
    ( ! [X3] :
        ( m1_subset_1(o_3_4_yellow19(sK5,X3,sK11(sK5,sK7(sK5))),k1_xboole_0)
        | ~ m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(sK5)
        | ~ v2_pre_topc(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_324 ),
    inference(superposition,[],[f152,f2267])).

fof(f2327,plain,
    ( ~ spl15_327
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_324 ),
    inference(avatar_split_clause,[],[f2320,f2266,f1496,f1225,f890,f859,f177,f170,f163,f2325])).

fof(f2325,plain,
    ( spl15_327
  <=> ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_327])])).

fof(f2320,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2319,f164])).

fof(f2319,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2318,f171])).

fof(f2318,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_4
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2317,f178])).

fof(f2317,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2316,f1497])).

fof(f2316,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2315,f891])).

fof(f2315,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_190
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2314,f860])).

fof(f2314,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_190
    | ~ spl15_324 ),
    inference(subsumption_resolution,[],[f2305,f1226])).

fof(f2305,plain,
    ( ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_324 ),
    inference(trivial_inequality_removal,[],[f2304])).

fof(f2304,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK11(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_324 ),
    inference(superposition,[],[f134,f2267])).

fof(f2268,plain,
    ( spl15_324
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_322 ),
    inference(avatar_split_clause,[],[f2259,f2252,f401,f391,f2266])).

fof(f2252,plain,
    ( spl15_322
  <=> v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_322])])).

fof(f2259,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK7(sK5))) = k1_xboole_0
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_322 ),
    inference(forward_demodulation,[],[f2255,f402])).

fof(f2255,plain,
    ( k10_yellow_6(sK5,sK11(sK5,sK7(sK5))) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_322 ),
    inference(resolution,[],[f2253,f395])).

fof(f2253,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_322 ),
    inference(avatar_component_clause,[],[f2252])).

fof(f2254,plain,
    ( spl15_320
    | spl15_322
    | ~ spl15_117
    | spl15_110
    | ~ spl15_115
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108
    | ~ spl15_112 ),
    inference(avatar_split_clause,[],[f1881,f838,f794,f177,f170,f163,f847,f835,f853,f2252,f2246])).

fof(f2246,plain,
    ( spl15_320
  <=> r2_hidden(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k10_yellow_6(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_320])])).

fof(f1881,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK7(sK5))))
    | r2_hidden(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k10_yellow_6(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108
    | ~ spl15_112 ),
    inference(subsumption_resolution,[],[f1874,f839])).

fof(f1874,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK11(sK5,sK7(sK5))))
    | r2_hidden(o_3_4_yellow19(sK5,sK7(sK5),sK11(sK5,sK7(sK5))),k10_yellow_6(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_108 ),
    inference(resolution,[],[f1843,f795])).

fof(f2168,plain,
    ( ~ spl15_31
    | spl15_318
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2146,f177,f170,f163,f2166,f280])).

fof(f2166,plain,
    ( spl15_318
  <=> ! [X1] :
        ( ~ v4_orders_2(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))),sK5)
        | ~ v7_waybel_0(X1)
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_318])])).

fof(f2146,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2144,f164])).

fof(f2144,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))),sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2138])).

fof(f2138,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))
        | ~ v7_waybel_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X1))))),sK5)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1904,f148])).

fof(f1904,plain,
    ( ! [X3] :
        ( m2_yellow_6(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))),sK5,X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ v7_waybel_0(X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f1900,f883])).

fof(f1900,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3)))),u1_struct_0(sK5))
        | m2_yellow_6(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))),sK5,X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1897])).

fof(f1897,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3)))),u1_struct_0(sK5))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | m2_yellow_6(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))),sK5,X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1343,f1444])).

fof(f2158,plain,
    ( ~ spl15_31
    | spl15_316
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2148,f177,f170,f163,f2156,f280])).

fof(f2156,plain,
    ( spl15_316
  <=> ! [X3] :
        ( ~ v4_orders_2(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))))
        | ~ v7_waybel_0(X3)
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_316])])).

fof(f2148,plain,
    ( ! [X3] :
        ( ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2142,f164])).

fof(f2142,plain,
    ( ! [X3] :
        ( ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2140])).

fof(f2140,plain,
    ( ! [X3] :
        ( ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))
        | ~ v7_waybel_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X3))))))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1904,f146])).

fof(f2152,plain,
    ( ~ spl15_31
    | spl15_314
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2147,f177,f170,f163,f2150,f280])).

fof(f2150,plain,
    ( spl15_314
  <=> ! [X2] :
        ( ~ v4_orders_2(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))))
        | ~ v7_waybel_0(X2)
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_314])])).

fof(f2147,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2143,f164])).

fof(f2143,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2139])).

fof(f2139,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | v1_xboole_0(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))
        | ~ v7_waybel_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(sK10(k1_zfmisc_1(k10_yellow_6(sK5,X2))))))
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1904,f147])).

fof(f2126,plain,
    ( ~ spl15_31
    | spl15_312
    | spl15_1
    | ~ spl15_18
    | ~ spl15_310 ),
    inference(avatar_split_clause,[],[f2122,f2116,f225,f163,f2124,f280])).

fof(f2124,plain,
    ( spl15_312
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(sK4(sK5,X0))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_312])])).

fof(f2116,plain,
    ( spl15_310
  <=> ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_310])])).

fof(f2122,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_310 ),
    inference(subsumption_resolution,[],[f2121,f226])).

fof(f2121,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_310 ),
    inference(subsumption_resolution,[],[f2120,f164])).

fof(f2120,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_310 ),
    inference(duplicate_literal_removal,[],[f2119])).

fof(f2119,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_310 ),
    inference(resolution,[],[f2117,f735])).

fof(f2117,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | v2_struct_0(sK4(sK5,X0)) )
    | ~ spl15_310 ),
    inference(avatar_component_clause,[],[f2116])).

fof(f2118,plain,
    ( ~ spl15_31
    | spl15_310
    | spl15_1
    | ~ spl15_18
    | ~ spl15_308 ),
    inference(avatar_split_clause,[],[f2114,f2107,f225,f163,f2116,f280])).

fof(f2107,plain,
    ( spl15_308
  <=> ! [X1] :
        ( v2_struct_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | ~ v7_waybel_0(sK4(sK5,X1))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_308])])).

fof(f2114,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_308 ),
    inference(subsumption_resolution,[],[f2113,f226])).

fof(f2113,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_1
    | ~ spl15_308 ),
    inference(subsumption_resolution,[],[f2112,f164])).

fof(f2112,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_308 ),
    inference(duplicate_literal_removal,[],[f2111])).

fof(f2111,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X0)),sK5)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5) )
    | ~ spl15_308 ),
    inference(resolution,[],[f2108,f737])).

fof(f2108,plain,
    ( ! [X1] :
        ( ~ v7_waybel_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | v2_struct_0(sK4(sK5,X1))
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1) )
    | ~ spl15_308 ),
    inference(avatar_component_clause,[],[f2107])).

fof(f2109,plain,
    ( ~ spl15_31
    | spl15_308
    | spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(avatar_split_clause,[],[f2007,f1994,f1350,f163,f2107,f280])).

fof(f1994,plain,
    ( spl15_296
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | v2_struct_0(sK4(sK5,X0))
        | m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_296])])).

fof(f2007,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ v7_waybel_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2006,f1351])).

fof(f2006,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ l1_waybel_0(sK4(sK5,X1),sK5)
        | ~ v7_waybel_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2003,f164])).

fof(f2003,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ l1_waybel_0(sK4(sK5,X1),sK5)
        | ~ v7_waybel_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(duplicate_literal_removal,[],[f1998])).

fof(f1998,plain,
    ( ! [X1] :
        ( v2_struct_0(sK4(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK11(sK5,sK4(sK5,X1)),sK5)
        | ~ l1_waybel_0(sK4(sK5,X1),sK5)
        | ~ v7_waybel_0(sK4(sK5,X1))
        | ~ v4_orders_2(sK4(sK5,X1))
        | v2_struct_0(sK4(sK5,X1))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(resolution,[],[f1995,f148])).

fof(f1995,plain,
    ( ! [X0] :
        ( m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl15_296 ),
    inference(avatar_component_clause,[],[f1994])).

fof(f2102,plain,
    ( ~ spl15_31
    | spl15_306
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2085,f177,f170,f163,f2100,f280])).

fof(f2100,plain,
    ( spl15_306
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(k10_yellow_6(sK5,X1))),sK5)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ l1_waybel_0(X1,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_306])])).

fof(f2085,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(k10_yellow_6(sK5,X1))),sK5)
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2083,f164])).

fof(f2083,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(k10_yellow_6(sK5,X1))),sK5)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2077])).

fof(f2077,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | l1_waybel_0(sK9(sK5,X1,sK10(k10_yellow_6(sK5,X1))),sK5)
        | ~ l1_waybel_0(X1,sK5)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f2075,f148])).

fof(f2075,plain,
    ( ! [X0] :
        ( m2_yellow_6(sK9(sK5,X0,sK10(k10_yellow_6(sK5,X0))),sK5,X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2074,f869])).

fof(f2074,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | m2_yellow_6(sK9(sK5,X0,sK10(k10_yellow_6(sK5,X0))),sK5,X0)
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2071])).

fof(f2071,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X0))
        | ~ v7_waybel_0(X0)
        | m2_yellow_6(sK9(sK5,X0,sK10(k10_yellow_6(sK5,X0))),sK5,X0)
        | ~ m1_subset_1(k10_yellow_6(sK5,X0),k1_zfmisc_1(u1_struct_0(sK5)))
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1738,f473])).

fof(f1738,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK10(k10_yellow_6(sK5,X3)),u1_struct_0(sK5))
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ v7_waybel_0(X3)
        | m2_yellow_6(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))),sK5,X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f1736])).

fof(f1736,plain,
    ( ! [X3] :
        ( ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ m1_subset_1(sK10(k10_yellow_6(sK5,X3)),u1_struct_0(sK5))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | m2_yellow_6(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))),sK5,X3) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1733,f1444])).

fof(f2097,plain,
    ( ~ spl15_31
    | spl15_304
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2087,f177,f170,f163,f2095,f280])).

fof(f2095,plain,
    ( spl15_304
  <=> ! [X3] :
        ( v2_struct_0(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))))
        | ~ v4_orders_2(X3)
        | ~ v7_waybel_0(X3)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ l1_waybel_0(X3,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_304])])).

fof(f2087,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2081,f164])).

fof(f2081,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2079])).

fof(f2079,plain,
    ( ! [X3] :
        ( v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK9(sK5,X3,sK10(k10_yellow_6(sK5,X3))))
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3)
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f2075,f146])).

fof(f2091,plain,
    ( ~ spl15_31
    | spl15_302
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f2086,f177,f170,f163,f2089,f280])).

fof(f2089,plain,
    ( spl15_302
  <=> ! [X2] :
        ( v2_struct_0(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(k10_yellow_6(sK5,X2))))
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | ~ l1_waybel_0(X2,sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_302])])).

fof(f2086,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(k10_yellow_6(sK5,X2))))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f2082,f164])).

fof(f2082,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(k10_yellow_6(sK5,X2))))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(duplicate_literal_removal,[],[f2078])).

fof(f2078,plain,
    ( ! [X2] :
        ( v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK9(sK5,X2,sK10(k10_yellow_6(sK5,X2))))
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f2075,f147])).

fof(f2020,plain,
    ( ~ spl15_31
    | spl15_300
    | spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(avatar_split_clause,[],[f2011,f1994,f1350,f163,f2018,f280])).

fof(f2018,plain,
    ( spl15_300
  <=> ! [X3] :
        ( v2_struct_0(sK4(sK5,X3))
        | ~ v4_orders_2(sK4(sK5,X3))
        | ~ v7_waybel_0(sK4(sK5,X3))
        | v4_orders_2(sK11(sK5,sK4(sK5,X3)))
        | ~ v4_orders_2(X3)
        | v2_struct_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | ~ v7_waybel_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_300])])).

fof(f2011,plain,
    ( ! [X3] :
        ( v2_struct_0(sK4(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK11(sK5,sK4(sK5,X3)))
        | ~ v7_waybel_0(sK4(sK5,X3))
        | ~ v4_orders_2(sK4(sK5,X3))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2010,f1351])).

fof(f2010,plain,
    ( ! [X3] :
        ( v2_struct_0(sK4(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK11(sK5,sK4(sK5,X3)))
        | ~ l1_waybel_0(sK4(sK5,X3),sK5)
        | ~ v7_waybel_0(sK4(sK5,X3))
        | ~ v4_orders_2(sK4(sK5,X3))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2001,f164])).

fof(f2001,plain,
    ( ! [X3] :
        ( v2_struct_0(sK4(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK11(sK5,sK4(sK5,X3)))
        | ~ l1_waybel_0(sK4(sK5,X3),sK5)
        | ~ v7_waybel_0(sK4(sK5,X3))
        | ~ v4_orders_2(sK4(sK5,X3))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(duplicate_literal_removal,[],[f2000])).

fof(f2000,plain,
    ( ! [X3] :
        ( v2_struct_0(sK4(sK5,X3))
        | ~ v7_waybel_0(X3)
        | ~ l1_waybel_0(X3,sK5)
        | v2_struct_0(X3)
        | ~ v4_orders_2(X3)
        | v4_orders_2(sK11(sK5,sK4(sK5,X3)))
        | ~ l1_waybel_0(sK4(sK5,X3),sK5)
        | ~ v7_waybel_0(sK4(sK5,X3))
        | ~ v4_orders_2(sK4(sK5,X3))
        | v2_struct_0(sK4(sK5,X3))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(resolution,[],[f1995,f146])).

fof(f2015,plain,
    ( ~ spl15_31
    | spl15_298
    | spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(avatar_split_clause,[],[f2009,f1994,f1350,f163,f2013,f280])).

fof(f2013,plain,
    ( spl15_298
  <=> ! [X2] :
        ( v2_struct_0(sK4(sK5,X2))
        | ~ v4_orders_2(sK4(sK5,X2))
        | ~ v7_waybel_0(sK4(sK5,X2))
        | v7_waybel_0(sK11(sK5,sK4(sK5,X2)))
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_298])])).

fof(f2009,plain,
    ( ! [X2] :
        ( v2_struct_0(sK4(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK11(sK5,sK4(sK5,X2)))
        | ~ v7_waybel_0(sK4(sK5,X2))
        | ~ v4_orders_2(sK4(sK5,X2))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_214
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2008,f1351])).

fof(f2008,plain,
    ( ! [X2] :
        ( v2_struct_0(sK4(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK11(sK5,sK4(sK5,X2)))
        | ~ l1_waybel_0(sK4(sK5,X2),sK5)
        | ~ v7_waybel_0(sK4(sK5,X2))
        | ~ v4_orders_2(sK4(sK5,X2))
        | ~ l1_struct_0(sK5) )
    | ~ spl15_1
    | ~ spl15_296 ),
    inference(subsumption_resolution,[],[f2002,f164])).

fof(f2002,plain,
    ( ! [X2] :
        ( v2_struct_0(sK4(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK11(sK5,sK4(sK5,X2)))
        | ~ l1_waybel_0(sK4(sK5,X2),sK5)
        | ~ v7_waybel_0(sK4(sK5,X2))
        | ~ v4_orders_2(sK4(sK5,X2))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(duplicate_literal_removal,[],[f1999])).

fof(f1999,plain,
    ( ! [X2] :
        ( v2_struct_0(sK4(sK5,X2))
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | v7_waybel_0(sK11(sK5,sK4(sK5,X2)))
        | ~ l1_waybel_0(sK4(sK5,X2),sK5)
        | ~ v7_waybel_0(sK4(sK5,X2))
        | ~ v4_orders_2(sK4(sK5,X2))
        | v2_struct_0(sK4(sK5,X2))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5) )
    | ~ spl15_296 ),
    inference(resolution,[],[f1995,f147])).

fof(f1996,plain,
    ( ~ spl15_31
    | spl15_296
    | spl15_1
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(avatar_split_clause,[],[f1992,f1350,f225,f163,f1994,f280])).

fof(f1992,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | ~ l1_waybel_0(X0,sK5)
        | m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_18
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f1991,f226])).

fof(f1991,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | ~ sP0(sK5)
        | ~ l1_waybel_0(X0,sK5)
        | m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_214 ),
    inference(subsumption_resolution,[],[f1990,f164])).

fof(f1990,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5)
        | ~ l1_waybel_0(X0,sK5)
        | m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0)) )
    | ~ spl15_214 ),
    inference(duplicate_literal_removal,[],[f1989])).

fof(f1989,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ sP0(sK5)
        | ~ l1_waybel_0(X0,sK5)
        | m2_yellow_6(sK11(sK5,sK4(sK5,X0)),sK5,sK4(sK5,X0))
        | v2_struct_0(sK4(sK5,X0))
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | ~ l1_waybel_0(X0,sK5)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl15_214 ),
    inference(resolution,[],[f1245,f1351])).

fof(f1245,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK4(X1,X0),X2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ sP0(X1)
      | ~ l1_waybel_0(X0,X1)
      | m2_yellow_6(sK11(X2,sK4(X1,X0)),X2,sK4(X1,X0))
      | v2_struct_0(sK4(X1,X0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f1244,f735])).

fof(f1244,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,X1)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ sP0(X1)
      | ~ l1_waybel_0(sK4(X1,X0),X2)
      | m2_yellow_6(sK11(X2,sK4(X1,X0)),X2,sK4(X1,X0))
      | ~ v4_orders_2(sK4(X1,X0))
      | v2_struct_0(sK4(X1,X0))
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f737,f149])).

fof(f1914,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_294
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_290 ),
    inference(avatar_split_clause,[],[f1868,f1856,f838,f177,f170,f163,f1912,f853,f847,f835])).

fof(f1912,plain,
    ( spl15_294
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | m2_yellow_6(sK9(sK5,sK7(sK5),X3),sK5,sK7(sK5))
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_294])])).

fof(f1868,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | m2_yellow_6(sK9(sK5,sK7(sK5),X3),sK5,sK7(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_290 ),
    inference(subsumption_resolution,[],[f1864,f839])).

fof(f1864,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | m2_yellow_6(sK9(sK5,sK7(sK5),X3),sK5,sK7(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_290 ),
    inference(duplicate_literal_removal,[],[f1861])).

fof(f1861,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | m2_yellow_6(sK9(sK5,sK7(sK5),X3),sK5,sK7(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_290 ),
    inference(resolution,[],[f1857,f1444])).

fof(f1910,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_292
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_290 ),
    inference(avatar_split_clause,[],[f1867,f1856,f838,f177,f170,f163,f1908,f853,f847,f835])).

fof(f1908,plain,
    ( spl15_292
  <=> ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK7(sK5),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_292])])).

fof(f1867,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK7(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_290 ),
    inference(subsumption_resolution,[],[f1865,f839])).

fof(f1865,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK7(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_290 ),
    inference(duplicate_literal_removal,[],[f1860])).

fof(f1860,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ m1_subset_1(X2,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | ~ v4_orders_2(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | r2_hidden(X2,k10_yellow_6(sK5,sK9(sK5,sK7(sK5),X2))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_290 ),
    inference(resolution,[],[f1857,f1576])).

fof(f1858,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_290
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f1819,f1799,f838,f177,f170,f163,f1856,f853,f847,f835])).

fof(f1819,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5))
        | ~ l1_waybel_0(sK7(sK5),sK5)
        | ~ v7_waybel_0(sK7(sK5))
        | v2_struct_0(sK7(sK5))
        | r3_waybel_9(sK5,sK7(sK5),X0) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(subsumption_resolution,[],[f1811,f839])).

fof(f1854,plain,
    ( spl15_274
    | ~ spl15_115
    | ~ spl15_117
    | spl15_110
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_140
    | ~ spl15_164
    | spl15_277 ),
    inference(avatar_split_clause,[],[f1766,f1762,f1080,f964,f838,f177,f170,f163,f835,f853,f847,f1752])).

fof(f1752,plain,
    ( spl15_274
  <=> v1_xboole_0(k10_yellow_6(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_274])])).

fof(f1762,plain,
    ( spl15_277
  <=> ~ r2_hidden(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_277])])).

fof(f1766,plain,
    ( v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_140
    | ~ spl15_164
    | ~ spl15_277 ),
    inference(subsumption_resolution,[],[f1765,f839])).

fof(f1765,plain,
    ( ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_164
    | ~ spl15_277 ),
    inference(resolution,[],[f1763,f1209])).

fof(f1209,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(k10_yellow_6(sK5,X0)),u1_struct_0(sK5))
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK5)
        | ~ v7_waybel_0(X0)
        | v1_xboole_0(k10_yellow_6(sK5,X0)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_164 ),
    inference(resolution,[],[f968,f1081])).

fof(f1763,plain,
    ( ~ r2_hidden(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_277 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f1852,plain,
    ( spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | ~ spl15_289
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f1826,f1799,f838,f177,f170,f163,f1850,f853,f847,f835])).

fof(f1850,plain,
    ( spl15_289
  <=> ~ v3_yellow_6(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_289])])).

fof(f1826,plain,
    ( ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(subsumption_resolution,[],[f1825,f164])).

fof(f1825,plain,
    ( ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(subsumption_resolution,[],[f1824,f171])).

fof(f1824,plain,
    ( ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(subsumption_resolution,[],[f1823,f178])).

fof(f1823,plain,
    ( ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_112
    | ~ spl15_282 ),
    inference(subsumption_resolution,[],[f1816,f839])).

fof(f1816,plain,
    ( ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_282 ),
    inference(trivial_inequality_removal,[],[f1815])).

fof(f1815,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v3_yellow_6(sK7(sK5),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_282 ),
    inference(superposition,[],[f134,f1800])).

fof(f1840,plain,
    ( ~ spl15_287
    | spl15_273
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f1806,f1799,f1746,f1838])).

fof(f1838,plain,
    ( spl15_287
  <=> ~ m1_subset_1(sK10(k1_xboole_0),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_287])])).

fof(f1746,plain,
    ( spl15_273
  <=> ~ m1_subset_1(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_273])])).

fof(f1806,plain,
    ( ~ m1_subset_1(sK10(k1_xboole_0),u1_struct_0(sK5))
    | ~ spl15_273
    | ~ spl15_282 ),
    inference(superposition,[],[f1747,f1800])).

fof(f1747,plain,
    ( ~ m1_subset_1(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_273 ),
    inference(avatar_component_clause,[],[f1746])).

fof(f1833,plain,
    ( ~ spl15_285
    | spl15_277
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f1805,f1799,f1762,f1831])).

fof(f1831,plain,
    ( spl15_285
  <=> ~ r2_hidden(sK10(k1_xboole_0),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_285])])).

fof(f1805,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),u1_struct_0(sK5))
    | ~ spl15_277
    | ~ spl15_282 ),
    inference(superposition,[],[f1763,f1800])).

fof(f1801,plain,
    ( spl15_282
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_274 ),
    inference(avatar_split_clause,[],[f1789,f1752,f401,f391,f1799])).

fof(f1789,plain,
    ( k10_yellow_6(sK5,sK7(sK5)) = k1_xboole_0
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_274 ),
    inference(forward_demodulation,[],[f1785,f402])).

fof(f1785,plain,
    ( k10_yellow_6(sK5,sK7(sK5)) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_274 ),
    inference(resolution,[],[f1753,f395])).

fof(f1753,plain,
    ( v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ spl15_274 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f1784,plain,
    ( ~ spl15_117
    | spl15_110
    | ~ spl15_115
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_140
    | spl15_279 ),
    inference(avatar_split_clause,[],[f1776,f1771,f964,f838,f177,f170,f163,f847,f835,f853])).

fof(f1771,plain,
    ( spl15_279
  <=> ~ m1_subset_1(k10_yellow_6(sK5,sK7(sK5)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_279])])).

fof(f1776,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112
    | ~ spl15_140
    | ~ spl15_279 ),
    inference(subsumption_resolution,[],[f1774,f839])).

fof(f1774,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_140
    | ~ spl15_279 ),
    inference(resolution,[],[f1772,f968])).

fof(f1772,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK7(sK5)),k1_xboole_0)
    | ~ spl15_279 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f1783,plain,
    ( ~ spl15_281
    | spl15_279 ),
    inference(avatar_split_clause,[],[f1775,f1771,f1781])).

fof(f1781,plain,
    ( spl15_281
  <=> ~ r2_hidden(k10_yellow_6(sK5,sK7(sK5)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_281])])).

fof(f1775,plain,
    ( ~ r2_hidden(k10_yellow_6(sK5,sK7(sK5)),k1_xboole_0)
    | ~ spl15_279 ),
    inference(resolution,[],[f1772,f142])).

fof(f1773,plain,
    ( spl15_274
    | ~ spl15_279
    | ~ spl15_140
    | spl15_273 ),
    inference(avatar_split_clause,[],[f1757,f1746,f964,f1771,f1752])).

fof(f1757,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK7(sK5)),k1_xboole_0)
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ spl15_140
    | ~ spl15_273 ),
    inference(forward_demodulation,[],[f1755,f965])).

fof(f1755,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK5,sK7(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ spl15_273 ),
    inference(resolution,[],[f1747,f473])).

fof(f1764,plain,
    ( ~ spl15_277
    | spl15_273 ),
    inference(avatar_split_clause,[],[f1756,f1746,f1762])).

fof(f1756,plain,
    ( ~ r2_hidden(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_273 ),
    inference(resolution,[],[f1747,f142])).

fof(f1754,plain,
    ( ~ spl15_273
    | spl15_274
    | ~ spl15_117
    | spl15_110
    | ~ spl15_115
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | spl15_37
    | ~ spl15_112 ),
    inference(avatar_split_clause,[],[f1741,f838,f310,f177,f170,f163,f847,f835,f853,f1752,f1746])).

fof(f1741,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | ~ m1_subset_1(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_37
    | ~ spl15_112 ),
    inference(subsumption_resolution,[],[f1740,f311])).

fof(f1740,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | sP1(sK5)
    | ~ m1_subset_1(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4
    | ~ spl15_112 ),
    inference(subsumption_resolution,[],[f1737,f839])).

fof(f1737,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | v1_xboole_0(k10_yellow_6(sK5,sK7(sK5)))
    | sP1(sK5)
    | ~ m1_subset_1(sK10(k10_yellow_6(sK5,sK7(sK5))),u1_struct_0(sK5))
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f1733,f132])).

fof(f1714,plain,
    ( spl15_258
    | spl15_270
    | ~ spl15_254 ),
    inference(avatar_split_clause,[],[f1633,f1621,f1712,f1654])).

fof(f1654,plain,
    ( spl15_258
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_258])])).

fof(f1712,plain,
    ( spl15_270
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_270])])).

fof(f1621,plain,
    ( spl15_254
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_254])])).

fof(f1633,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl15_254 ),
    inference(superposition,[],[f473,f1622])).

fof(f1622,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_254 ),
    inference(avatar_component_clause,[],[f1621])).

fof(f1705,plain,
    ( spl15_142
    | ~ spl15_269
    | ~ spl15_140
    | ~ spl15_262 ),
    inference(avatar_split_clause,[],[f1698,f1667,f964,f1703,f993])).

fof(f1703,plain,
    ( spl15_269
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_269])])).

fof(f1667,plain,
    ( spl15_262
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_262])])).

fof(f1698,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_262 ),
    inference(superposition,[],[f1676,f965])).

fof(f1676,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_262 ),
    inference(resolution,[],[f1668,f153])).

fof(f1668,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_262 ),
    inference(avatar_component_clause,[],[f1667])).

fof(f1696,plain,
    ( ~ spl15_267
    | spl15_265 ),
    inference(avatar_split_clause,[],[f1689,f1686,f1694])).

fof(f1694,plain,
    ( spl15_267
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_267])])).

fof(f1686,plain,
    ( spl15_265
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_265])])).

fof(f1689,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_265 ),
    inference(resolution,[],[f1687,f142])).

fof(f1687,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_265 ),
    inference(avatar_component_clause,[],[f1686])).

fof(f1688,plain,
    ( ~ spl15_265
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_262 ),
    inference(avatar_split_clause,[],[f1680,f1667,f401,f391,f1686])).

fof(f1680,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_262 ),
    inference(forward_demodulation,[],[f1675,f402])).

fof(f1675,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_262 ),
    inference(resolution,[],[f1668,f394])).

fof(f1681,plain,
    ( ~ spl15_259
    | ~ spl15_262 ),
    inference(avatar_split_clause,[],[f1679,f1667,f1651])).

fof(f1651,plain,
    ( spl15_259
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_259])])).

fof(f1679,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_262 ),
    inference(resolution,[],[f1668,f151])).

fof(f1669,plain,
    ( spl15_258
    | spl15_262
    | ~ spl15_254 ),
    inference(avatar_split_clause,[],[f1635,f1621,f1667,f1654])).

fof(f1635,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_254 ),
    inference(superposition,[],[f375,f1622])).

fof(f1662,plain,
    ( spl15_258
    | ~ spl15_261
    | ~ spl15_254 ),
    inference(avatar_split_clause,[],[f1634,f1621,f1660,f1654])).

fof(f1660,plain,
    ( spl15_261
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_261])])).

fof(f1634,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_254 ),
    inference(superposition,[],[f377,f1622])).

fof(f1643,plain,
    ( spl15_256
    | ~ spl15_254 ),
    inference(avatar_split_clause,[],[f1636,f1621,f1641])).

fof(f1641,plain,
    ( spl15_256
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_256])])).

fof(f1636,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_254 ),
    inference(superposition,[],[f140,f1622])).

fof(f1623,plain,
    ( spl15_254
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_252 ),
    inference(avatar_split_clause,[],[f1614,f1607,f401,f391,f1621])).

fof(f1607,plain,
    ( spl15_252
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_252])])).

fof(f1614,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_252 ),
    inference(forward_demodulation,[],[f1610,f402])).

fof(f1610,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_252 ),
    inference(resolution,[],[f1608,f395])).

fof(f1608,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl15_252 ),
    inference(avatar_component_clause,[],[f1607])).

fof(f1609,plain,
    ( spl15_248
    | spl15_250
    | spl15_252
    | ~ spl15_12
    | spl15_97 ),
    inference(avatar_split_clause,[],[f680,f625,f205,f1607,f1601,f1595])).

fof(f1595,plain,
    ( spl15_248
  <=> v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_248])])).

fof(f1601,plain,
    ( spl15_250
  <=> v1_xboole_0(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_250])])).

fof(f625,plain,
    ( spl15_97
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_97])])).

fof(f680,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | v1_xboole_0(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl15_12
    | ~ spl15_97 ),
    inference(subsumption_resolution,[],[f674,f626])).

fof(f626,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_97 ),
    inference(avatar_component_clause,[],[f625])).

fof(f674,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | v1_xboole_0(sK10(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl15_12 ),
    inference(resolution,[],[f487,f485])).

fof(f485,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(sK10(X1))
        | v1_xboole_0(X1) )
    | ~ spl15_12 ),
    inference(resolution,[],[f477,f142])).

fof(f477,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK10(X2)) )
    | ~ spl15_12 ),
    inference(resolution,[],[f473,f384])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl15_12 ),
    inference(resolution,[],[f383,f375])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl15_12 ),
    inference(resolution,[],[f154,f206])).

fof(f1585,plain,
    ( spl15_246
    | ~ spl15_4
    | ~ spl15_244 ),
    inference(avatar_split_clause,[],[f1577,f1571,f177,f1583])).

fof(f1583,plain,
    ( spl15_246
  <=> l1_orders_2(sK11(sK5,sK11(sK5,sK7(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_246])])).

fof(f1577,plain,
    ( l1_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ spl15_4
    | ~ spl15_244 ),
    inference(resolution,[],[f1572,f271])).

fof(f1573,plain,
    ( ~ spl15_31
    | spl15_244
    | spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_238 ),
    inference(avatar_split_clause,[],[f1541,f1531,f1496,f1225,f890,f859,f163,f1571,f280])).

fof(f1541,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1540,f164])).

fof(f1540,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1539,f1497])).

fof(f1539,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1538,f891])).

fof(f1538,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1537,f860])).

fof(f1537,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1534,f1226])).

fof(f1534,plain,
    ( l1_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))),sK5)
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_238 ),
    inference(resolution,[],[f1532,f148])).

fof(f1566,plain,
    ( ~ spl15_31
    | spl15_242
    | spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_238 ),
    inference(avatar_split_clause,[],[f1551,f1531,f1496,f1225,f890,f859,f163,f1564,f280])).

fof(f1551,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1550,f164])).

fof(f1550,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1549,f1497])).

fof(f1549,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1548,f891])).

fof(f1548,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1547,f860])).

fof(f1547,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1536,f1226])).

fof(f1536,plain,
    ( v4_orders_2(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_238 ),
    inference(resolution,[],[f1532,f146])).

fof(f1558,plain,
    ( ~ spl15_31
    | spl15_240
    | spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | spl15_233
    | ~ spl15_238 ),
    inference(avatar_split_clause,[],[f1546,f1531,f1496,f1225,f890,f859,f163,f1556,f280])).

fof(f1546,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1545,f164])).

fof(f1545,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_233
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1544,f1497])).

fof(f1544,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_122
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1543,f891])).

fof(f1543,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_118
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1542,f860])).

fof(f1542,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_190
    | ~ spl15_238 ),
    inference(subsumption_resolution,[],[f1535,f1226])).

fof(f1535,plain,
    ( v7_waybel_0(sK11(sK5,sK11(sK5,sK7(sK5))))
    | ~ l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
    | v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_238 ),
    inference(resolution,[],[f1532,f147])).

fof(f1533,plain,
    ( spl15_238
    | ~ spl15_31
    | spl15_1
    | ~ spl15_190
    | ~ spl15_234 ),
    inference(avatar_split_clause,[],[f1526,f1502,f1225,f163,f280,f1531])).

fof(f1502,plain,
    ( spl15_234
  <=> ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK7(sK5)),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK7(sK5))),X0,sK11(sK5,sK7(sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_234])])).

fof(f1526,plain,
    ( ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,sK11(sK5,sK7(sK5)))
    | ~ spl15_1
    | ~ spl15_190
    | ~ spl15_234 ),
    inference(subsumption_resolution,[],[f1524,f164])).

fof(f1524,plain,
    ( v2_struct_0(sK5)
    | ~ l1_struct_0(sK5)
    | m2_yellow_6(sK11(sK5,sK11(sK5,sK7(sK5))),sK5,sK11(sK5,sK7(sK5)))
    | ~ spl15_190
    | ~ spl15_234 ),
    inference(resolution,[],[f1503,f1226])).

fof(f1503,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK7(sK5)),X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK7(sK5))),X0,sK11(sK5,sK7(sK5))) )
    | ~ spl15_234 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f1522,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_1
    | ~ spl15_108
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(avatar_split_clause,[],[f1514,f1499,f838,f794,f163,f853,f847,f835,f280])).

fof(f1499,plain,
    ( spl15_232
  <=> v2_struct_0(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_232])])).

fof(f1514,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_108
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1513,f164])).

fof(f1513,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_108
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1507,f839])).

fof(f1507,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_108
    | ~ spl15_232 ),
    inference(resolution,[],[f1505,f795])).

fof(f1505,plain,
    ( ! [X0,X1] :
        ( ~ m2_yellow_6(sK11(sK5,sK7(sK5)),X0,X1)
        | ~ l1_waybel_0(X1,X0)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_232 ),
    inference(resolution,[],[f1500,f145])).

fof(f1500,plain,
    ( v2_struct_0(sK11(sK5,sK7(sK5)))
    | ~ spl15_232 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1521,plain,
    ( ~ spl15_237
    | spl15_110
    | ~ spl15_115
    | ~ spl15_117
    | spl15_1
    | spl15_37
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(avatar_split_clause,[],[f1512,f1499,f838,f310,f163,f853,f847,f835,f1519])).

fof(f1519,plain,
    ( spl15_237
  <=> ~ l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_237])])).

fof(f1512,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_orders_2(sK5)
    | ~ spl15_1
    | ~ spl15_37
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1511,f119])).

fof(f119,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_l1_orders_2)).

fof(f1511,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ l1_orders_2(sK5)
    | ~ spl15_1
    | ~ spl15_37
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1510,f311])).

fof(f1510,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | sP1(sK5)
    | ~ l1_orders_2(sK5)
    | ~ spl15_1
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1509,f164])).

fof(f1509,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | sP1(sK5)
    | ~ l1_orders_2(sK5)
    | ~ spl15_112
    | ~ spl15_232 ),
    inference(subsumption_resolution,[],[f1508,f839])).

fof(f1508,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | sP1(sK5)
    | ~ l1_orders_2(sK5)
    | ~ spl15_232 ),
    inference(duplicate_literal_removal,[],[f1506])).

fof(f1506,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | v2_struct_0(sK5)
    | sP1(sK5)
    | ~ l1_orders_2(sK5)
    | ~ spl15_232 ),
    inference(resolution,[],[f1505,f785])).

fof(f785,plain,(
    ! [X1] :
      ( m2_yellow_6(sK11(X1,sK7(X1)),X1,sK7(X1))
      | v2_struct_0(X1)
      | sP1(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f782,f119])).

fof(f1504,plain,
    ( spl15_232
    | spl15_234
    | ~ spl15_118
    | ~ spl15_122 ),
    inference(avatar_split_clause,[],[f935,f890,f859,f1502,f1499])).

fof(f935,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK7(sK5)),X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK7(sK5))),X0,sK11(sK5,sK7(sK5)))
        | v2_struct_0(sK11(sK5,sK7(sK5)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_118
    | ~ spl15_122 ),
    inference(subsumption_resolution,[],[f934,f891])).

fof(f934,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK11(sK5,sK7(sK5)),X0)
        | m2_yellow_6(sK11(X0,sK11(sK5,sK7(sK5))),X0,sK11(sK5,sK7(sK5)))
        | ~ v4_orders_2(sK11(sK5,sK7(sK5)))
        | v2_struct_0(sK11(sK5,sK7(sK5)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl15_118 ),
    inference(resolution,[],[f860,f149])).

fof(f1400,plain,
    ( ~ spl15_231
    | spl15_229 ),
    inference(avatar_split_clause,[],[f1393,f1390,f1398])).

fof(f1398,plain,
    ( spl15_231
  <=> ~ r2_hidden(u1_struct_0(sK13),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_231])])).

fof(f1390,plain,
    ( spl15_229
  <=> ~ m1_subset_1(u1_struct_0(sK13),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_229])])).

fof(f1393,plain,
    ( ~ r2_hidden(u1_struct_0(sK13),k1_xboole_0)
    | ~ spl15_229 ),
    inference(resolution,[],[f1391,f142])).

fof(f1391,plain,
    ( ~ m1_subset_1(u1_struct_0(sK13),k1_xboole_0)
    | ~ spl15_229 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f1392,plain,
    ( spl15_226
    | ~ spl15_229
    | ~ spl15_140
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1382,f1297,f964,f1390,f1384])).

fof(f1384,plain,
    ( spl15_226
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK13)
        | m1_subset_1(sK8(sK13,X0),u1_struct_0(sK5))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_226])])).

fof(f1297,plain,
    ( spl15_204
  <=> ! [X1] :
        ( ~ v7_waybel_0(X1)
        | r2_hidden(sK8(sK13,X1),u1_struct_0(sK13))
        | ~ l1_waybel_0(X1,sK13)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_204])])).

fof(f1382,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK13),k1_xboole_0)
        | ~ l1_waybel_0(X0,sK13)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | m1_subset_1(sK8(sK13,X0),u1_struct_0(sK5)) )
    | ~ spl15_140
    | ~ spl15_204 ),
    inference(superposition,[],[f1315,f965])).

fof(f1315,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(u1_struct_0(sK13),k1_zfmisc_1(X2))
        | ~ l1_waybel_0(X1,sK13)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1)
        | m1_subset_1(sK8(sK13,X1),X2) )
    | ~ spl15_204 ),
    inference(resolution,[],[f1298,f153])).

fof(f1298,plain,
    ( ! [X1] :
        ( r2_hidden(sK8(sK13,X1),u1_struct_0(sK13))
        | ~ v7_waybel_0(X1)
        | ~ l1_waybel_0(X1,sK13)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1) )
    | ~ spl15_204 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f1380,plain,
    ( spl15_146
    | spl15_224
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f884,f177,f170,f163,f1378,f1007])).

fof(f1378,plain,
    ( spl15_224
  <=> ! [X1] :
        ( ~ v7_waybel_0(X1)
        | r2_hidden(sK10(k10_yellow_6(sK5,X1)),u1_struct_0(sK5))
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | ~ l1_waybel_0(X1,sK5)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_224])])).

fof(f884,plain,
    ( ! [X1] :
        ( ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK5)
        | v1_xboole_0(k10_yellow_6(sK5,X1))
        | v1_xboole_0(u1_struct_0(sK5))
        | r2_hidden(sK10(k10_yellow_6(sK5,X1)),u1_struct_0(sK5)) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f869,f476])).

fof(f1375,plain,
    ( spl15_220
    | ~ spl15_47
    | spl15_222
    | ~ spl15_42 ),
    inference(avatar_split_clause,[],[f1345,f336,f1373,f349,f1370])).

fof(f1370,plain,
    ( spl15_220
  <=> v2_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_220])])).

fof(f349,plain,
    ( spl15_47
  <=> ~ l1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).

fof(f1373,plain,
    ( spl15_222
  <=> ! [X1] :
        ( ~ l1_waybel_0(X1,sK13)
        | l1_waybel_0(sK4(sK13,X1),sK13)
        | v2_struct_0(X1)
        | ~ v4_orders_2(X1)
        | ~ v7_waybel_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_222])])).

fof(f336,plain,
    ( spl15_42
  <=> sP0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f1345,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK13)
        | ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_struct_0(sK13)
        | v2_struct_0(sK13)
        | l1_waybel_0(sK4(sK13,X1),sK13) )
    | ~ spl15_42 ),
    inference(resolution,[],[f747,f337])).

fof(f337,plain,
    ( sP0(sK13)
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f336])).

fof(f747,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK4(X0,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f746])).

fof(f746,plain,(
    ! [X0,X1] :
      ( l1_waybel_0(sK4(X0,X1),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f148,f105])).

fof(f1364,plain,
    ( spl15_216
    | spl15_218
    | ~ spl15_10
    | ~ spl15_22 ),
    inference(avatar_split_clause,[],[f1347,f248,f198,f1362,f1359])).

fof(f1359,plain,
    ( spl15_216
  <=> v2_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_216])])).

fof(f1362,plain,
    ( spl15_218
  <=> ! [X0] :
        ( ~ l1_waybel_0(X0,sK14)
        | l1_waybel_0(sK4(sK14,X0),sK14)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_218])])).

fof(f198,plain,
    ( spl15_10
  <=> l1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f248,plain,
    ( spl15_22
  <=> sP0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_22])])).

fof(f1347,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK14)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK14)
        | l1_waybel_0(sK4(sK14,X0),sK14) )
    | ~ spl15_10
    | ~ spl15_22 ),
    inference(subsumption_resolution,[],[f1344,f199])).

fof(f199,plain,
    ( l1_struct_0(sK14)
    | ~ spl15_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1344,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK14)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(sK14)
        | v2_struct_0(sK14)
        | l1_waybel_0(sK4(sK14,X0),sK14) )
    | ~ spl15_22 ),
    inference(resolution,[],[f747,f249])).

fof(f249,plain,
    ( sP0(sK14)
    | ~ spl15_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f1352,plain,
    ( ~ spl15_31
    | spl15_214
    | spl15_1
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f1348,f225,f163,f1350,f280])).

fof(f1348,plain,
    ( ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(sK5)
        | l1_waybel_0(sK4(sK5,X2),sK5) )
    | ~ spl15_1
    | ~ spl15_18 ),
    inference(subsumption_resolution,[],[f1346,f164])).

fof(f1346,plain,
    ( ! [X2] :
        ( ~ l1_waybel_0(X2,sK5)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_struct_0(sK5)
        | v2_struct_0(sK5)
        | l1_waybel_0(sK4(sK5,X2),sK5) )
    | ~ spl15_18 ),
    inference(resolution,[],[f747,f226])).

fof(f1340,plain,
    ( ~ spl15_213
    | spl15_211 ),
    inference(avatar_split_clause,[],[f1333,f1330,f1338])).

fof(f1338,plain,
    ( spl15_213
  <=> ~ r2_hidden(u1_struct_0(sK13),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_213])])).

fof(f1330,plain,
    ( spl15_211
  <=> ~ m1_subset_1(u1_struct_0(sK13),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_211])])).

fof(f1333,plain,
    ( ~ r2_hidden(u1_struct_0(sK13),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_211 ),
    inference(resolution,[],[f1331,f142])).

fof(f1331,plain,
    ( ~ m1_subset_1(u1_struct_0(sK13),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_211 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f1332,plain,
    ( spl15_208
    | ~ spl15_211
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_204 ),
    inference(avatar_split_clause,[],[f1319,f1297,f401,f391,f1330,f1324])).

fof(f1324,plain,
    ( spl15_208
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_208])])).

fof(f1319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK13),k1_zfmisc_1(k1_xboole_0))
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK13)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) )
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_204 ),
    inference(forward_demodulation,[],[f1314,f402])).

fof(f1314,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK13)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ m1_subset_1(u1_struct_0(sK13),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl15_54
    | ~ spl15_204 ),
    inference(resolution,[],[f1298,f394])).

fof(f1313,plain,
    ( spl15_206
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_202 ),
    inference(avatar_split_clause,[],[f1304,f1294,f401,f391,f1311])).

fof(f1311,plain,
    ( spl15_206
  <=> k1_xboole_0 = u1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_206])])).

fof(f1294,plain,
    ( spl15_202
  <=> v1_xboole_0(u1_struct_0(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_202])])).

fof(f1304,plain,
    ( k1_xboole_0 = u1_struct_0(sK13)
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_202 ),
    inference(forward_demodulation,[],[f1300,f402])).

fof(f1300,plain,
    ( u1_struct_0(sK13) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_202 ),
    inference(resolution,[],[f1295,f395])).

fof(f1295,plain,
    ( v1_xboole_0(u1_struct_0(sK13))
    | ~ spl15_202 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1299,plain,
    ( spl15_202
    | spl15_204
    | ~ spl15_50 ),
    inference(avatar_split_clause,[],[f1253,f366,f1297,f1294])).

fof(f366,plain,
    ( spl15_50
  <=> sP1(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_50])])).

fof(f1253,plain,
    ( ! [X1] :
        ( ~ v7_waybel_0(X1)
        | ~ v4_orders_2(X1)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK13)
        | v1_xboole_0(u1_struct_0(sK13))
        | r2_hidden(sK8(sK13,X1),u1_struct_0(sK13)) )
    | ~ spl15_50 ),
    inference(resolution,[],[f711,f367])).

fof(f367,plain,
    ( sP1(sK13)
    | ~ spl15_50 ),
    inference(avatar_component_clause,[],[f366])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ~ sP1(X1)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X1)
      | v1_xboole_0(u1_struct_0(X1))
      | r2_hidden(sK8(X1,X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f126,f143])).

fof(f1277,plain,
    ( spl15_200
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_196 ),
    inference(avatar_split_clause,[],[f1268,f1258,f401,f391,f1275])).

fof(f1275,plain,
    ( spl15_200
  <=> k1_xboole_0 = u1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_200])])).

fof(f1258,plain,
    ( spl15_196
  <=> v1_xboole_0(u1_struct_0(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_196])])).

fof(f1268,plain,
    ( k1_xboole_0 = u1_struct_0(sK14)
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_196 ),
    inference(forward_demodulation,[],[f1264,f402])).

fof(f1264,plain,
    ( u1_struct_0(sK14) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_196 ),
    inference(resolution,[],[f1259,f395])).

fof(f1259,plain,
    ( v1_xboole_0(u1_struct_0(sK14))
    | ~ spl15_196 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f1263,plain,
    ( spl15_196
    | spl15_198
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f1252,f261,f1261,f1258])).

fof(f1261,plain,
    ( spl15_198
  <=> ! [X0] :
        ( ~ v7_waybel_0(X0)
        | r2_hidden(sK8(sK14,X0),u1_struct_0(sK14))
        | ~ l1_waybel_0(X0,sK14)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_198])])).

fof(f261,plain,
    ( spl15_26
  <=> sP1(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f1252,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK14)
        | v1_xboole_0(u1_struct_0(sK14))
        | r2_hidden(sK8(sK14,X0),u1_struct_0(sK14)) )
    | ~ spl15_26 ),
    inference(resolution,[],[f711,f262])).

fof(f262,plain,
    ( sP1(sK14)
    | ~ spl15_26 ),
    inference(avatar_component_clause,[],[f261])).

fof(f1243,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_127
    | ~ spl15_129
    | ~ spl15_131
    | spl15_194
    | spl15_1
    | ~ spl15_120 ),
    inference(avatar_split_clause,[],[f880,f874,f163,f1241,f915,f909,f903,f897,f280])).

fof(f880,plain,
    ( l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_120 ),
    inference(subsumption_resolution,[],[f877,f164])).

fof(f877,plain,
    ( l1_waybel_0(sK11(sK5,sK3(sK5)),sK5)
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_120 ),
    inference(resolution,[],[f875,f148])).

fof(f1236,plain,
    ( spl15_192
    | ~ spl15_4
    | ~ spl15_190 ),
    inference(avatar_split_clause,[],[f1228,f1225,f177,f1234])).

fof(f1234,plain,
    ( spl15_192
  <=> l1_orders_2(sK11(sK5,sK7(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_192])])).

fof(f1228,plain,
    ( l1_orders_2(sK11(sK5,sK7(sK5)))
    | ~ spl15_4
    | ~ spl15_190 ),
    inference(resolution,[],[f1226,f271])).

fof(f1227,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_113
    | ~ spl15_115
    | ~ spl15_117
    | spl15_190
    | spl15_1
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f800,f794,f163,f1225,f853,f847,f841,f835,f280])).

fof(f800,plain,
    ( l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_108 ),
    inference(subsumption_resolution,[],[f797,f164])).

fof(f797,plain,
    ( l1_waybel_0(sK11(sK5,sK7(sK5)),sK5)
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_108 ),
    inference(resolution,[],[f795,f148])).

fof(f1200,plain,
    ( spl15_176
    | spl15_188
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f1128,f1121,f1198,f1146])).

fof(f1146,plain,
    ( spl15_176
  <=> v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_176])])).

fof(f1198,plain,
    ( spl15_188
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_188])])).

fof(f1121,plain,
    ( spl15_172
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_172])])).

fof(f1128,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0))) )
    | ~ spl15_172 ),
    inference(superposition,[],[f473,f1122])).

fof(f1122,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_172 ),
    inference(avatar_component_clause,[],[f1121])).

fof(f1195,plain,
    ( spl15_142
    | ~ spl15_187
    | ~ spl15_140
    | ~ spl15_180 ),
    inference(avatar_split_clause,[],[f1187,f1159,f964,f1193,f993])).

fof(f1193,plain,
    ( spl15_187
  <=> ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_187])])).

fof(f1159,plain,
    ( spl15_180
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_180])])).

fof(f1187,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_180 ),
    inference(superposition,[],[f1165,f965])).

fof(f1165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_180 ),
    inference(resolution,[],[f1160,f153])).

fof(f1160,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_180 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f1185,plain,
    ( ~ spl15_185
    | spl15_183 ),
    inference(avatar_split_clause,[],[f1178,f1175,f1183])).

fof(f1183,plain,
    ( spl15_185
  <=> ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_185])])).

fof(f1175,plain,
    ( spl15_183
  <=> ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_183])])).

fof(f1178,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_183 ),
    inference(resolution,[],[f1176,f142])).

fof(f1176,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_183 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1177,plain,
    ( ~ spl15_183
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_180 ),
    inference(avatar_split_clause,[],[f1169,f1159,f401,f391,f1175])).

fof(f1169,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_180 ),
    inference(forward_demodulation,[],[f1164,f402])).

fof(f1164,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_180 ),
    inference(resolution,[],[f1160,f394])).

fof(f1170,plain,
    ( ~ spl15_177
    | ~ spl15_180 ),
    inference(avatar_split_clause,[],[f1168,f1159,f1143])).

fof(f1143,plain,
    ( spl15_177
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_177])])).

fof(f1168,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_180 ),
    inference(resolution,[],[f1160,f151])).

fof(f1161,plain,
    ( spl15_176
    | spl15_180
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f1130,f1121,f1159,f1146])).

fof(f1130,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_172 ),
    inference(superposition,[],[f375,f1122])).

fof(f1154,plain,
    ( spl15_176
    | ~ spl15_179
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f1129,f1121,f1152,f1146])).

fof(f1152,plain,
    ( spl15_179
  <=> ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_179])])).

fof(f1129,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_172 ),
    inference(superposition,[],[f377,f1122])).

fof(f1138,plain,
    ( spl15_174
    | ~ spl15_172 ),
    inference(avatar_split_clause,[],[f1131,f1121,f1136])).

fof(f1136,plain,
    ( spl15_174
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_174])])).

fof(f1131,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_172 ),
    inference(superposition,[],[f140,f1122])).

fof(f1123,plain,
    ( spl15_172
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_170 ),
    inference(avatar_split_clause,[],[f1111,f1104,f401,f391,f1121])).

fof(f1104,plain,
    ( spl15_170
  <=> v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_170])])).

fof(f1111,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_170 ),
    inference(forward_demodulation,[],[f1107,f402])).

fof(f1107,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl15_54
    | ~ spl15_170 ),
    inference(resolution,[],[f1105,f395])).

fof(f1105,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_xboole_0))))
    | ~ spl15_170 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f1106,plain,
    ( spl15_168
    | spl15_170
    | spl15_83
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f988,f964,f555,f1104,f1098])).

fof(f1098,plain,
    ( spl15_168
  <=> m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_168])])).

fof(f988,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_xboole_0))))
    | m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))),u1_struct_0(sK5))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f987,f965])).

fof(f987,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(subsumption_resolution,[],[f986,f556])).

fof(f986,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f979,f965])).

fof(f979,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))),u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(u1_struct_0(sK5))))))
    | ~ spl15_140 ),
    inference(superposition,[],[f700,f965])).

fof(f700,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(sK10(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f669,f140])).

fof(f1093,plain,
    ( spl15_146
    | spl15_166
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f974,f964,f1091,f1007])).

fof(f1091,plain,
    ( spl15_166
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | v1_xboole_0(X3)
        | r2_hidden(sK10(X3),u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_166])])).

fof(f974,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | v1_xboole_0(u1_struct_0(sK5))
        | r2_hidden(sK10(X3),u1_struct_0(sK5))
        | v1_xboole_0(X3) )
    | ~ spl15_140 ),
    inference(superposition,[],[f489,f965])).

fof(f489,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X4))
      | v1_xboole_0(X4)
      | r2_hidden(sK10(X3),X4)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f476,f142])).

fof(f1082,plain,
    ( spl15_146
    | spl15_164
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f971,f964,f1080,f1007])).

fof(f971,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_xboole_0)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK5))
        | r2_hidden(sK10(X1),u1_struct_0(sK5)) )
    | ~ spl15_140 ),
    inference(superposition,[],[f476,f965])).

fof(f1078,plain,
    ( spl15_158
    | ~ spl15_163
    | ~ spl15_140
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1048,f1013,f964,f1075,f1061])).

fof(f1061,plain,
    ( spl15_158
  <=> m1_subset_1(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_158])])).

fof(f1075,plain,
    ( spl15_163
  <=> ~ r2_hidden(u1_struct_0(sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_163])])).

fof(f1048,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k1_xboole_0)
    | m1_subset_1(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_148 ),
    inference(superposition,[],[f1046,f965])).

fof(f1046,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(X0))
        | m1_subset_1(sK10(sK10(k1_xboole_0)),X0) )
    | ~ spl15_148 ),
    inference(resolution,[],[f1017,f142])).

fof(f1017,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X0))
        | m1_subset_1(sK10(sK10(k1_xboole_0)),X0) )
    | ~ spl15_148 ),
    inference(resolution,[],[f1014,f153])).

fof(f1014,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | ~ spl15_148 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f1077,plain,
    ( ~ spl15_163
    | spl15_161 ),
    inference(avatar_split_clause,[],[f1070,f1067,f1075])).

fof(f1067,plain,
    ( spl15_161
  <=> ~ m1_subset_1(u1_struct_0(sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_161])])).

fof(f1070,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k1_xboole_0)
    | ~ spl15_161 ),
    inference(resolution,[],[f1068,f142])).

fof(f1068,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_xboole_0)
    | ~ spl15_161 ),
    inference(avatar_component_clause,[],[f1067])).

fof(f1069,plain,
    ( spl15_158
    | ~ spl15_161
    | ~ spl15_140
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1047,f1013,f964,f1067,f1061])).

fof(f1047,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_xboole_0)
    | m1_subset_1(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | ~ spl15_140
    | ~ spl15_148 ),
    inference(superposition,[],[f1017,f965])).

fof(f1055,plain,
    ( spl15_142
    | ~ spl15_157
    | ~ spl15_100
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f975,f964,f641,f1053,f993])).

fof(f1053,plain,
    ( spl15_157
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_157])])).

fof(f641,plain,
    ( spl15_100
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_100])])).

fof(f975,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_100
    | ~ spl15_140 ),
    inference(superposition,[],[f646,f965])).

fof(f646,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl15_100 ),
    inference(resolution,[],[f642,f153])).

fof(f642,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_100 ),
    inference(avatar_component_clause,[],[f641])).

fof(f1045,plain,
    ( spl15_146
    | ~ spl15_151
    | spl15_83
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f985,f964,f555,f1027,f1007])).

fof(f1027,plain,
    ( spl15_151
  <=> ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_151])])).

fof(f985,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_xboole_0)))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(subsumption_resolution,[],[f984,f556])).

fof(f984,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_xboole_0)))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f978,f965])).

fof(f978,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_xboole_0)))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK5))))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_140 ),
    inference(superposition,[],[f671,f965])).

fof(f671,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK10(sK10(k1_zfmisc_1(X4))))
      | v1_xboole_0(sK10(k1_zfmisc_1(X4)))
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f487,f141])).

fof(f1044,plain,
    ( ~ spl15_155
    | spl15_153 ),
    inference(avatar_split_clause,[],[f1037,f1034,f1042])).

fof(f1042,plain,
    ( spl15_155
  <=> ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_155])])).

fof(f1034,plain,
    ( spl15_153
  <=> ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_153])])).

fof(f1037,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_153 ),
    inference(resolution,[],[f1035,f142])).

fof(f1035,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_153 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1036,plain,
    ( ~ spl15_153
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1021,f1013,f401,f391,f1034])).

fof(f1021,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_148 ),
    inference(forward_demodulation,[],[f1016,f402])).

fof(f1016,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_148 ),
    inference(resolution,[],[f1014,f394])).

fof(f1029,plain,
    ( ~ spl15_151
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1019,f1013,f1027])).

fof(f1019,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK10(sK10(k1_xboole_0)))
    | ~ spl15_148 ),
    inference(resolution,[],[f1014,f141])).

fof(f1022,plain,
    ( ~ spl15_147
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1020,f1013,f1004])).

fof(f1020,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_148 ),
    inference(resolution,[],[f1014,f151])).

fof(f1015,plain,
    ( spl15_146
    | spl15_148
    | spl15_83
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f983,f964,f555,f1013,f1007])).

fof(f983,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_83
    | ~ spl15_140 ),
    inference(subsumption_resolution,[],[f982,f556])).

fof(f982,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ spl15_140 ),
    inference(forward_demodulation,[],[f972,f965])).

fof(f972,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(sK10(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl15_140 ),
    inference(superposition,[],[f487,f965])).

fof(f1001,plain,
    ( spl15_142
    | ~ spl15_145
    | ~ spl15_64
    | ~ spl15_140 ),
    inference(avatar_split_clause,[],[f969,f964,f437,f999,f993])).

fof(f999,plain,
    ( spl15_145
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_145])])).

fof(f437,plain,
    ( spl15_64
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f969,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,u1_struct_0(sK5))
    | ~ spl15_64
    | ~ spl15_140 ),
    inference(superposition,[],[f474,f965])).

fof(f474,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X2))
        | m1_subset_1(k1_xboole_0,X2) )
    | ~ spl15_64 ),
    inference(resolution,[],[f153,f438])).

fof(f438,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_64 ),
    inference(avatar_component_clause,[],[f437])).

fof(f966,plain,
    ( spl15_140
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_136 ),
    inference(avatar_split_clause,[],[f957,f947,f401,f391,f964])).

fof(f947,plain,
    ( spl15_136
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_136])])).

fof(f957,plain,
    ( k1_xboole_0 = k1_zfmisc_1(u1_struct_0(sK5))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_136 ),
    inference(forward_demodulation,[],[f953,f402])).

fof(f953,plain,
    ( k1_zfmisc_1(u1_struct_0(sK5)) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_136 ),
    inference(resolution,[],[f948,f395])).

fof(f948,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl15_136 ),
    inference(avatar_component_clause,[],[f947])).

fof(f952,plain,
    ( spl15_136
    | spl15_138
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f885,f177,f170,f163,f950,f947])).

fof(f950,plain,
    ( spl15_138
  <=> ! [X2] :
        ( ~ v7_waybel_0(X2)
        | r2_hidden(k10_yellow_6(sK5,X2),k1_zfmisc_1(u1_struct_0(sK5)))
        | ~ l1_waybel_0(X2,sK5)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_138])])).

fof(f885,plain,
    ( ! [X2] :
        ( ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK5)
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
        | r2_hidden(k10_yellow_6(sK5,X2),k1_zfmisc_1(u1_struct_0(sK5))) )
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(resolution,[],[f869,f143])).

fof(f942,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_127
    | ~ spl15_129
    | ~ spl15_131
    | spl15_134
    | spl15_1
    | ~ spl15_120 ),
    inference(avatar_split_clause,[],[f882,f874,f163,f940,f915,f909,f903,f897,f280])).

fof(f882,plain,
    ( v4_orders_2(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_120 ),
    inference(subsumption_resolution,[],[f879,f164])).

fof(f879,plain,
    ( v4_orders_2(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_120 ),
    inference(resolution,[],[f875,f146])).

fof(f933,plain,
    ( spl15_37
    | spl15_115 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_115 ),
    inference(subsumption_resolution,[],[f931,f311])).

fof(f931,plain,
    ( sP1(sK5)
    | ~ spl15_115 ),
    inference(resolution,[],[f848,f130])).

fof(f848,plain,
    ( ~ v7_waybel_0(sK7(sK5))
    | ~ spl15_115 ),
    inference(avatar_component_clause,[],[f847])).

fof(f930,plain,
    ( spl15_37
    | spl15_117 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_117 ),
    inference(subsumption_resolution,[],[f928,f311])).

fof(f928,plain,
    ( sP1(sK5)
    | ~ spl15_117 ),
    inference(resolution,[],[f854,f131])).

fof(f854,plain,
    ( ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ spl15_117 ),
    inference(avatar_component_clause,[],[f853])).

fof(f927,plain,
    ( spl15_18
    | spl15_127 ),
    inference(avatar_split_clause,[],[f924,f903,f225])).

fof(f926,plain,
    ( spl15_19
    | spl15_127 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl15_19
    | ~ spl15_127 ),
    inference(subsumption_resolution,[],[f924,f223])).

fof(f923,plain,
    ( ~ spl15_31
    | spl15_124
    | ~ spl15_127
    | ~ spl15_129
    | ~ spl15_131
    | spl15_132
    | spl15_1
    | ~ spl15_120 ),
    inference(avatar_split_clause,[],[f881,f874,f163,f921,f915,f909,f903,f897,f280])).

fof(f881,plain,
    ( v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_120 ),
    inference(subsumption_resolution,[],[f878,f164])).

fof(f878,plain,
    ( v7_waybel_0(sK11(sK5,sK3(sK5)))
    | ~ l1_waybel_0(sK3(sK5),sK5)
    | ~ v7_waybel_0(sK3(sK5))
    | ~ v4_orders_2(sK3(sK5))
    | v2_struct_0(sK3(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_120 ),
    inference(resolution,[],[f875,f147])).

fof(f892,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_113
    | ~ spl15_115
    | ~ spl15_117
    | spl15_122
    | spl15_1
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f802,f794,f163,f890,f853,f847,f841,f835,f280])).

fof(f802,plain,
    ( v4_orders_2(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_108 ),
    inference(subsumption_resolution,[],[f799,f164])).

fof(f799,plain,
    ( v4_orders_2(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_108 ),
    inference(resolution,[],[f795,f146])).

fof(f876,plain,
    ( spl15_120
    | spl15_18
    | spl15_1
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f865,f177,f163,f225,f874])).

fof(f865,plain,
    ( sP0(sK5)
    | m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,sK3(sK5))
    | ~ spl15_1
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f751,f164])).

fof(f751,plain,
    ( v2_struct_0(sK5)
    | sP0(sK5)
    | m2_yellow_6(sK11(sK5,sK3(sK5)),sK5,sK3(sK5))
    | ~ spl15_4 ),
    inference(resolution,[],[f749,f178])).

fof(f749,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | sP0(X0)
      | m2_yellow_6(sK11(X0,sK3(X0)),X0,sK3(X0)) ) ),
    inference(resolution,[],[f745,f121])).

fof(f745,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m2_yellow_6(sK11(X0,sK3(X0)),X0,sK3(X0))
      | v2_struct_0(X0)
      | sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,(
    ! [X0] :
      ( m2_yellow_6(sK11(X0,sK3(X0)),X0,sK3(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | sP0(X0)
      | sP0(X0) ) ),
    inference(resolution,[],[f741,f110])).

fof(f741,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK3(X0),X1)
      | m2_yellow_6(sK11(X1,sK3(X0)),X1,sK3(X0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f740,f107])).

fof(f740,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK3(X0),X1)
      | m2_yellow_6(sK11(X1,sK3(X0)),X1,sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | sP0(X0) ) ),
    inference(subsumption_resolution,[],[f738,f108])).

fof(f738,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK3(X0),X1)
      | m2_yellow_6(sK11(X1,sK3(X0)),X1,sK3(X0))
      | ~ v4_orders_2(sK3(X0))
      | v2_struct_0(sK3(X0))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | sP0(X0) ) ),
    inference(resolution,[],[f149,f109])).

fof(f866,plain,
    ( spl15_36
    | spl15_113 ),
    inference(avatar_split_clause,[],[f862,f841,f307])).

fof(f864,plain,
    ( spl15_37
    | spl15_113 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | ~ spl15_37
    | ~ spl15_113 ),
    inference(subsumption_resolution,[],[f862,f311])).

fof(f861,plain,
    ( ~ spl15_31
    | spl15_110
    | ~ spl15_113
    | ~ spl15_115
    | ~ spl15_117
    | spl15_118
    | spl15_1
    | ~ spl15_108 ),
    inference(avatar_split_clause,[],[f801,f794,f163,f859,f853,f847,f841,f835,f280])).

fof(f801,plain,
    ( v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_1
    | ~ spl15_108 ),
    inference(subsumption_resolution,[],[f798,f164])).

fof(f798,plain,
    ( v7_waybel_0(sK11(sK5,sK7(sK5)))
    | ~ l1_waybel_0(sK7(sK5),sK5)
    | ~ v7_waybel_0(sK7(sK5))
    | ~ v4_orders_2(sK7(sK5))
    | v2_struct_0(sK7(sK5))
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_108 ),
    inference(resolution,[],[f795,f147])).

fof(f796,plain,
    ( spl15_108
    | spl15_1
    | ~ spl15_4
    | spl15_37 ),
    inference(avatar_split_clause,[],[f789,f310,f177,f163,f794])).

fof(f789,plain,
    ( m2_yellow_6(sK11(sK5,sK7(sK5)),sK5,sK7(sK5))
    | ~ spl15_1
    | ~ spl15_4
    | ~ spl15_37 ),
    inference(subsumption_resolution,[],[f788,f311])).

fof(f696,plain,
    ( spl15_96
    | spl15_106
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f605,f530,f694,f628])).

fof(f628,plain,
    ( spl15_96
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f694,plain,
    ( spl15_106
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_106])])).

fof(f530,plain,
    ( spl15_78
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_78])])).

fof(f605,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl15_78 ),
    inference(superposition,[],[f473,f531])).

fof(f531,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_78 ),
    inference(avatar_component_clause,[],[f530])).

fof(f692,plain,
    ( spl15_90
    | spl15_74
    | ~ spl15_80 ),
    inference(avatar_split_clause,[],[f578,f545,f502,f595])).

fof(f595,plain,
    ( spl15_90
  <=> r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_90])])).

fof(f502,plain,
    ( spl15_74
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f545,plain,
    ( spl15_80
  <=> m1_subset_1(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_80])])).

fof(f578,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_80 ),
    inference(resolution,[],[f546,f143])).

fof(f546,plain,
    ( m1_subset_1(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_80 ),
    inference(avatar_component_clause,[],[f545])).

fof(f666,plain,
    ( ~ spl15_105
    | spl15_103 ),
    inference(avatar_split_clause,[],[f659,f656,f664])).

fof(f664,plain,
    ( spl15_105
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_105])])).

fof(f656,plain,
    ( spl15_103
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_103])])).

fof(f659,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_103 ),
    inference(resolution,[],[f657,f142])).

fof(f657,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_103 ),
    inference(avatar_component_clause,[],[f656])).

fof(f658,plain,
    ( ~ spl15_103
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_100 ),
    inference(avatar_split_clause,[],[f650,f641,f401,f391,f656])).

fof(f650,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_100 ),
    inference(forward_demodulation,[],[f645,f402])).

fof(f645,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_100 ),
    inference(resolution,[],[f642,f394])).

fof(f651,plain,
    ( ~ spl15_97
    | ~ spl15_100 ),
    inference(avatar_split_clause,[],[f649,f641,f625])).

fof(f649,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_100 ),
    inference(resolution,[],[f642,f151])).

fof(f643,plain,
    ( spl15_100
    | spl15_96
    | ~ spl15_86 ),
    inference(avatar_split_clause,[],[f602,f574,f628,f641])).

fof(f574,plain,
    ( spl15_86
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_86])])).

fof(f602,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_86 ),
    inference(resolution,[],[f575,f143])).

fof(f575,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_86 ),
    inference(avatar_component_clause,[],[f574])).

fof(f636,plain,
    ( spl15_96
    | ~ spl15_99
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f606,f530,f634,f628])).

fof(f634,plain,
    ( spl15_99
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_99])])).

fof(f606,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_78 ),
    inference(superposition,[],[f377,f531])).

fof(f622,plain,
    ( spl15_94
    | ~ spl15_78
    | ~ spl15_80 ),
    inference(avatar_split_clause,[],[f604,f545,f530,f620])).

fof(f620,plain,
    ( spl15_94
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_94])])).

fof(f604,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl15_78
    | ~ spl15_80 ),
    inference(superposition,[],[f546,f531])).

fof(f615,plain,
    ( ~ spl15_93
    | ~ spl15_78
    | spl15_89 ),
    inference(avatar_split_clause,[],[f603,f588,f530,f613])).

fof(f613,plain,
    ( spl15_93
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_93])])).

fof(f588,plain,
    ( spl15_89
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_89])])).

fof(f603,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl15_78
    | ~ spl15_89 ),
    inference(superposition,[],[f589,f531])).

fof(f589,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl15_89 ),
    inference(avatar_component_clause,[],[f588])).

fof(f597,plain,
    ( spl15_90
    | spl15_75
    | ~ spl15_76 ),
    inference(avatar_split_clause,[],[f540,f516,f499,f595])).

fof(f499,plain,
    ( spl15_75
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_75])])).

fof(f516,plain,
    ( spl15_76
  <=> k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).

fof(f540,plain,
    ( r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_75
    | ~ spl15_76 ),
    inference(subsumption_resolution,[],[f536,f500])).

fof(f500,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_75 ),
    inference(avatar_component_clause,[],[f499])).

fof(f536,plain,
    ( r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_76 ),
    inference(superposition,[],[f375,f517])).

fof(f517,plain,
    ( k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_76 ),
    inference(avatar_component_clause,[],[f516])).

fof(f590,plain,
    ( ~ spl15_89
    | spl15_75
    | ~ spl15_76 ),
    inference(avatar_split_clause,[],[f539,f516,f499,f588])).

fof(f539,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl15_75
    | ~ spl15_76 ),
    inference(subsumption_resolution,[],[f535,f500])).

fof(f535,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_76 ),
    inference(superposition,[],[f377,f517])).

fof(f576,plain,
    ( spl15_86
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f569,f530,f574])).

fof(f569,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_78 ),
    inference(superposition,[],[f140,f531])).

fof(f565,plain,
    ( ~ spl15_85
    | spl15_77
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f548,f530,f513,f563])).

fof(f563,plain,
    ( spl15_85
  <=> k1_xboole_0 != sK10(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_85])])).

fof(f513,plain,
    ( spl15_77
  <=> k1_xboole_0 != sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_77])])).

fof(f548,plain,
    ( k1_xboole_0 != sK10(k1_xboole_0)
    | ~ spl15_77
    | ~ spl15_78 ),
    inference(forward_demodulation,[],[f514,f531])).

fof(f514,plain,
    ( k1_xboole_0 != sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_77 ),
    inference(avatar_component_clause,[],[f513])).

fof(f557,plain,
    ( ~ spl15_83
    | spl15_73
    | ~ spl15_78 ),
    inference(avatar_split_clause,[],[f550,f530,f493,f555])).

fof(f493,plain,
    ( spl15_73
  <=> ~ v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_73])])).

fof(f550,plain,
    ( ~ v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl15_73
    | ~ spl15_78 ),
    inference(forward_demodulation,[],[f494,f531])).

fof(f494,plain,
    ( ~ v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl15_73 ),
    inference(avatar_component_clause,[],[f493])).

fof(f547,plain,
    ( spl15_80
    | ~ spl15_76 ),
    inference(avatar_split_clause,[],[f537,f516,f545])).

fof(f537,plain,
    ( m1_subset_1(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_76 ),
    inference(superposition,[],[f140,f517])).

fof(f532,plain,
    ( spl15_78
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_74 ),
    inference(avatar_split_clause,[],[f523,f502,f401,f391,f530])).

fof(f523,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_74 ),
    inference(forward_demodulation,[],[f519,f402])).

fof(f519,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_54
    | ~ spl15_74 ),
    inference(resolution,[],[f503,f395])).

fof(f503,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_74 ),
    inference(avatar_component_clause,[],[f502])).

fof(f518,plain,
    ( spl15_76
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_72 ),
    inference(avatar_split_clause,[],[f509,f496,f401,f391,f516])).

fof(f496,plain,
    ( spl15_72
  <=> v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f509,plain,
    ( k1_xboole_0 = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_72 ),
    inference(forward_demodulation,[],[f505,f402])).

fof(f505,plain,
    ( sK10(k1_zfmisc_1(k1_xboole_0)) = sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl15_54
    | ~ spl15_72 ),
    inference(resolution,[],[f497,f395])).

fof(f497,plain,
    ( v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f496])).

fof(f504,plain,
    ( spl15_72
    | spl15_74
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f483,f205,f502,f496])).

fof(f483,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK10(sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl15_12 ),
    inference(resolution,[],[f477,f140])).

fof(f472,plain,
    ( ~ spl15_71
    | spl15_69 ),
    inference(avatar_split_clause,[],[f465,f462,f470])).

fof(f470,plain,
    ( spl15_71
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_71])])).

fof(f462,plain,
    ( spl15_69
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_69])])).

fof(f465,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_69 ),
    inference(resolution,[],[f463,f142])).

fof(f463,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_69 ),
    inference(avatar_component_clause,[],[f462])).

fof(f464,plain,
    ( ~ spl15_69
    | ~ spl15_12
    | ~ spl15_64 ),
    inference(avatar_split_clause,[],[f455,f437,f205,f462])).

fof(f455,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_12
    | ~ spl15_64 ),
    inference(resolution,[],[f438,f383])).

fof(f453,plain,
    ( spl15_66
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_60 ),
    inference(avatar_split_clause,[],[f444,f424,f401,f391,f451])).

fof(f451,plain,
    ( spl15_66
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).

fof(f424,plain,
    ( spl15_60
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_60])])).

fof(f444,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl15_54
    | ~ spl15_56
    | ~ spl15_60 ),
    inference(forward_demodulation,[],[f440,f402])).

fof(f440,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54
    | ~ spl15_60 ),
    inference(resolution,[],[f425,f395])).

fof(f425,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_60 ),
    inference(avatar_component_clause,[],[f424])).

fof(f439,plain,
    ( spl15_60
    | spl15_64
    | ~ spl15_56 ),
    inference(avatar_split_clause,[],[f406,f401,f437,f424])).

fof(f406,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_56 ),
    inference(superposition,[],[f375,f402])).

fof(f432,plain,
    ( spl15_60
    | ~ spl15_63
    | ~ spl15_56 ),
    inference(avatar_split_clause,[],[f405,f401,f430,f424])).

fof(f430,plain,
    ( spl15_63
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_63])])).

fof(f405,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_56 ),
    inference(superposition,[],[f377,f402])).

fof(f414,plain,
    ( spl15_58
    | ~ spl15_56 ),
    inference(avatar_split_clause,[],[f407,f401,f412])).

fof(f412,plain,
    ( spl15_58
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_58])])).

fof(f407,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_56 ),
    inference(superposition,[],[f140,f402])).

fof(f403,plain,
    ( spl15_56
    | ~ spl15_54 ),
    inference(avatar_split_clause,[],[f396,f391,f401])).

fof(f396,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl15_54 ),
    inference(resolution,[],[f392,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t6_boole)).

fof(f393,plain,
    ( spl15_54
    | ~ spl15_12 ),
    inference(avatar_split_clause,[],[f385,f205,f391])).

fof(f385,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl15_12 ),
    inference(resolution,[],[f384,f140])).

fof(f374,plain,
    ( spl15_50
    | spl15_52
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f331,f191,f372,f366])).

fof(f372,plain,
    ( spl15_52
  <=> l1_orders_2(sK7(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f191,plain,
    ( spl15_8
  <=> l1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f331,plain,
    ( l1_orders_2(sK7(sK13))
    | sP1(sK13)
    | ~ spl15_8 ),
    inference(resolution,[],[f272,f131])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(X1,sK13)
        | l1_orders_2(X1) )
    | ~ spl15_8 ),
    inference(resolution,[],[f231,f192])).

fof(f192,plain,
    ( l1_pre_topc(sK13)
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f191])).

fof(f361,plain,
    ( ~ spl15_8
    | spl15_47 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl15_8
    | ~ spl15_47 ),
    inference(subsumption_resolution,[],[f358,f192])).

fof(f358,plain,
    ( ~ l1_pre_topc(sK13)
    | ~ spl15_47 ),
    inference(resolution,[],[f350,f121])).

fof(f350,plain,
    ( ~ l1_struct_0(sK13)
    | ~ spl15_47 ),
    inference(avatar_component_clause,[],[f349])).

fof(f357,plain,
    ( ~ spl15_47
    | spl15_48
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f330,f191,f355,f349])).

fof(f355,plain,
    ( spl15_48
  <=> l1_orders_2(sK6(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_48])])).

fof(f330,plain,
    ( l1_orders_2(sK6(sK13))
    | ~ l1_struct_0(sK13)
    | ~ spl15_8 ),
    inference(resolution,[],[f272,f123])).

fof(f123,plain,(
    ! [X0] :
      ( l1_waybel_0(sK6(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_waybel_0(sK6(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_l1_waybel_0)).

fof(f344,plain,
    ( spl15_42
    | spl15_44
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f329,f191,f342,f336])).

fof(f342,plain,
    ( spl15_44
  <=> l1_orders_2(sK3(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f329,plain,
    ( l1_orders_2(sK3(sK13))
    | sP0(sK13)
    | ~ spl15_8 ),
    inference(resolution,[],[f272,f110])).

fof(f328,plain,
    ( spl15_18
    | spl15_40
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f273,f177,f326,f225])).

fof(f326,plain,
    ( spl15_40
  <=> l1_orders_2(sK3(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f273,plain,
    ( l1_orders_2(sK3(sK5))
    | sP0(sK5)
    | ~ spl15_4 ),
    inference(resolution,[],[f271,f110])).

fof(f321,plain,
    ( spl15_36
    | ~ spl15_17
    | ~ spl15_34 ),
    inference(avatar_split_clause,[],[f304,f300,f216,f307])).

fof(f216,plain,
    ( spl15_17
  <=> ~ v1_compts_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_17])])).

fof(f300,plain,
    ( spl15_34
  <=> sP2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f304,plain,
    ( ~ v1_compts_1(sK5)
    | sP1(sK5)
    | ~ spl15_34 ),
    inference(resolution,[],[f301,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v1_compts_1(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v1_compts_1(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f301,plain,
    ( sP2(sK5)
    | ~ spl15_34 ),
    inference(avatar_component_clause,[],[f300])).

fof(f320,plain,
    ( spl15_16
    | ~ spl15_37
    | ~ spl15_34 ),
    inference(avatar_split_clause,[],[f303,f300,f310,f219])).

fof(f219,plain,
    ( spl15_16
  <=> v1_compts_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f303,plain,
    ( ~ sP1(sK5)
    | v1_compts_1(sK5)
    | ~ spl15_34 ),
    inference(resolution,[],[f301,f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ sP1(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f319,plain,
    ( spl15_36
    | spl15_38
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f275,f177,f317,f307])).

fof(f317,plain,
    ( spl15_38
  <=> l1_orders_2(sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_38])])).

fof(f275,plain,
    ( l1_orders_2(sK7(sK5))
    | sP1(sK5)
    | ~ spl15_4 ),
    inference(resolution,[],[f271,f131])).

fof(f312,plain,
    ( ~ spl15_37
    | spl15_17
    | ~ spl15_34 ),
    inference(avatar_split_clause,[],[f305,f300,f216,f310])).

fof(f305,plain,
    ( ~ sP1(sK5)
    | ~ spl15_17
    | ~ spl15_34 ),
    inference(subsumption_resolution,[],[f303,f217])).

fof(f217,plain,
    ( ~ v1_compts_1(sK5)
    | ~ spl15_17 ),
    inference(avatar_component_clause,[],[f216])).

fof(f302,plain,
    ( spl15_34
    | spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f295,f177,f170,f163,f300])).

fof(f295,plain,
    ( sP2(sK5)
    | ~ spl15_1
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f294,f164])).

fof(f294,plain,
    ( sP2(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_2
    | ~ spl15_4 ),
    inference(subsumption_resolution,[],[f293,f178])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK5)
    | sP2(sK5)
    | v2_struct_0(sK5)
    | ~ spl15_2 ),
    inference(resolution,[],[f133,f171])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f44,f73,f72])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t35_yellow19)).

fof(f292,plain,
    ( ~ spl15_4
    | spl15_31 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl15_4
    | ~ spl15_31 ),
    inference(subsumption_resolution,[],[f289,f178])).

fof(f289,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ spl15_31 ),
    inference(resolution,[],[f281,f121])).

fof(f281,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl15_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f288,plain,
    ( ~ spl15_31
    | spl15_32
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f274,f177,f286,f280])).

fof(f286,plain,
    ( spl15_32
  <=> l1_orders_2(sK6(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f274,plain,
    ( l1_orders_2(sK6(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl15_4 ),
    inference(resolution,[],[f271,f123])).

fof(f269,plain,
    ( spl15_26
    | spl15_28
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f235,f198,f267,f261])).

fof(f267,plain,
    ( spl15_28
  <=> l1_orders_2(sK7(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f235,plain,
    ( l1_orders_2(sK7(sK14))
    | sP1(sK14)
    | ~ spl15_10 ),
    inference(resolution,[],[f230,f131])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK14)
        | l1_orders_2(X0) )
    | ~ spl15_10 ),
    inference(resolution,[],[f122,f199])).

fof(f256,plain,
    ( spl15_22
    | spl15_24
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f233,f198,f254,f248])).

fof(f254,plain,
    ( spl15_24
  <=> l1_orders_2(sK3(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_24])])).

fof(f233,plain,
    ( l1_orders_2(sK3(sK14))
    | sP0(sK14)
    | ~ spl15_10 ),
    inference(resolution,[],[f230,f110])).

fof(f243,plain,
    ( spl15_20
    | ~ spl15_10 ),
    inference(avatar_split_clause,[],[f236,f198,f241])).

fof(f241,plain,
    ( spl15_20
  <=> l1_orders_2(sK6(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f236,plain,
    ( l1_orders_2(sK6(sK14))
    | ~ spl15_10 ),
    inference(subsumption_resolution,[],[f234,f199])).

fof(f234,plain,
    ( l1_orders_2(sK6(sK14))
    | ~ l1_struct_0(sK14)
    | ~ spl15_10 ),
    inference(resolution,[],[f230,f123])).

fof(f228,plain,
    ( ~ spl15_17
    | ~ spl15_19 ),
    inference(avatar_split_clause,[],[f116,f222,f216])).

fof(f116,plain,
    ( ~ sP0(sK5)
    | ~ v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ( ~ sP0(sK5)
      | ~ v1_compts_1(sK5) )
    & ( sP0(sK5)
      | v1_compts_1(sK5) )
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f81,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ( ~ sP0(X0)
          | ~ v1_compts_1(X0) )
        & ( sP0(X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ sP0(sK5)
        | ~ v1_compts_1(sK5) )
      & ( sP0(sK5)
        | v1_compts_1(sK5) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ? [X0] :
      ( ( ~ sP0(X0)
        | ~ v1_compts_1(X0) )
      & ( sP0(X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> sP0(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f70])).

fof(f37,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',t37_yellow19)).

fof(f227,plain,
    ( spl15_16
    | spl15_18 ),
    inference(avatar_split_clause,[],[f115,f225,f219])).

fof(f115,plain,
    ( sP0(sK5)
    | v1_compts_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f214,plain,(
    spl15_14 ),
    inference(avatar_split_clause,[],[f118,f212])).

fof(f212,plain,
    ( spl15_14
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f118,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',d2_xboole_0)).

fof(f207,plain,(
    spl15_12 ),
    inference(avatar_split_clause,[],[f158,f205])).

fof(f158,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f117,f118])).

fof(f117,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',dt_o_0_0_xboole_0)).

fof(f200,plain,(
    spl15_10 ),
    inference(avatar_split_clause,[],[f157,f198])).

fof(f157,plain,(
    l1_struct_0(sK14) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    l1_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f20,f103])).

fof(f103,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK14) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_l1_struct_0)).

fof(f193,plain,(
    spl15_8 ),
    inference(avatar_split_clause,[],[f156,f191])).

fof(f156,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    l1_pre_topc(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f19,f101])).

fof(f101,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK13) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_l1_pre_topc)).

fof(f186,plain,(
    spl15_6 ),
    inference(avatar_split_clause,[],[f155,f184])).

fof(f184,plain,
    ( spl15_6
  <=> l1_orders_2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f155,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    l1_orders_2(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f18,f99])).

fof(f99,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK12) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t37_yellow19.p',existence_l1_orders_2)).

fof(f179,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f114,f177])).

fof(f114,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f172,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f113,f170])).

fof(f113,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

fof(f165,plain,(
    ~ spl15_1 ),
    inference(avatar_split_clause,[],[f112,f163])).

fof(f112,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t8_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:02 EDT 2019

% Result     : Theorem 2.10s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       : 3100 (13434 expanded)
%              Number of leaves         :  812 (5831 expanded)
%              Depth                    :   16
%              Number of atoms          : 9280 (38736 expanded)
%              Number of equality atoms :  121 (2327 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12842,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f149,f156,f163,f170,f177,f184,f191,f199,f209,f222,f229,f236,f248,f256,f264,f274,f282,f296,f303,f310,f319,f327,f334,f341,f349,f357,f364,f372,f380,f381,f389,f397,f412,f421,f429,f439,f446,f462,f469,f478,f488,f509,f516,f523,f530,f546,f554,f569,f580,f590,f598,f605,f612,f619,f628,f635,f642,f649,f656,f665,f672,f683,f694,f702,f717,f726,f734,f749,f758,f768,f779,f788,f804,f813,f835,f849,f857,f864,f871,f878,f885,f892,f905,f928,f936,f949,f972,f980,f987,f1007,f1014,f1045,f1052,f1059,f1069,f1076,f1083,f1090,f1160,f1185,f1194,f1216,f1294,f1302,f1339,f1352,f1378,f1391,f1398,f1429,f1437,f1444,f1462,f1576,f1589,f1596,f1648,f1662,f1678,f1698,f1709,f1723,f1737,f1745,f1781,f1845,f1907,f1919,f1926,f1960,f2007,f2028,f2035,f2051,f2058,f2065,f2085,f2112,f2119,f2137,f2144,f2151,f2158,f2180,f2198,f2205,f2213,f2221,f2234,f2241,f2248,f2258,f2265,f2272,f2280,f2293,f2312,f2330,f2337,f2344,f2364,f2371,f2384,f2411,f2418,f2425,f2462,f2477,f2490,f2497,f2504,f2512,f2521,f2538,f2576,f2608,f2619,f2632,f2657,f2672,f2683,f2690,f2697,f2738,f2779,f2786,f2836,f2858,f2865,f2875,f2882,f2889,f2897,f2915,f2932,f2939,f2964,f2971,f2978,f2984,f3026,f3044,f3066,f3084,f3091,f3101,f3128,f3135,f3146,f3153,f3211,f3224,f3231,f3238,f3257,f3278,f3286,f3337,f3367,f3381,f3430,f3473,f3490,f3503,f3530,f3537,f3555,f3573,f3580,f3587,f3594,f3607,f3616,f3645,f3652,f3665,f3680,f3694,f3701,f3709,f3722,f3729,f3743,f3755,f3762,f3769,f3787,f3804,f3811,f3818,f3825,f3833,f3841,f3853,f3860,f3877,f3884,f3914,f3930,f3937,f3944,f3964,f3969,f3982,f3989,f4007,f4014,f4021,f4028,f4035,f4065,f4076,f4083,f4093,f4137,f4148,f4183,f4191,f4202,f4237,f4245,f4252,f4297,f4306,f4358,f4378,f4385,f4393,f4400,f4412,f4426,f4463,f4471,f4481,f4495,f4502,f4509,f4516,f4529,f4536,f4543,f4567,f4589,f4596,f4603,f4610,f4623,f4653,f4662,f4757,f4764,f4778,f4785,f4792,f4799,f4849,f4856,f4863,f4951,f4958,f4965,f4972,f4984,f5008,f5009,f5016,f5017,f5024,f5031,f5038,f5045,f5052,f5059,f5066,f5073,f5080,f5087,f5095,f5240,f5261,f5277,f5294,f5315,f5322,f5494,f5511,f5518,f5553,f5560,f5567,f5574,f5581,f5588,f5595,f5602,f5699,f5711,f5718,f5725,f5732,f5739,f5746,f5754,f5774,f5781,f5788,f5795,f5802,f5819,f5842,f5905,f5912,f5919,f5926,f5933,f5940,f5947,f5985,f5992,f5999,f6022,f6030,f6037,f6053,f6064,f6071,f6079,f6092,f6100,f6109,f6116,f6123,f6130,f6137,f6144,f6151,f6158,f6166,f6184,f6219,f6237,f6258,f6265,f6275,f6292,f6299,f6312,f6319,f6333,f6340,f6353,f6360,f6367,f6374,f6383,f6390,f6397,f6405,f6431,f6438,f6445,f6452,f6470,f6477,f6486,f6520,f6527,f6541,f6562,f6569,f6579,f6596,f6603,f6615,f6628,f6662,f6670,f6677,f6684,f6717,f6807,f6846,f6875,f6885,f6908,f6919,f6926,f6977,f6990,f6997,f7091,f7098,f7138,f7146,f7184,f7235,f7242,f7265,f7313,f7320,f7347,f7374,f7406,f7413,f7471,f7481,f7514,f7525,f7543,f7550,f7576,f7627,f7640,f7660,f7704,f7734,f7746,f7753,f7760,f7805,f7812,f7819,f7832,f7843,f7850,f7863,f7870,f7907,f7938,f7947,f7961,f7985,f7992,f7999,f8020,f8045,f8052,f8063,f8082,f8089,f8101,f8112,f8119,f8126,f8133,f8140,f8164,f8171,f8193,f8200,f8208,f8221,f8236,f8258,f8268,f8331,f8333,f8336,f8366,f8368,f8371,f8373,f8378,f8380,f8382,f8385,f8387,f8389,f8391,f8393,f8395,f8397,f8399,f8401,f8403,f8405,f8407,f8409,f8421,f8423,f8425,f8427,f8429,f8431,f8433,f8435,f8437,f8439,f8441,f8443,f8445,f8447,f8449,f8451,f8453,f8456,f8959,f8966,f9068,f9071,f9135,f9137,f9139,f9147,f9166,f9168,f9176,f9178,f9180,f9278,f9280,f9286,f9288,f9291,f9301,f9303,f9305,f9308,f9315,f9317,f9324,f9326,f9333,f9338,f9341,f9351,f9355,f9358,f9365,f9471,f9493,f9512,f9547,f9636,f9751,f9771,f9798,f9812,f9819,f9847,f9854,f9861,f9891,f9906,f9918,f9930,f9931,f10001,f10008,f10044,f10099,f10106,f10179,f10186,f10213,f10220,f10227,f10239,f10246,f10283,f10290,f10311,f10318,f10325,f10332,f10339,f10350,f10391,f10409,f10447,f10454,f10461,f10481,f10496,f10503,f10522,f10529,f10538,f10555,f10587,f10638,f10676,f10695,f10707,f10743,f10750,f10757,f10764,f10771,f10778,f10790,f10797,f10804,f10817,f10824,f10848,f10865,f10867,f10869,f10871,f10873,f10905,f10912,f10925,f10932,f10957,f10970,f10977,f10984,f10991,f10998,f11005,f11029,f11044,f11055,f11062,f11069,f11076,f11083,f11114,f11165,f11172,f11179,f11210,f11217,f11224,f11231,f11259,f11284,f11309,f11316,f11323,f11336,f11343,f11360,f11374,f11383,f11390,f11397,f11404,f11415,f11422,f11429,f11443,f11468,f11487,f11503,f11510,f11533,f11548,f11555,f11562,f11581,f11593,f11600,f11607,f11614,f11621,f11640,f11653,f11670,f11706,f11713,f11720,f11727,f11760,f11797,f11804,f11887,f11894,f11913,f11920,f11957,f11964,f11971,f11978,f12017,f12029,f12064,f12071,f12078,f12125,f12162,f12170,f12177,f12184,f12191,f12198,f12208,f12215,f12231,f12248,f12255,f12262,f12269,f12276,f12283,f12290,f12309,f12347,f12356,f12364,f12371,f12388,f12395,f12409,f12416,f12423,f12435,f12442,f12449,f12456,f12469,f12482,f12507,f12525,f12532,f12539,f12546,f12561,f12568,f12594,f12623,f12720,f12755,f12838,f12841])).

fof(f12841,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_57
    | ~ spl13_348
    | ~ spl13_444
    | ~ spl13_446
    | ~ spl13_512 ),
    inference(avatar_contradiction_clause,[],[f12840])).

fof(f12840,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_57
    | ~ spl13_348
    | ~ spl13_444
    | ~ spl13_446
    | ~ spl13_512 ),
    inference(subsumption_resolution,[],[f12839,f12483])).

fof(f12483,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK3)
    | ~ spl13_444
    | ~ spl13_446 ),
    inference(unit_resulting_resolution,[],[f3429,f10685])).

fof(f10685,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | r2_hidden(X2,sK3) )
    | ~ spl13_444 ),
    inference(resolution,[],[f3380,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t1_subset)).

fof(f3380,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK3) )
    | ~ spl13_444 ),
    inference(avatar_component_clause,[],[f3379])).

fof(f3379,plain,
    ( spl13_444
  <=> ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_444])])).

fof(f3429,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK2)
    | ~ spl13_446 ),
    inference(avatar_component_clause,[],[f3428])).

fof(f3428,plain,
    ( spl13_446
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_446])])).

fof(f12839,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_57
    | ~ spl13_348
    | ~ spl13_512 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f363,f2575,f3832,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2)
      | ~ r1_orders_2(X1,sK6(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK6(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK7(X0,X1,X2,X5))
                      & m1_subset_1(sK7(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f77,f79,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK6(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK7(X0,X1,X2,X5))
        & m1_subset_1(sK7(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',d12_waybel_0)).

fof(f3832,plain,
    ( r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)))
    | ~ spl13_512 ),
    inference(avatar_component_clause,[],[f3831])).

fof(f3831,plain,
    ( spl13_512
  <=> r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_512])])).

fof(f2575,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_348 ),
    inference(avatar_component_clause,[],[f2574])).

fof(f2574,plain,
    ( spl13_348
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_348])])).

fof(f363,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | ~ spl13_57 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl13_57
  <=> ~ r2_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).

fof(f183,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl13_12
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f155,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl13_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f148,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl13_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f141,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f12838,plain,
    ( spl13_1418
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_492 ),
    inference(avatar_split_clause,[],[f9728,f3732,f294,f182,f154,f147,f140,f12836])).

fof(f12836,plain,
    ( spl13_1418
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1418])])).

fof(f294,plain,
    ( spl13_38
  <=> r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f3732,plain,
    ( spl13_492
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_492])])).

fof(f9728,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_492 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f3733,f109])).

fof(f109,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X5),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f3733,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_492 ),
    inference(avatar_component_clause,[],[f3732])).

fof(f295,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f12755,plain,
    ( spl13_700
    | ~ spl13_736 ),
    inference(avatar_split_clause,[],[f5805,f5786,f5551])).

fof(f5551,plain,
    ( spl13_700
  <=> m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_700])])).

fof(f5786,plain,
    ( spl13_736
  <=> r2_hidden(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_736])])).

fof(f5805,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_736 ),
    inference(unit_resulting_resolution,[],[f5787,f121])).

fof(f5787,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_736 ),
    inference(avatar_component_clause,[],[f5786])).

fof(f12720,plain,
    ( ~ spl13_1417
    | spl13_683 ),
    inference(avatar_split_clause,[],[f5305,f5238,f12718])).

fof(f12718,plain,
    ( spl13_1417
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1417])])).

fof(f5238,plain,
    ( spl13_683
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK10(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_683])])).

fof(f5305,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(u1_struct_0(sK1)))))
    | ~ spl13_683 ),
    inference(unit_resulting_resolution,[],[f119,f5239,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t4_subset)).

fof(f5239,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(u1_struct_0(sK1)))
    | ~ spl13_683 ),
    inference(avatar_component_clause,[],[f5238])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f23,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',existence_m1_subset_1)).

fof(f12623,plain,
    ( spl13_238
    | ~ spl13_1059
    | ~ spl13_6
    | spl13_207 ),
    inference(avatar_split_clause,[],[f1295,f1292,f161,f9796,f1721])).

fof(f1721,plain,
    ( spl13_238
  <=> o_0_0_xboole_0 = sK10(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_238])])).

fof(f9796,plain,
    ( spl13_1059
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1059])])).

fof(f161,plain,
    ( spl13_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f1292,plain,
    ( spl13_207
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_207])])).

fof(f1295,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK10(o_0_0_xboole_0))
    | o_0_0_xboole_0 = sK10(o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_207 ),
    inference(resolution,[],[f1293,f432])).

fof(f432,plain,
    ( ! [X4,X3] :
        ( r2_hidden(X3,X4)
        | ~ m1_subset_1(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl13_6 ),
    inference(resolution,[],[f122,f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl13_6 ),
    inference(backward_demodulation,[],[f200,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t6_boole)).

fof(f200,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f162,f108])).

fof(f162,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t2_subset)).

fof(f1293,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(o_0_0_xboole_0))
    | ~ spl13_207 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f12594,plain,
    ( ~ spl13_1415
    | ~ spl13_72
    | spl13_705 ),
    inference(avatar_split_clause,[],[f9800,f5562,f437,f12592])).

fof(f12592,plain,
    ( spl13_1415
  <=> ~ r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1415])])).

fof(f437,plain,
    ( spl13_72
  <=> m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f5562,plain,
    ( spl13_705
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_705])])).

fof(f9800,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_705 ),
    inference(unit_resulting_resolution,[],[f438,f5563,f130])).

fof(f5563,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_705 ),
    inference(avatar_component_clause,[],[f5562])).

fof(f438,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f437])).

fof(f12568,plain,
    ( ~ spl13_1413
    | spl13_1395 ),
    inference(avatar_split_clause,[],[f12510,f12454,f12566])).

fof(f12566,plain,
    ( spl13_1413
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1413])])).

fof(f12454,plain,
    ( spl13_1395
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1395])])).

fof(f12510,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_1395 ),
    inference(unit_resulting_resolution,[],[f12455,f121])).

fof(f12455,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_1395 ),
    inference(avatar_component_clause,[],[f12454])).

fof(f12561,plain,
    ( ~ spl13_1411
    | spl13_1393 ),
    inference(avatar_split_clause,[],[f12497,f12447,f12559])).

fof(f12559,plain,
    ( spl13_1411
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1411])])).

fof(f12447,plain,
    ( spl13_1393
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1393])])).

fof(f12497,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_1393 ),
    inference(unit_resulting_resolution,[],[f12448,f121])).

fof(f12448,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_1393 ),
    inference(avatar_component_clause,[],[f12447])).

fof(f12546,plain,
    ( ~ spl13_1409
    | spl13_1391 ),
    inference(avatar_split_clause,[],[f12472,f12440,f12544])).

fof(f12544,plain,
    ( spl13_1409
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1409])])).

fof(f12440,plain,
    ( spl13_1391
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1391])])).

fof(f12472,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_1391 ),
    inference(unit_resulting_resolution,[],[f12441,f121])).

fof(f12441,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_1391 ),
    inference(avatar_component_clause,[],[f12440])).

fof(f12539,plain,
    ( ~ spl13_1407
    | spl13_1389 ),
    inference(avatar_split_clause,[],[f12459,f12433,f12537])).

fof(f12537,plain,
    ( spl13_1407
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1407])])).

fof(f12433,plain,
    ( spl13_1389
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1389])])).

fof(f12459,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_1389 ),
    inference(unit_resulting_resolution,[],[f12434,f121])).

fof(f12434,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_1389 ),
    inference(avatar_component_clause,[],[f12433])).

fof(f12532,plain,
    ( ~ spl13_1405
    | ~ spl13_404
    | spl13_995 ),
    inference(avatar_split_clause,[],[f9271,f7945,f3036,f12530])).

fof(f12530,plain,
    ( spl13_1405
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1405])])).

fof(f3036,plain,
    ( spl13_404
  <=> k1_zfmisc_1(sK3) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_404])])).

fof(f7945,plain,
    ( spl13_995
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_995])])).

fof(f9271,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_404
    | ~ spl13_995 ),
    inference(backward_demodulation,[],[f3037,f7946])).

fof(f7946,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | ~ spl13_995 ),
    inference(avatar_component_clause,[],[f7945])).

fof(f3037,plain,
    ( k1_zfmisc_1(sK3) = o_0_0_xboole_0
    | ~ spl13_404 ),
    inference(avatar_component_clause,[],[f3036])).

fof(f12525,plain,
    ( ~ spl13_1403
    | spl13_1395 ),
    inference(avatar_split_clause,[],[f12508,f12454,f12523])).

fof(f12523,plain,
    ( spl13_1403
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1403])])).

fof(f12508,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1395 ),
    inference(unit_resulting_resolution,[],[f12455,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t3_subset)).

fof(f12507,plain,
    ( ~ spl13_1401
    | spl13_1393 ),
    inference(avatar_split_clause,[],[f12495,f12447,f12505])).

fof(f12505,plain,
    ( spl13_1401
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1401])])).

fof(f12495,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1393 ),
    inference(unit_resulting_resolution,[],[f12448,f126])).

fof(f12482,plain,
    ( ~ spl13_1399
    | spl13_1391 ),
    inference(avatar_split_clause,[],[f12470,f12440,f12480])).

fof(f12480,plain,
    ( spl13_1399
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1399])])).

fof(f12470,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1391 ),
    inference(unit_resulting_resolution,[],[f12441,f126])).

fof(f12469,plain,
    ( ~ spl13_1397
    | spl13_1389 ),
    inference(avatar_split_clause,[],[f12457,f12433,f12467])).

fof(f12467,plain,
    ( spl13_1397
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1397])])).

fof(f12457,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_1389 ),
    inference(unit_resulting_resolution,[],[f12434,f126])).

fof(f12456,plain,
    ( ~ spl13_1395
    | ~ spl13_970
    | spl13_1129 ),
    inference(avatar_split_clause,[],[f10484,f10479,f7751,f12454])).

fof(f7751,plain,
    ( spl13_970
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_970])])).

fof(f10479,plain,
    ( spl13_1129
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1129])])).

fof(f10484,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_970
    | ~ spl13_1129 ),
    inference(unit_resulting_resolution,[],[f7752,f10480,f130])).

fof(f10480,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1129 ),
    inference(avatar_component_clause,[],[f10479])).

fof(f7752,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_970 ),
    inference(avatar_component_clause,[],[f7751])).

fof(f12449,plain,
    ( ~ spl13_1393
    | ~ spl13_970
    | spl13_1111 ),
    inference(avatar_split_clause,[],[f10374,f10323,f7751,f12447])).

fof(f10323,plain,
    ( spl13_1111
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1111])])).

fof(f10374,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_970
    | ~ spl13_1111 ),
    inference(unit_resulting_resolution,[],[f7752,f10324,f130])).

fof(f10324,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1111 ),
    inference(avatar_component_clause,[],[f10323])).

fof(f12442,plain,
    ( ~ spl13_1391
    | ~ spl13_970
    | spl13_1091 ),
    inference(avatar_split_clause,[],[f10197,f10184,f7751,f12440])).

fof(f10184,plain,
    ( spl13_1091
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1091])])).

fof(f10197,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_970
    | ~ spl13_1091 ),
    inference(unit_resulting_resolution,[],[f7752,f10185,f130])).

fof(f10185,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1091 ),
    inference(avatar_component_clause,[],[f10184])).

fof(f12435,plain,
    ( ~ spl13_1389
    | ~ spl13_970
    | spl13_1089 ),
    inference(avatar_split_clause,[],[f10189,f10177,f7751,f12433])).

fof(f10177,plain,
    ( spl13_1089
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1089])])).

fof(f10189,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_970
    | ~ spl13_1089 ),
    inference(unit_resulting_resolution,[],[f7752,f10178,f130])).

fof(f10178,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_1089 ),
    inference(avatar_component_clause,[],[f10177])).

fof(f12423,plain,
    ( ~ spl13_1387
    | spl13_1381 ),
    inference(avatar_split_clause,[],[f12399,f12393,f12421])).

fof(f12421,plain,
    ( spl13_1387
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1387])])).

fof(f12393,plain,
    ( spl13_1381
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1381])])).

fof(f12399,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_1381 ),
    inference(unit_resulting_resolution,[],[f12394,f121])).

fof(f12394,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_1381 ),
    inference(avatar_component_clause,[],[f12393])).

fof(f12416,plain,
    ( ~ spl13_1385
    | spl13_1133 ),
    inference(avatar_split_clause,[],[f10511,f10501,f12414])).

fof(f12414,plain,
    ( spl13_1385
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1385])])).

fof(f10501,plain,
    ( spl13_1133
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1133])])).

fof(f10511,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl13_1133 ),
    inference(unit_resulting_resolution,[],[f119,f10502,f130])).

fof(f10502,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl13_1133 ),
    inference(avatar_component_clause,[],[f10501])).

fof(f12409,plain,
    ( ~ spl13_1383
    | spl13_1381 ),
    inference(avatar_split_clause,[],[f12397,f12393,f12407])).

fof(f12407,plain,
    ( spl13_1383
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1383])])).

fof(f12397,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1381 ),
    inference(unit_resulting_resolution,[],[f12394,f126])).

fof(f12395,plain,
    ( ~ spl13_1381
    | ~ spl13_234
    | spl13_1129 ),
    inference(avatar_split_clause,[],[f10483,f10479,f1660,f12393])).

fof(f1660,plain,
    ( spl13_234
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_234])])).

fof(f10483,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_234
    | ~ spl13_1129 ),
    inference(unit_resulting_resolution,[],[f1661,f10480,f130])).

fof(f1661,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_234 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f12388,plain,
    ( ~ spl13_1379
    | ~ spl13_404
    | spl13_489 ),
    inference(avatar_split_clause,[],[f9209,f3720,f3036,f12386])).

fof(f12386,plain,
    ( spl13_1379
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1379])])).

fof(f3720,plain,
    ( spl13_489
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_489])])).

fof(f9209,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))))
    | ~ spl13_404
    | ~ spl13_489 ),
    inference(backward_demodulation,[],[f3037,f3721])).

fof(f3721,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))))
    | ~ spl13_489 ),
    inference(avatar_component_clause,[],[f3720])).

fof(f12371,plain,
    ( ~ spl13_1377
    | spl13_1363 ),
    inference(avatar_split_clause,[],[f12313,f12274,f12369])).

fof(f12369,plain,
    ( spl13_1377
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1377])])).

fof(f12274,plain,
    ( spl13_1363
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1363])])).

fof(f12313,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1363 ),
    inference(unit_resulting_resolution,[],[f12275,f121])).

fof(f12275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1363 ),
    inference(avatar_component_clause,[],[f12274])).

fof(f12364,plain,
    ( ~ spl13_1375
    | spl13_1357 ),
    inference(avatar_split_clause,[],[f12299,f12253,f12362])).

fof(f12362,plain,
    ( spl13_1375
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1375])])).

fof(f12253,plain,
    ( spl13_1357
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1357])])).

fof(f12299,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_1357 ),
    inference(unit_resulting_resolution,[],[f12254,f121])).

fof(f12254,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_1357 ),
    inference(avatar_component_clause,[],[f12253])).

fof(f12356,plain,
    ( ~ spl13_1373
    | spl13_1327 ),
    inference(avatar_split_clause,[],[f12030,f12027,f12354])).

fof(f12354,plain,
    ( spl13_1373
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1373])])).

fof(f12027,plain,
    ( spl13_1327
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1327])])).

fof(f12030,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_1327 ),
    inference(unit_resulting_resolution,[],[f119,f12028,f130])).

fof(f12028,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(sK2))
    | ~ spl13_1327 ),
    inference(avatar_component_clause,[],[f12027])).

fof(f12347,plain,
    ( ~ spl13_1371
    | spl13_1363 ),
    inference(avatar_split_clause,[],[f12311,f12274,f12345])).

fof(f12345,plain,
    ( spl13_1371
  <=> ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1371])])).

fof(f12311,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1363 ),
    inference(unit_resulting_resolution,[],[f12275,f126])).

fof(f12309,plain,
    ( ~ spl13_1369
    | spl13_1357 ),
    inference(avatar_split_clause,[],[f12297,f12253,f12307])).

fof(f12307,plain,
    ( spl13_1369
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1369])])).

fof(f12297,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1357 ),
    inference(unit_resulting_resolution,[],[f12254,f126])).

fof(f12290,plain,
    ( ~ spl13_1367
    | spl13_1117 ),
    inference(avatar_split_clause,[],[f10410,f10348,f12288])).

fof(f12288,plain,
    ( spl13_1367
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1367])])).

fof(f10348,plain,
    ( spl13_1117
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1117])])).

fof(f10410,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(o_0_0_xboole_0))))
    | ~ spl13_1117 ),
    inference(unit_resulting_resolution,[],[f119,f10349,f130])).

fof(f10349,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(o_0_0_xboole_0))
    | ~ spl13_1117 ),
    inference(avatar_component_clause,[],[f10348])).

fof(f12283,plain,
    ( ~ spl13_1365
    | spl13_1115 ),
    inference(avatar_split_clause,[],[f10394,f10337,f12281])).

fof(f12281,plain,
    ( spl13_1365
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1365])])).

fof(f10337,plain,
    ( spl13_1115
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1115])])).

fof(f10394,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl13_1115 ),
    inference(unit_resulting_resolution,[],[f119,f10338,f130])).

fof(f10338,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1115 ),
    inference(avatar_component_clause,[],[f10337])).

fof(f12276,plain,
    ( ~ spl13_1363
    | ~ spl13_498
    | spl13_1115 ),
    inference(avatar_split_clause,[],[f10393,f10337,f3757,f12274])).

fof(f3757,plain,
    ( spl13_498
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_498])])).

fof(f10393,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_498
    | ~ spl13_1115 ),
    inference(unit_resulting_resolution,[],[f3758,f10338,f130])).

fof(f3758,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl13_498 ),
    inference(avatar_component_clause,[],[f3757])).

fof(f12269,plain,
    ( ~ spl13_1361
    | spl13_1113 ),
    inference(avatar_split_clause,[],[f10380,f10330,f12267])).

fof(f12267,plain,
    ( spl13_1361
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1361])])).

fof(f10330,plain,
    ( spl13_1113
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1113])])).

fof(f10380,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl13_1113 ),
    inference(unit_resulting_resolution,[],[f119,f10331,f130])).

fof(f10331,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1113 ),
    inference(avatar_component_clause,[],[f10330])).

fof(f12262,plain,
    ( ~ spl13_1359
    | spl13_585 ),
    inference(avatar_split_clause,[],[f10168,f4395,f12260])).

fof(f12260,plain,
    ( spl13_1359
  <=> ~ r2_hidden(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1359])])).

fof(f4395,plain,
    ( spl13_585
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_585])])).

fof(f10168,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_585 ),
    inference(unit_resulting_resolution,[],[f119,f4396,f130])).

fof(f4396,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_585 ),
    inference(avatar_component_clause,[],[f4395])).

fof(f12255,plain,
    ( ~ spl13_1357
    | ~ spl13_234
    | spl13_1111 ),
    inference(avatar_split_clause,[],[f10373,f10323,f1660,f12253])).

fof(f10373,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_234
    | ~ spl13_1111 ),
    inference(unit_resulting_resolution,[],[f1661,f10324,f130])).

fof(f12248,plain,
    ( ~ spl13_1355
    | ~ spl13_404
    | spl13_953 ),
    inference(avatar_split_clause,[],[f9266,f7548,f3036,f12246])).

fof(f12246,plain,
    ( spl13_1355
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1355])])).

fof(f7548,plain,
    ( spl13_953
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_953])])).

fof(f9266,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))))
    | ~ spl13_404
    | ~ spl13_953 ),
    inference(backward_demodulation,[],[f3037,f7549])).

fof(f7549,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))))
    | ~ spl13_953 ),
    inference(avatar_component_clause,[],[f7548])).

fof(f12231,plain,
    ( spl13_1352
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_712 ),
    inference(avatar_split_clause,[],[f9868,f5593,f285,f182,f154,f147,f140,f12229])).

fof(f12229,plain,
    ( spl13_1352
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1352])])).

fof(f285,plain,
    ( spl13_37
  <=> ~ r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).

fof(f5593,plain,
    ( spl13_712
  <=> m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_712])])).

fof(f9868,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_712 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f5594,f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
                      & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f82,f84,f83])).

fof(f83,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',d11_waybel_0)).

fof(f5594,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_712 ),
    inference(avatar_component_clause,[],[f5593])).

fof(f286,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_37 ),
    inference(avatar_component_clause,[],[f285])).

fof(f12215,plain,
    ( ~ spl13_1351
    | spl13_1331 ),
    inference(avatar_split_clause,[],[f12128,f12069,f12213])).

fof(f12213,plain,
    ( spl13_1351
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1351])])).

fof(f12069,plain,
    ( spl13_1331
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1331])])).

fof(f12128,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_1331 ),
    inference(unit_resulting_resolution,[],[f12070,f121])).

fof(f12070,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_1331 ),
    inference(avatar_component_clause,[],[f12069])).

fof(f12208,plain,
    ( ~ spl13_1349
    | spl13_1329 ),
    inference(avatar_split_clause,[],[f12115,f12062,f12206])).

fof(f12206,plain,
    ( spl13_1349
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1349])])).

fof(f12062,plain,
    ( spl13_1329
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1329])])).

fof(f12115,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_1329 ),
    inference(unit_resulting_resolution,[],[f12063,f121])).

fof(f12063,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_1329 ),
    inference(avatar_component_clause,[],[f12062])).

fof(f12198,plain,
    ( ~ spl13_1347
    | spl13_1095 ),
    inference(avatar_split_clause,[],[f10257,f10218,f12196])).

fof(f12196,plain,
    ( spl13_1347
  <=> ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1347])])).

fof(f10218,plain,
    ( spl13_1095
  <=> ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1095])])).

fof(f10257,plain,
    ( ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1095 ),
    inference(unit_resulting_resolution,[],[f119,f10219,f130])).

fof(f10219,plain,
    ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1095 ),
    inference(avatar_component_clause,[],[f10218])).

fof(f12191,plain,
    ( ~ spl13_1345
    | spl13_1093 ),
    inference(avatar_split_clause,[],[f10250,f10211,f12189])).

fof(f12189,plain,
    ( spl13_1345
  <=> ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1345])])).

fof(f10211,plain,
    ( spl13_1093
  <=> ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1093])])).

fof(f10250,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1093 ),
    inference(unit_resulting_resolution,[],[f119,f10212,f130])).

fof(f10212,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1093 ),
    inference(avatar_component_clause,[],[f10211])).

fof(f12184,plain,
    ( ~ spl13_1343
    | ~ spl13_6
    | spl13_281
    | spl13_443 ),
    inference(avatar_split_clause,[],[f8469,f3373,f2149,f161,f12182])).

fof(f12182,plain,
    ( spl13_1343
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1343])])).

fof(f2149,plain,
    ( spl13_281
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_281])])).

fof(f3373,plain,
    ( spl13_443
  <=> o_0_0_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_443])])).

fof(f8469,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_6
    | ~ spl13_281
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f2273,f3374])).

fof(f3374,plain,
    ( o_0_0_xboole_0 != sK2
    | ~ spl13_443 ),
    inference(avatar_component_clause,[],[f3373])).

fof(f2273,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | o_0_0_xboole_0 = sK2
    | ~ spl13_6
    | ~ spl13_281 ),
    inference(resolution,[],[f2150,f432])).

fof(f2150,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_281 ),
    inference(avatar_component_clause,[],[f2149])).

fof(f12177,plain,
    ( ~ spl13_1341
    | ~ spl13_404
    | spl13_929 ),
    inference(avatar_split_clause,[],[f9259,f7311,f3036,f12175])).

fof(f12175,plain,
    ( spl13_1341
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1341])])).

fof(f7311,plain,
    ( spl13_929
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_929])])).

fof(f9259,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_404
    | ~ spl13_929 ),
    inference(backward_demodulation,[],[f3037,f7312])).

fof(f7312,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | ~ spl13_929 ),
    inference(avatar_component_clause,[],[f7311])).

fof(f12170,plain,
    ( ~ spl13_1339
    | ~ spl13_404
    | spl13_857 ),
    inference(avatar_split_clause,[],[f9232,f6484,f3036,f12168])).

fof(f12168,plain,
    ( spl13_1339
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1339])])).

fof(f6484,plain,
    ( spl13_857
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_857])])).

fof(f9232,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_404
    | ~ spl13_857 ),
    inference(backward_demodulation,[],[f3037,f6485])).

fof(f6485,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_857 ),
    inference(avatar_component_clause,[],[f6484])).

fof(f12162,plain,
    ( ~ spl13_1337
    | spl13_1331 ),
    inference(avatar_split_clause,[],[f12126,f12069,f12160])).

fof(f12160,plain,
    ( spl13_1337
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1337])])).

fof(f12126,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1331 ),
    inference(unit_resulting_resolution,[],[f12070,f126])).

fof(f12125,plain,
    ( ~ spl13_1335
    | spl13_1329 ),
    inference(avatar_split_clause,[],[f12113,f12062,f12123])).

fof(f12123,plain,
    ( spl13_1335
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1335])])).

fof(f12113,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_1329 ),
    inference(unit_resulting_resolution,[],[f12063,f126])).

fof(f12078,plain,
    ( ~ spl13_1333
    | spl13_1315 ),
    inference(avatar_split_clause,[],[f11923,f11918,f12076])).

fof(f12076,plain,
    ( spl13_1333
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1333])])).

fof(f11918,plain,
    ( spl13_1315
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1315])])).

fof(f11923,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1315 ),
    inference(unit_resulting_resolution,[],[f11919,f121])).

fof(f11919,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1315 ),
    inference(avatar_component_clause,[],[f11918])).

fof(f12071,plain,
    ( ~ spl13_1331
    | ~ spl13_234
    | spl13_1091 ),
    inference(avatar_split_clause,[],[f10196,f10184,f1660,f12069])).

fof(f10196,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_234
    | ~ spl13_1091 ),
    inference(unit_resulting_resolution,[],[f1661,f10185,f130])).

fof(f12064,plain,
    ( ~ spl13_1329
    | ~ spl13_234
    | spl13_1089 ),
    inference(avatar_split_clause,[],[f10188,f10177,f1660,f12062])).

fof(f10188,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_234
    | ~ spl13_1089 ),
    inference(unit_resulting_resolution,[],[f1661,f10178,f130])).

fof(f12029,plain,
    ( ~ spl13_1327
    | ~ spl13_6
    | spl13_357
    | spl13_1325 ),
    inference(avatar_split_clause,[],[f12021,f12015,f2627,f161,f12027])).

fof(f2627,plain,
    ( spl13_357
  <=> o_0_0_xboole_0 != sK10(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_357])])).

fof(f12015,plain,
    ( spl13_1325
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1325])])).

fof(f12021,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(sK2))
    | ~ spl13_6
    | ~ spl13_357
    | ~ spl13_1325 ),
    inference(unit_resulting_resolution,[],[f2628,f12016,f432])).

fof(f12016,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(sK2))
    | ~ spl13_1325 ),
    inference(avatar_component_clause,[],[f12015])).

fof(f2628,plain,
    ( o_0_0_xboole_0 != sK10(sK2)
    | ~ spl13_357 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f12017,plain,
    ( ~ spl13_1325
    | ~ spl13_368
    | ~ spl13_404
    | spl13_1061 ),
    inference(avatar_split_clause,[],[f12006,f9810,f3036,f2733,f12015])).

fof(f2733,plain,
    ( spl13_368
  <=> m1_subset_1(sK10(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_368])])).

fof(f9810,plain,
    ( spl13_1061
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1061])])).

fof(f12006,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(sK2))
    | ~ spl13_368
    | ~ spl13_404
    | ~ spl13_1061 ),
    inference(unit_resulting_resolution,[],[f2734,f9836])).

fof(f9836,plain,
    ( ! [X0] :
        ( ~ r2_hidden(u1_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,o_0_0_xboole_0) )
    | ~ spl13_404
    | ~ spl13_1061 ),
    inference(forward_demodulation,[],[f9833,f3037])).

fof(f9833,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
        | ~ r2_hidden(u1_struct_0(sK1),X0) )
    | ~ spl13_1061 ),
    inference(resolution,[],[f9811,f130])).

fof(f9811,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl13_1061 ),
    inference(avatar_component_clause,[],[f9810])).

fof(f2734,plain,
    ( m1_subset_1(sK10(sK2),o_0_0_xboole_0)
    | ~ spl13_368 ),
    inference(avatar_component_clause,[],[f2733])).

fof(f11978,plain,
    ( ~ spl13_1323
    | ~ spl13_404
    | spl13_847 ),
    inference(avatar_split_clause,[],[f9229,f6436,f3036,f11976])).

fof(f11976,plain,
    ( spl13_1323
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1323])])).

fof(f6436,plain,
    ( spl13_847
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_847])])).

fof(f9229,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_404
    | ~ spl13_847 ),
    inference(backward_demodulation,[],[f3037,f6437])).

fof(f6437,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_847 ),
    inference(avatar_component_clause,[],[f6436])).

fof(f11971,plain,
    ( ~ spl13_1321
    | ~ spl13_404
    | spl13_487 ),
    inference(avatar_split_clause,[],[f9207,f3707,f3036,f11969])).

fof(f11969,plain,
    ( spl13_1321
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1321])])).

fof(f3707,plain,
    ( spl13_487
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_487])])).

fof(f9207,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl13_404
    | ~ spl13_487 ),
    inference(backward_demodulation,[],[f3037,f3708])).

fof(f3708,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl13_487 ),
    inference(avatar_component_clause,[],[f3707])).

fof(f11964,plain,
    ( ~ spl13_1319
    | ~ spl13_404
    | spl13_435 ),
    inference(avatar_split_clause,[],[f9197,f3276,f3036,f11962])).

fof(f11962,plain,
    ( spl13_1319
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1319])])).

fof(f3276,plain,
    ( spl13_435
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_435])])).

fof(f9197,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))))
    | ~ spl13_404
    | ~ spl13_435 ),
    inference(backward_demodulation,[],[f3037,f3277])).

fof(f3277,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))))
    | ~ spl13_435 ),
    inference(avatar_component_clause,[],[f3276])).

fof(f11957,plain,
    ( ~ spl13_1317
    | spl13_1315 ),
    inference(avatar_split_clause,[],[f11921,f11918,f11955])).

fof(f11955,plain,
    ( spl13_1317
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1317])])).

fof(f11921,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1315 ),
    inference(unit_resulting_resolution,[],[f11919,f126])).

fof(f11920,plain,
    ( ~ spl13_1315
    | spl13_209
    | ~ spl13_318 ),
    inference(avatar_split_clause,[],[f9948,f2342,f1297,f11918])).

fof(f1297,plain,
    ( spl13_209
  <=> ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_209])])).

fof(f2342,plain,
    ( spl13_318
  <=> r2_hidden(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_318])])).

fof(f9948,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_209
    | ~ spl13_318 ),
    inference(unit_resulting_resolution,[],[f2343,f1298,f130])).

fof(f1298,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_209 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f2343,plain,
    ( r2_hidden(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_318 ),
    inference(avatar_component_clause,[],[f2342])).

fof(f11913,plain,
    ( spl13_1312
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_492 ),
    inference(avatar_split_clause,[],[f9738,f3732,f182,f154,f147,f140,f11911])).

fof(f11911,plain,
    ( spl13_1312
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1312])])).

fof(f9738,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_492 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f3733,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_k2_waybel_0)).

fof(f11894,plain,
    ( ~ spl13_1311
    | spl13_1081 ),
    inference(avatar_split_clause,[],[f10046,f10006,f11892])).

fof(f11892,plain,
    ( spl13_1311
  <=> ~ r2_hidden(sK10(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1311])])).

fof(f10006,plain,
    ( spl13_1081
  <=> ~ m1_subset_1(sK10(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1081])])).

fof(f10046,plain,
    ( ~ r2_hidden(sK10(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1081 ),
    inference(unit_resulting_resolution,[],[f119,f10007,f130])).

fof(f10007,plain,
    ( ~ m1_subset_1(sK10(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1081 ),
    inference(avatar_component_clause,[],[f10006])).

fof(f11887,plain,
    ( ~ spl13_1309
    | spl13_1079 ),
    inference(avatar_split_clause,[],[f10010,f9999,f11885])).

fof(f11885,plain,
    ( spl13_1309
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1309])])).

fof(f9999,plain,
    ( spl13_1079
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1079])])).

fof(f10010,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1079 ),
    inference(unit_resulting_resolution,[],[f119,f10000,f130])).

fof(f10000,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1079 ),
    inference(avatar_component_clause,[],[f9999])).

fof(f11804,plain,
    ( ~ spl13_1307
    | spl13_1303 ),
    inference(avatar_split_clause,[],[f11787,f11758,f11802])).

fof(f11802,plain,
    ( spl13_1307
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1307])])).

fof(f11758,plain,
    ( spl13_1303
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1303])])).

fof(f11787,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1303 ),
    inference(unit_resulting_resolution,[],[f11759,f121])).

fof(f11759,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1303 ),
    inference(avatar_component_clause,[],[f11758])).

fof(f11797,plain,
    ( ~ spl13_1305
    | spl13_1303 ),
    inference(avatar_split_clause,[],[f11785,f11758,f11795])).

fof(f11795,plain,
    ( spl13_1305
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1305])])).

fof(f11785,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1303 ),
    inference(unit_resulting_resolution,[],[f11759,f126])).

fof(f11760,plain,
    ( ~ spl13_1303
    | spl13_1217
    | ~ spl13_1294 ),
    inference(avatar_split_clause,[],[f11739,f11704,f11170,f11758])).

fof(f11170,plain,
    ( spl13_1217
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1217])])).

fof(f11704,plain,
    ( spl13_1294
  <=> r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1294])])).

fof(f11739,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1217
    | ~ spl13_1294 ),
    inference(unit_resulting_resolution,[],[f11171,f11705,f130])).

fof(f11705,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2))
    | ~ spl13_1294 ),
    inference(avatar_component_clause,[],[f11704])).

fof(f11171,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1217 ),
    inference(avatar_component_clause,[],[f11170])).

fof(f11727,plain,
    ( ~ spl13_1301
    | spl13_1283 ),
    inference(avatar_split_clause,[],[f11660,f11605,f11725])).

fof(f11725,plain,
    ( spl13_1301
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1301])])).

fof(f11605,plain,
    ( spl13_1283
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1283])])).

fof(f11660,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_1283 ),
    inference(unit_resulting_resolution,[],[f11606,f121])).

fof(f11606,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_1283 ),
    inference(avatar_component_clause,[],[f11605])).

fof(f11720,plain,
    ( ~ spl13_1299
    | spl13_1281 ),
    inference(avatar_split_clause,[],[f11643,f11598,f11718])).

fof(f11718,plain,
    ( spl13_1299
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1299])])).

fof(f11598,plain,
    ( spl13_1281
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1281])])).

fof(f11643,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1281 ),
    inference(unit_resulting_resolution,[],[f11599,f121])).

fof(f11599,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1281 ),
    inference(avatar_component_clause,[],[f11598])).

fof(f11713,plain,
    ( ~ spl13_1297
    | spl13_1279 ),
    inference(avatar_split_clause,[],[f11630,f11591,f11711])).

fof(f11711,plain,
    ( spl13_1297
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1297])])).

fof(f11591,plain,
    ( spl13_1279
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1279])])).

fof(f11630,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1279 ),
    inference(unit_resulting_resolution,[],[f11592,f121])).

fof(f11592,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1279 ),
    inference(avatar_component_clause,[],[f11591])).

fof(f11706,plain,
    ( spl13_1294
    | spl13_967 ),
    inference(avatar_split_clause,[],[f7929,f7732,f11704])).

fof(f7732,plain,
    ( spl13_967
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_967])])).

fof(f7929,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2))
    | ~ spl13_967 ),
    inference(resolution,[],[f7738,f119])).

fof(f7738,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | r2_hidden(X0,k1_zfmisc_1(sK2)) )
    | ~ spl13_967 ),
    inference(resolution,[],[f7733,f122])).

fof(f7733,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl13_967 ),
    inference(avatar_component_clause,[],[f7732])).

fof(f11670,plain,
    ( ~ spl13_1293
    | spl13_1283 ),
    inference(avatar_split_clause,[],[f11658,f11605,f11668])).

fof(f11668,plain,
    ( spl13_1293
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1293])])).

fof(f11658,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK10(o_0_0_xboole_0))
    | ~ spl13_1283 ),
    inference(unit_resulting_resolution,[],[f11606,f126])).

fof(f11653,plain,
    ( ~ spl13_1291
    | spl13_1281 ),
    inference(avatar_split_clause,[],[f11641,f11598,f11651])).

fof(f11651,plain,
    ( spl13_1291
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1291])])).

fof(f11641,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK4(sK1))
    | ~ spl13_1281 ),
    inference(unit_resulting_resolution,[],[f11599,f126])).

fof(f11640,plain,
    ( ~ spl13_1289
    | spl13_1279 ),
    inference(avatar_split_clause,[],[f11628,f11591,f11638])).

fof(f11638,plain,
    ( spl13_1289
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1289])])).

fof(f11628,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),u1_struct_0(sK1))
    | ~ spl13_1279 ),
    inference(unit_resulting_resolution,[],[f11592,f126])).

fof(f11621,plain,
    ( ~ spl13_1287
    | spl13_1273 ),
    inference(avatar_split_clause,[],[f11571,f11553,f11619])).

fof(f11619,plain,
    ( spl13_1287
  <=> ~ r2_hidden(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1287])])).

fof(f11553,plain,
    ( spl13_1273
  <=> ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1273])])).

fof(f11571,plain,
    ( ~ r2_hidden(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1273 ),
    inference(unit_resulting_resolution,[],[f11554,f121])).

fof(f11554,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1273 ),
    inference(avatar_component_clause,[],[f11553])).

fof(f11614,plain,
    ( ~ spl13_1285
    | ~ spl13_6
    | spl13_937
    | spl13_1271 ),
    inference(avatar_split_clause,[],[f11566,f11546,f7395,f161,f11612])).

fof(f11612,plain,
    ( spl13_1285
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1285])])).

fof(f7395,plain,
    ( spl13_937
  <=> o_0_0_xboole_0 != sK10(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_937])])).

fof(f11546,plain,
    ( spl13_1271
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1271])])).

fof(f11566,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_6
    | ~ spl13_937
    | ~ spl13_1271 ),
    inference(unit_resulting_resolution,[],[f7396,f11547,f432])).

fof(f11547,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1271 ),
    inference(avatar_component_clause,[],[f11546])).

fof(f7396,plain,
    ( o_0_0_xboole_0 != sK10(k1_zfmisc_1(sK2))
    | ~ spl13_937 ),
    inference(avatar_component_clause,[],[f7395])).

fof(f11607,plain,
    ( ~ spl13_1283
    | ~ spl13_970
    | spl13_1059 ),
    inference(avatar_split_clause,[],[f9940,f9796,f7751,f11605])).

fof(f9940,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_970
    | ~ spl13_1059 ),
    inference(unit_resulting_resolution,[],[f9797,f7752,f130])).

fof(f9797,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK10(o_0_0_xboole_0))
    | ~ spl13_1059 ),
    inference(avatar_component_clause,[],[f9796])).

fof(f11600,plain,
    ( ~ spl13_1281
    | ~ spl13_970
    | spl13_1075 ),
    inference(avatar_split_clause,[],[f9939,f9916,f7751,f11598])).

fof(f9916,plain,
    ( spl13_1075
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1075])])).

fof(f9939,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_970
    | ~ spl13_1075 ),
    inference(unit_resulting_resolution,[],[f9917,f7752,f130])).

fof(f9917,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(sK1))
    | ~ spl13_1075 ),
    inference(avatar_component_clause,[],[f9916])).

fof(f11593,plain,
    ( ~ spl13_1279
    | spl13_699
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f9937,f7751,f5513,f11591])).

fof(f5513,plain,
    ( spl13_699
  <=> ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_699])])).

fof(f9937,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_699
    | ~ spl13_970 ),
    inference(unit_resulting_resolution,[],[f5514,f7752,f130])).

fof(f5514,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_699 ),
    inference(avatar_component_clause,[],[f5513])).

fof(f11581,plain,
    ( ~ spl13_1277
    | spl13_1273 ),
    inference(avatar_split_clause,[],[f11568,f11553,f11579])).

fof(f11579,plain,
    ( spl13_1277
  <=> ~ r1_tarski(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1277])])).

fof(f11568,plain,
    ( ~ r1_tarski(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1273 ),
    inference(unit_resulting_resolution,[],[f11554,f126])).

fof(f11562,plain,
    ( ~ spl13_1275
    | spl13_1269 ),
    inference(avatar_split_clause,[],[f11538,f11531,f11560])).

fof(f11560,plain,
    ( spl13_1275
  <=> ~ r2_hidden(sK10(sK4(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1275])])).

fof(f11531,plain,
    ( spl13_1269
  <=> ~ m1_subset_1(sK10(sK4(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1269])])).

fof(f11538,plain,
    ( ~ r2_hidden(sK10(sK4(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1269 ),
    inference(unit_resulting_resolution,[],[f11532,f121])).

fof(f11532,plain,
    ( ~ m1_subset_1(sK10(sK4(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1269 ),
    inference(avatar_component_clause,[],[f11531])).

fof(f11555,plain,
    ( ~ spl13_1273
    | ~ spl13_266
    | spl13_1269 ),
    inference(avatar_split_clause,[],[f11536,f11531,f2056,f11553])).

fof(f2056,plain,
    ( spl13_266
  <=> r2_hidden(sK10(sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_266])])).

fof(f11536,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_266
    | ~ spl13_1269 ),
    inference(unit_resulting_resolution,[],[f2057,f11532,f130])).

fof(f2057,plain,
    ( r2_hidden(sK10(sK4(sK1)),sK4(sK1))
    | ~ spl13_266 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f11548,plain,
    ( ~ spl13_1271
    | ~ spl13_6
    | spl13_963 ),
    inference(avatar_split_clause,[],[f7717,f7693,f161,f11546])).

fof(f7693,plain,
    ( spl13_963
  <=> k1_zfmisc_1(sK2) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_963])])).

fof(f7717,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_6
    | ~ spl13_963 ),
    inference(unit_resulting_resolution,[],[f119,f7694,f838])).

fof(f838,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,X3)
        | o_0_0_xboole_0 = X4
        | ~ m1_subset_1(X3,X4) )
    | ~ spl13_6 ),
    inference(resolution,[],[f432,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',antisymmetry_r2_hidden)).

fof(f7694,plain,
    ( k1_zfmisc_1(sK2) != o_0_0_xboole_0
    | ~ spl13_963 ),
    inference(avatar_component_clause,[],[f7693])).

fof(f11533,plain,
    ( ~ spl13_1269
    | ~ spl13_6
    | ~ spl13_1022 ),
    inference(avatar_split_clause,[],[f8183,f8117,f161,f11531])).

fof(f8117,plain,
    ( spl13_1022
  <=> r2_hidden(sK10(sK10(sK4(sK1))),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1022])])).

fof(f8183,plain,
    ( ~ m1_subset_1(sK10(sK4(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_1022 ),
    inference(resolution,[],[f8148,f162])).

fof(f8148,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(sK4(sK1)),k1_zfmisc_1(X0)) )
    | ~ spl13_1022 ),
    inference(resolution,[],[f8118,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t5_subset)).

fof(f8118,plain,
    ( r2_hidden(sK10(sK10(sK4(sK1))),sK10(sK4(sK1)))
    | ~ spl13_1022 ),
    inference(avatar_component_clause,[],[f8117])).

fof(f11510,plain,
    ( spl13_1266
    | ~ spl13_1250 ),
    inference(avatar_split_clause,[],[f11446,f11395,f11508])).

fof(f11508,plain,
    ( spl13_1266
  <=> m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1266])])).

fof(f11395,plain,
    ( spl13_1250
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1250])])).

fof(f11446,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK3)
    | ~ spl13_1250 ),
    inference(unit_resulting_resolution,[],[f11396,f121])).

fof(f11396,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK3)
    | ~ spl13_1250 ),
    inference(avatar_component_clause,[],[f11395])).

fof(f11503,plain,
    ( ~ spl13_1265
    | ~ spl13_1250 ),
    inference(avatar_split_clause,[],[f11445,f11395,f11501])).

fof(f11501,plain,
    ( spl13_1265
  <=> ~ r2_hidden(sK3,sK10(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1265])])).

fof(f11445,plain,
    ( ~ r2_hidden(sK3,sK10(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_1250 ),
    inference(unit_resulting_resolution,[],[f11396,f120])).

fof(f11487,plain,
    ( ~ spl13_1263
    | spl13_1249 ),
    inference(avatar_split_clause,[],[f11433,f11388,f11485])).

fof(f11485,plain,
    ( spl13_1263
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1263])])).

fof(f11388,plain,
    ( spl13_1249
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1249])])).

fof(f11433,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1249 ),
    inference(unit_resulting_resolution,[],[f11389,f121])).

fof(f11389,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_1249 ),
    inference(avatar_component_clause,[],[f11388])).

fof(f11468,plain,
    ( spl13_204
    | ~ spl13_72
    | ~ spl13_266 ),
    inference(avatar_split_clause,[],[f8299,f2056,f437,f1214])).

fof(f1214,plain,
    ( spl13_204
  <=> r2_hidden(sK10(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_204])])).

fof(f8299,plain,
    ( r2_hidden(sK10(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl13_72
    | ~ spl13_266 ),
    inference(unit_resulting_resolution,[],[f119,f438,f2171])).

fof(f2171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(X0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl13_266 ),
    inference(resolution,[],[f2075,f122])).

fof(f2075,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(X0)) )
    | ~ spl13_266 ),
    inference(resolution,[],[f2057,f131])).

fof(f11443,plain,
    ( ~ spl13_1261
    | spl13_1249 ),
    inference(avatar_split_clause,[],[f11431,f11388,f11441])).

fof(f11441,plain,
    ( spl13_1261
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1261])])).

fof(f11431,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK1))
    | ~ spl13_1249 ),
    inference(unit_resulting_resolution,[],[f11389,f126])).

fof(f11429,plain,
    ( ~ spl13_1259
    | spl13_1237 ),
    inference(avatar_split_clause,[],[f11364,f11321,f11427])).

fof(f11427,plain,
    ( spl13_1259
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1259])])).

fof(f11321,plain,
    ( spl13_1237
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1237])])).

fof(f11364,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1237 ),
    inference(unit_resulting_resolution,[],[f11322,f121])).

fof(f11322,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1237 ),
    inference(avatar_component_clause,[],[f11321])).

fof(f11422,plain,
    ( ~ spl13_1257
    | spl13_1235 ),
    inference(avatar_split_clause,[],[f11350,f11314,f11420])).

fof(f11420,plain,
    ( spl13_1257
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1257])])).

fof(f11314,plain,
    ( spl13_1235
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1235])])).

fof(f11350,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1235 ),
    inference(unit_resulting_resolution,[],[f11315,f121])).

fof(f11315,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1235 ),
    inference(avatar_component_clause,[],[f11314])).

fof(f11415,plain,
    ( ~ spl13_1255
    | ~ spl13_6
    | spl13_443
    | ~ spl13_954 ),
    inference(avatar_split_clause,[],[f11300,f7574,f3373,f161,f11413])).

fof(f11413,plain,
    ( spl13_1255
  <=> ~ r2_hidden(sK2,sK10(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1255])])).

fof(f7574,plain,
    ( spl13_954
  <=> m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_954])])).

fof(f11300,plain,
    ( ~ r2_hidden(sK2,sK10(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_954 ),
    inference(unit_resulting_resolution,[],[f3374,f7575,f838])).

fof(f7575,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK2)
    | ~ spl13_954 ),
    inference(avatar_component_clause,[],[f7574])).

fof(f11404,plain,
    ( spl13_1252
    | ~ spl13_6
    | spl13_443
    | ~ spl13_954 ),
    inference(avatar_split_clause,[],[f11298,f7574,f3373,f161,f11402])).

fof(f11402,plain,
    ( spl13_1252
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1252])])).

fof(f11298,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK2)
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_954 ),
    inference(unit_resulting_resolution,[],[f3374,f7575,f432])).

fof(f11397,plain,
    ( spl13_1250
    | ~ spl13_444
    | ~ spl13_954 ),
    inference(avatar_split_clause,[],[f11294,f7574,f3379,f11395])).

fof(f11294,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK3)
    | ~ spl13_444
    | ~ spl13_954 ),
    inference(unit_resulting_resolution,[],[f7575,f3380])).

fof(f11390,plain,
    ( ~ spl13_1249
    | ~ spl13_234
    | spl13_1075 ),
    inference(avatar_split_clause,[],[f9919,f9916,f1660,f11388])).

fof(f9919,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_234
    | ~ spl13_1075 ),
    inference(unit_resulting_resolution,[],[f1661,f9917,f130])).

fof(f11383,plain,
    ( ~ spl13_1247
    | ~ spl13_404
    | spl13_557 ),
    inference(avatar_split_clause,[],[f9222,f4091,f3036,f11381])).

fof(f11381,plain,
    ( spl13_1247
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1247])])).

fof(f4091,plain,
    ( spl13_557
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_557])])).

fof(f9222,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_404
    | ~ spl13_557 ),
    inference(backward_demodulation,[],[f3037,f4092])).

fof(f4092,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_557 ),
    inference(avatar_component_clause,[],[f4091])).

fof(f11374,plain,
    ( ~ spl13_1245
    | spl13_1237 ),
    inference(avatar_split_clause,[],[f11361,f11321,f11372])).

fof(f11372,plain,
    ( spl13_1245
  <=> ~ r1_tarski(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1245])])).

fof(f11361,plain,
    ( ~ r1_tarski(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1237 ),
    inference(unit_resulting_resolution,[],[f11322,f126])).

fof(f11360,plain,
    ( ~ spl13_1243
    | spl13_1235 ),
    inference(avatar_split_clause,[],[f11348,f11314,f11358])).

fof(f11358,plain,
    ( spl13_1243
  <=> ~ r1_tarski(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1243])])).

fof(f11348,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1235 ),
    inference(unit_resulting_resolution,[],[f11315,f126])).

fof(f11343,plain,
    ( ~ spl13_1241
    | spl13_1223 ),
    inference(avatar_split_clause,[],[f11274,f11215,f11341])).

fof(f11341,plain,
    ( spl13_1241
  <=> ~ r2_hidden(sK10(sK3),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1241])])).

fof(f11215,plain,
    ( spl13_1223
  <=> ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1223])])).

fof(f11274,plain,
    ( ~ r2_hidden(sK10(sK3),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1223 ),
    inference(unit_resulting_resolution,[],[f11216,f121])).

fof(f11216,plain,
    ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1223 ),
    inference(avatar_component_clause,[],[f11215])).

fof(f11336,plain,
    ( ~ spl13_1239
    | spl13_1219 ),
    inference(avatar_split_clause,[],[f11249,f11177,f11334])).

fof(f11334,plain,
    ( spl13_1239
  <=> ~ r2_hidden(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1239])])).

fof(f11177,plain,
    ( spl13_1219
  <=> ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1219])])).

fof(f11249,plain,
    ( ~ r2_hidden(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1219 ),
    inference(unit_resulting_resolution,[],[f11178,f121])).

fof(f11178,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1219 ),
    inference(avatar_component_clause,[],[f11177])).

fof(f11323,plain,
    ( ~ spl13_1237
    | ~ spl13_344
    | spl13_1219 ),
    inference(avatar_split_clause,[],[f11247,f11177,f2519,f11321])).

fof(f2519,plain,
    ( spl13_344
  <=> r2_hidden(sK10(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_344])])).

fof(f11247,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_344
    | ~ spl13_1219 ),
    inference(unit_resulting_resolution,[],[f2520,f11178,f130])).

fof(f2520,plain,
    ( r2_hidden(sK10(sK2),sK3)
    | ~ spl13_344 ),
    inference(avatar_component_clause,[],[f2519])).

fof(f11316,plain,
    ( ~ spl13_1235
    | ~ spl13_328
    | spl13_1219 ),
    inference(avatar_split_clause,[],[f11246,f11177,f2416,f11314])).

fof(f2416,plain,
    ( spl13_328
  <=> r2_hidden(sK10(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_328])])).

fof(f11246,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_328
    | ~ spl13_1219 ),
    inference(unit_resulting_resolution,[],[f2417,f11178,f130])).

fof(f2417,plain,
    ( r2_hidden(sK10(sK2),sK2)
    | ~ spl13_328 ),
    inference(avatar_component_clause,[],[f2416])).

fof(f11309,plain,
    ( ~ spl13_1233
    | spl13_1217 ),
    inference(avatar_split_clause,[],[f11241,f11170,f11307])).

fof(f11307,plain,
    ( spl13_1233
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1233])])).

fof(f11241,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1217 ),
    inference(unit_resulting_resolution,[],[f11171,f121])).

fof(f11284,plain,
    ( ~ spl13_1231
    | spl13_1223 ),
    inference(avatar_split_clause,[],[f11271,f11215,f11282])).

fof(f11282,plain,
    ( spl13_1231
  <=> ~ r1_tarski(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1231])])).

fof(f11271,plain,
    ( ~ r1_tarski(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1223 ),
    inference(unit_resulting_resolution,[],[f11216,f126])).

fof(f11259,plain,
    ( ~ spl13_1229
    | spl13_1219 ),
    inference(avatar_split_clause,[],[f11245,f11177,f11257])).

fof(f11257,plain,
    ( spl13_1229
  <=> ~ r1_tarski(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1229])])).

fof(f11245,plain,
    ( ~ r1_tarski(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1219 ),
    inference(unit_resulting_resolution,[],[f11178,f126])).

fof(f11231,plain,
    ( ~ spl13_1227
    | ~ spl13_6
    | spl13_937
    | spl13_1209 ),
    inference(avatar_split_clause,[],[f11131,f11074,f7395,f161,f11229])).

fof(f11229,plain,
    ( spl13_1227
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1227])])).

fof(f11074,plain,
    ( spl13_1209
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1209])])).

fof(f11131,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_6
    | ~ spl13_937
    | ~ spl13_1209 ),
    inference(unit_resulting_resolution,[],[f7396,f11075,f432])).

fof(f11075,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1209 ),
    inference(avatar_component_clause,[],[f11074])).

fof(f11224,plain,
    ( ~ spl13_1225
    | spl13_1205 ),
    inference(avatar_split_clause,[],[f11125,f11060,f11222])).

fof(f11222,plain,
    ( spl13_1225
  <=> ~ r2_hidden(sK10(sK10(sK3)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1225])])).

fof(f11060,plain,
    ( spl13_1205
  <=> ~ m1_subset_1(sK10(sK10(sK3)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1205])])).

fof(f11125,plain,
    ( ~ r2_hidden(sK10(sK10(sK3)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1205 ),
    inference(unit_resulting_resolution,[],[f11061,f121])).

fof(f11061,plain,
    ( ~ m1_subset_1(sK10(sK10(sK3)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1205 ),
    inference(avatar_component_clause,[],[f11060])).

fof(f11217,plain,
    ( ~ spl13_1223
    | ~ spl13_386
    | spl13_1205 ),
    inference(avatar_split_clause,[],[f11123,f11060,f2887,f11215])).

fof(f2887,plain,
    ( spl13_386
  <=> r2_hidden(sK10(sK10(sK3)),sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_386])])).

fof(f11123,plain,
    ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_386
    | ~ spl13_1205 ),
    inference(unit_resulting_resolution,[],[f2888,f11061,f130])).

fof(f2888,plain,
    ( r2_hidden(sK10(sK10(sK3)),sK10(sK3))
    | ~ spl13_386 ),
    inference(avatar_component_clause,[],[f2887])).

fof(f11210,plain,
    ( ~ spl13_1221
    | spl13_1203 ),
    inference(avatar_split_clause,[],[f11118,f11053,f11208])).

fof(f11208,plain,
    ( spl13_1221
  <=> ~ r2_hidden(sK10(sK10(sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1221])])).

fof(f11053,plain,
    ( spl13_1203
  <=> ~ m1_subset_1(sK10(sK10(sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1203])])).

fof(f11118,plain,
    ( ~ r2_hidden(sK10(sK10(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1203 ),
    inference(unit_resulting_resolution,[],[f11054,f121])).

fof(f11054,plain,
    ( ~ m1_subset_1(sK10(sK10(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1203 ),
    inference(avatar_component_clause,[],[f11053])).

fof(f11179,plain,
    ( ~ spl13_1219
    | ~ spl13_366
    | spl13_1203 ),
    inference(avatar_split_clause,[],[f11116,f11053,f2695,f11177])).

fof(f2695,plain,
    ( spl13_366
  <=> r2_hidden(sK10(sK10(sK2)),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_366])])).

fof(f11116,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_366
    | ~ spl13_1203 ),
    inference(unit_resulting_resolution,[],[f2696,f11054,f130])).

fof(f2696,plain,
    ( r2_hidden(sK10(sK10(sK2)),sK10(sK2))
    | ~ spl13_366 ),
    inference(avatar_component_clause,[],[f2695])).

fof(f11172,plain,
    ( ~ spl13_1217
    | ~ spl13_6
    | spl13_937 ),
    inference(avatar_split_clause,[],[f10293,f7395,f161,f11170])).

fof(f10293,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_937 ),
    inference(unit_resulting_resolution,[],[f162,f119,f7396,f837])).

fof(f837,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,X1) )
    | ~ spl13_6 ),
    inference(resolution,[],[f432,f131])).

fof(f11165,plain,
    ( ~ spl13_1215
    | ~ spl13_404
    | spl13_553 ),
    inference(avatar_split_clause,[],[f9220,f4074,f3036,f11163])).

fof(f11163,plain,
    ( spl13_1215
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1215])])).

fof(f4074,plain,
    ( spl13_553
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_553])])).

fof(f9220,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_404
    | ~ spl13_553 ),
    inference(backward_demodulation,[],[f3037,f4075])).

fof(f4075,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_553 ),
    inference(avatar_component_clause,[],[f4074])).

fof(f11114,plain,
    ( ~ spl13_1213
    | spl13_1195 ),
    inference(avatar_split_clause,[],[f11034,f10996,f11112])).

fof(f11112,plain,
    ( spl13_1213
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1213])])).

fof(f10996,plain,
    ( spl13_1195
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1195])])).

fof(f11034,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_1195 ),
    inference(unit_resulting_resolution,[],[f10997,f121])).

fof(f10997,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_1195 ),
    inference(avatar_component_clause,[],[f10996])).

fof(f11083,plain,
    ( ~ spl13_1211
    | spl13_1191 ),
    inference(avatar_split_clause,[],[f11019,f10982,f11081])).

fof(f11081,plain,
    ( spl13_1211
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1211])])).

fof(f10982,plain,
    ( spl13_1191
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1191])])).

fof(f11019,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1191 ),
    inference(unit_resulting_resolution,[],[f10983,f121])).

fof(f10983,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1191 ),
    inference(avatar_component_clause,[],[f10982])).

fof(f11076,plain,
    ( ~ spl13_1209
    | spl13_1149 ),
    inference(avatar_split_clause,[],[f10697,f10693,f11074])).

fof(f10693,plain,
    ( spl13_1149
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1149])])).

fof(f10697,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_1149 ),
    inference(unit_resulting_resolution,[],[f119,f10694,f130])).

fof(f10694,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK2)
    | ~ spl13_1149 ),
    inference(avatar_component_clause,[],[f10693])).

fof(f11069,plain,
    ( ~ spl13_1207
    | ~ spl13_404
    | spl13_855 ),
    inference(avatar_split_clause,[],[f9231,f6475,f3036,f11067])).

fof(f11067,plain,
    ( spl13_1207
  <=> ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1207])])).

fof(f6475,plain,
    ( spl13_855
  <=> ~ r1_tarski(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_855])])).

fof(f9231,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_404
    | ~ spl13_855 ),
    inference(backward_demodulation,[],[f3037,f6476])).

fof(f6476,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_855 ),
    inference(avatar_component_clause,[],[f6475])).

fof(f11062,plain,
    ( ~ spl13_1205
    | ~ spl13_6
    | ~ spl13_884 ),
    inference(avatar_split_clause,[],[f6746,f6675,f161,f11060])).

fof(f6675,plain,
    ( spl13_884
  <=> r2_hidden(sK10(sK10(sK10(sK3))),sK10(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_884])])).

fof(f6746,plain,
    ( ~ m1_subset_1(sK10(sK10(sK3)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_884 ),
    inference(resolution,[],[f6699,f162])).

fof(f6699,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(sK10(sK3)),k1_zfmisc_1(X0)) )
    | ~ spl13_884 ),
    inference(resolution,[],[f6676,f131])).

fof(f6676,plain,
    ( r2_hidden(sK10(sK10(sK10(sK3))),sK10(sK10(sK3)))
    | ~ spl13_884 ),
    inference(avatar_component_clause,[],[f6675])).

fof(f11055,plain,
    ( ~ spl13_1203
    | ~ spl13_6
    | ~ spl13_838 ),
    inference(avatar_split_clause,[],[f6454,f6388,f161,f11053])).

fof(f6388,plain,
    ( spl13_838
  <=> r2_hidden(sK10(sK10(sK10(sK2))),sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_838])])).

fof(f6454,plain,
    ( ~ m1_subset_1(sK10(sK10(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_838 ),
    inference(resolution,[],[f6413,f162])).

fof(f6413,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(sK10(sK2)),k1_zfmisc_1(X0)) )
    | ~ spl13_838 ),
    inference(resolution,[],[f6389,f131])).

fof(f6389,plain,
    ( r2_hidden(sK10(sK10(sK10(sK2))),sK10(sK10(sK2)))
    | ~ spl13_838 ),
    inference(avatar_component_clause,[],[f6388])).

fof(f11044,plain,
    ( ~ spl13_1201
    | spl13_1195 ),
    inference(avatar_split_clause,[],[f11032,f10996,f11042])).

fof(f11042,plain,
    ( spl13_1201
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1201])])).

fof(f11032,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK10(o_0_0_xboole_0))
    | ~ spl13_1195 ),
    inference(unit_resulting_resolution,[],[f10997,f126])).

fof(f11029,plain,
    ( ~ spl13_1199
    | spl13_1191 ),
    inference(avatar_split_clause,[],[f11017,f10982,f11027])).

fof(f11027,plain,
    ( spl13_1199
  <=> ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1199])])).

fof(f11017,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1191 ),
    inference(unit_resulting_resolution,[],[f10983,f126])).

fof(f11005,plain,
    ( ~ spl13_1197
    | spl13_705 ),
    inference(avatar_split_clause,[],[f9801,f5562,f11003])).

fof(f11003,plain,
    ( spl13_1197
  <=> ~ r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1197])])).

fof(f9801,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_705 ),
    inference(unit_resulting_resolution,[],[f119,f5563,f130])).

fof(f10998,plain,
    ( ~ spl13_1195
    | ~ spl13_234
    | spl13_1059 ),
    inference(avatar_split_clause,[],[f9826,f9796,f1660,f10996])).

fof(f9826,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK10(o_0_0_xboole_0)))
    | ~ spl13_234
    | ~ spl13_1059 ),
    inference(unit_resulting_resolution,[],[f1661,f9797,f130])).

fof(f10991,plain,
    ( ~ spl13_1193
    | spl13_1057 ),
    inference(avatar_split_clause,[],[f9821,f9769,f10989])).

fof(f10989,plain,
    ( spl13_1193
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1193])])).

fof(f9769,plain,
    ( spl13_1057
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1057])])).

fof(f9821,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1057 ),
    inference(unit_resulting_resolution,[],[f119,f9770,f130])).

fof(f9770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1057 ),
    inference(avatar_component_clause,[],[f9769])).

fof(f10984,plain,
    ( ~ spl13_1191
    | ~ spl13_498
    | spl13_1053 ),
    inference(avatar_split_clause,[],[f9781,f9545,f3757,f10982])).

fof(f9545,plain,
    ( spl13_1053
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1053])])).

fof(f9781,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_498
    | ~ spl13_1053 ),
    inference(unit_resulting_resolution,[],[f9546,f3758,f130])).

fof(f9546,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1053 ),
    inference(avatar_component_clause,[],[f9545])).

fof(f10977,plain,
    ( ~ spl13_1189
    | ~ spl13_404
    | spl13_921 ),
    inference(avatar_split_clause,[],[f9252,f7182,f3036,f10975])).

fof(f10975,plain,
    ( spl13_1189
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK10(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1189])])).

fof(f7182,plain,
    ( spl13_921
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_921])])).

fof(f9252,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK10(o_0_0_xboole_0))))
    | ~ spl13_404
    | ~ spl13_921 ),
    inference(backward_demodulation,[],[f3037,f7183])).

fof(f7183,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK3)))))
    | ~ spl13_921 ),
    inference(avatar_component_clause,[],[f7182])).

fof(f10970,plain,
    ( spl13_1186
    | ~ spl13_404
    | ~ spl13_904 ),
    inference(avatar_split_clause,[],[f9242,f6924,f3036,f10968])).

fof(f10968,plain,
    ( spl13_1186
  <=> r2_hidden(sK10(sK10(o_0_0_xboole_0)),sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1186])])).

fof(f6924,plain,
    ( spl13_904
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK10(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_904])])).

fof(f9242,plain,
    ( r2_hidden(sK10(sK10(o_0_0_xboole_0)),sK10(o_0_0_xboole_0))
    | ~ spl13_404
    | ~ spl13_904 ),
    inference(backward_demodulation,[],[f3037,f6925])).

fof(f6925,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_904 ),
    inference(avatar_component_clause,[],[f6924])).

fof(f10957,plain,
    ( ~ spl13_1185
    | ~ spl13_404
    | spl13_903 ),
    inference(avatar_split_clause,[],[f9241,f6917,f3036,f10955])).

fof(f10955,plain,
    ( spl13_1185
  <=> ~ r2_hidden(sK10(o_0_0_xboole_0),sK10(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1185])])).

fof(f6917,plain,
    ( spl13_903
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(sK3)),sK10(sK10(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_903])])).

fof(f9241,plain,
    ( ~ r2_hidden(sK10(o_0_0_xboole_0),sK10(sK10(o_0_0_xboole_0)))
    | ~ spl13_404
    | ~ spl13_903 ),
    inference(backward_demodulation,[],[f3037,f6918])).

fof(f6918,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(sK3)),sK10(sK10(k1_zfmisc_1(sK3))))
    | ~ spl13_903 ),
    inference(avatar_component_clause,[],[f6917])).

fof(f10932,plain,
    ( ~ spl13_1183
    | spl13_1173 ),
    inference(avatar_split_clause,[],[f10851,f10822,f10930])).

fof(f10930,plain,
    ( spl13_1183
  <=> ~ r2_hidden(sK10(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1183])])).

fof(f10822,plain,
    ( spl13_1173
  <=> ~ m1_subset_1(sK10(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1173])])).

fof(f10851,plain,
    ( ~ r2_hidden(sK10(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1173 ),
    inference(unit_resulting_resolution,[],[f10823,f121])).

fof(f10823,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1173 ),
    inference(avatar_component_clause,[],[f10822])).

fof(f10925,plain,
    ( ~ spl13_1181
    | spl13_1171 ),
    inference(avatar_split_clause,[],[f10833,f10815,f10923])).

fof(f10923,plain,
    ( spl13_1181
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1181])])).

fof(f10815,plain,
    ( spl13_1171
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1171])])).

fof(f10833,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1171 ),
    inference(unit_resulting_resolution,[],[f10816,f121])).

fof(f10816,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_1171 ),
    inference(avatar_component_clause,[],[f10815])).

fof(f10912,plain,
    ( ~ spl13_1179
    | spl13_1147 ),
    inference(avatar_split_clause,[],[f10827,f10674,f10910])).

fof(f10910,plain,
    ( spl13_1179
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1179])])).

fof(f10674,plain,
    ( spl13_1147
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1147])])).

fof(f10827,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1147 ),
    inference(unit_resulting_resolution,[],[f10675,f121])).

fof(f10675,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1147 ),
    inference(avatar_component_clause,[],[f10674])).

fof(f10905,plain,
    ( ~ spl13_1177
    | spl13_233
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f10729,f3036,f1591,f10903])).

fof(f10903,plain,
    ( spl13_1177
  <=> ~ r1_tarski(sK6(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1177])])).

fof(f1591,plain,
    ( spl13_233
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_233])])).

fof(f10729,plain,
    ( ~ r1_tarski(sK6(sK0,sK1,sK3),sK3)
    | ~ spl13_233
    | ~ spl13_404 ),
    inference(unit_resulting_resolution,[],[f1592,f9670])).

fof(f9670,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | m1_subset_1(X0,o_0_0_xboole_0) )
    | ~ spl13_404 ),
    inference(superposition,[],[f126,f3037])).

fof(f1592,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),o_0_0_xboole_0)
    | ~ spl13_233 ),
    inference(avatar_component_clause,[],[f1591])).

fof(f10873,plain,
    ( spl13_323
    | ~ spl13_750
    | spl13_765 ),
    inference(avatar_contradiction_clause,[],[f10872])).

fof(f10872,plain,
    ( $false
    | ~ spl13_323
    | ~ spl13_750
    | ~ spl13_765 ),
    inference(subsumption_resolution,[],[f10863,f5995])).

fof(f5995,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_765 ),
    inference(avatar_component_clause,[],[f5994])).

fof(f5994,plain,
    ( spl13_765
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_765])])).

fof(f10863,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_323
    | ~ spl13_750 ),
    inference(resolution,[],[f5918,f9357])).

fof(f9357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | r2_hidden(X0,sK3) )
    | ~ spl13_323 ),
    inference(resolution,[],[f2370,f122])).

fof(f2370,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_323 ),
    inference(avatar_component_clause,[],[f2369])).

fof(f2369,plain,
    ( spl13_323
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_323])])).

fof(f5918,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_750 ),
    inference(avatar_component_clause,[],[f5917])).

fof(f5917,plain,
    ( spl13_750
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_750])])).

fof(f10871,plain,
    ( spl13_323
    | ~ spl13_750
    | spl13_765 ),
    inference(avatar_contradiction_clause,[],[f10870])).

fof(f10870,plain,
    ( $false
    | ~ spl13_323
    | ~ spl13_750
    | ~ spl13_765 ),
    inference(subsumption_resolution,[],[f10857,f5995])).

fof(f10857,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_323
    | ~ spl13_750 ),
    inference(unit_resulting_resolution,[],[f5918,f9357])).

fof(f10869,plain,
    ( spl13_323
    | ~ spl13_750
    | spl13_765 ),
    inference(avatar_contradiction_clause,[],[f10868])).

fof(f10868,plain,
    ( $false
    | ~ spl13_323
    | ~ spl13_750
    | ~ spl13_765 ),
    inference(subsumption_resolution,[],[f10858,f5995])).

fof(f10858,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_323
    | ~ spl13_750 ),
    inference(unit_resulting_resolution,[],[f2370,f5918,f122])).

fof(f10867,plain,
    ( ~ spl13_6
    | ~ spl13_750
    | spl13_765
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f10866])).

fof(f10866,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_750
    | ~ spl13_765
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f10859,f5995])).

fof(f10859,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_6
    | ~ spl13_750
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f162,f7409,f5918,f431])).

fof(f431,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | X1 = X2
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f122,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t8_boole)).

fof(f7409,plain,
    ( o_0_0_xboole_0 != sK3
    | ~ spl13_941 ),
    inference(avatar_component_clause,[],[f7408])).

fof(f7408,plain,
    ( spl13_941
  <=> o_0_0_xboole_0 != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_941])])).

fof(f10865,plain,
    ( ~ spl13_6
    | ~ spl13_750
    | spl13_765
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f10864])).

fof(f10864,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_750
    | ~ spl13_765
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f10860,f5995])).

fof(f10860,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_6
    | ~ spl13_750
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f7409,f5918,f432])).

fof(f10848,plain,
    ( ~ spl13_1175
    | spl13_1171 ),
    inference(avatar_split_clause,[],[f10831,f10815,f10846])).

fof(f10846,plain,
    ( spl13_1175
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1175])])).

fof(f10831,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_1171 ),
    inference(unit_resulting_resolution,[],[f10816,f126])).

fof(f10824,plain,
    ( ~ spl13_1173
    | ~ spl13_6
    | spl13_681 ),
    inference(avatar_split_clause,[],[f10059,f5229,f161,f10822])).

fof(f5229,plain,
    ( spl13_681
  <=> o_0_0_xboole_0 != sK10(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_681])])).

fof(f10059,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_681 ),
    inference(unit_resulting_resolution,[],[f162,f119,f5230,f837])).

fof(f5230,plain,
    ( o_0_0_xboole_0 != sK10(u1_struct_0(sK1))
    | ~ spl13_681 ),
    inference(avatar_component_clause,[],[f5229])).

fof(f10817,plain,
    ( ~ spl13_1171
    | ~ spl13_234
    | spl13_699 ),
    inference(avatar_split_clause,[],[f9683,f5513,f1660,f10815])).

fof(f9683,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_234
    | ~ spl13_699 ),
    inference(unit_resulting_resolution,[],[f1661,f5514,f130])).

fof(f10804,plain,
    ( ~ spl13_1169
    | ~ spl13_404
    | spl13_1013 ),
    inference(avatar_split_clause,[],[f10732,f8061,f3036,f10802])).

fof(f10802,plain,
    ( spl13_1169
  <=> ~ r1_tarski(sK10(sK4(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1169])])).

fof(f8061,plain,
    ( spl13_1013
  <=> ~ m1_subset_1(sK10(sK4(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1013])])).

fof(f10732,plain,
    ( ~ r1_tarski(sK10(sK4(sK1)),sK3)
    | ~ spl13_404
    | ~ spl13_1013 ),
    inference(unit_resulting_resolution,[],[f8062,f9670])).

fof(f8062,plain,
    ( ~ m1_subset_1(sK10(sK4(sK1)),o_0_0_xboole_0)
    | ~ spl13_1013 ),
    inference(avatar_component_clause,[],[f8061])).

fof(f10797,plain,
    ( ~ spl13_1167
    | ~ spl13_404
    | spl13_871 ),
    inference(avatar_split_clause,[],[f10734,f6577,f3036,f10795])).

fof(f10795,plain,
    ( spl13_1167
  <=> ~ r1_tarski(sK10(sK10(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1167])])).

fof(f6577,plain,
    ( spl13_871
  <=> ~ m1_subset_1(sK10(sK10(sK3)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_871])])).

fof(f10734,plain,
    ( ~ r1_tarski(sK10(sK10(sK3)),sK3)
    | ~ spl13_404
    | ~ spl13_871 ),
    inference(unit_resulting_resolution,[],[f6578,f9670])).

fof(f6578,plain,
    ( ~ m1_subset_1(sK10(sK10(sK3)),o_0_0_xboole_0)
    | ~ spl13_871 ),
    inference(avatar_component_clause,[],[f6577])).

fof(f10790,plain,
    ( ~ spl13_1165
    | ~ spl13_404
    | spl13_815 ),
    inference(avatar_split_clause,[],[f10733,f6273,f3036,f10788])).

fof(f10788,plain,
    ( spl13_1165
  <=> ~ r1_tarski(sK10(sK10(sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1165])])).

fof(f6273,plain,
    ( spl13_815
  <=> ~ m1_subset_1(sK10(sK10(sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_815])])).

fof(f10733,plain,
    ( ~ r1_tarski(sK10(sK10(sK2)),sK3)
    | ~ spl13_404
    | ~ spl13_815 ),
    inference(unit_resulting_resolution,[],[f6274,f9670])).

fof(f6274,plain,
    ( ~ m1_subset_1(sK10(sK10(sK2)),o_0_0_xboole_0)
    | ~ spl13_815 ),
    inference(avatar_component_clause,[],[f6273])).

fof(f10778,plain,
    ( ~ spl13_1163
    | ~ spl13_404
    | spl13_687 ),
    inference(avatar_split_clause,[],[f10730,f5275,f3036,f10776])).

fof(f10776,plain,
    ( spl13_1163
  <=> ~ r1_tarski(sK10(u1_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1163])])).

fof(f5275,plain,
    ( spl13_687
  <=> ~ m1_subset_1(sK10(u1_struct_0(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_687])])).

fof(f10730,plain,
    ( ~ r1_tarski(sK10(u1_struct_0(sK1)),sK3)
    | ~ spl13_404
    | ~ spl13_687 ),
    inference(unit_resulting_resolution,[],[f5276,f9670])).

fof(f5276,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl13_687 ),
    inference(avatar_component_clause,[],[f5275])).

fof(f10771,plain,
    ( ~ spl13_1161
    | spl13_311
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f10726,f3036,f2291,f10769])).

fof(f10769,plain,
    ( spl13_1161
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1161])])).

fof(f2291,plain,
    ( spl13_311
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_311])])).

fof(f10726,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK3)
    | ~ spl13_311
    | ~ spl13_404 ),
    inference(unit_resulting_resolution,[],[f2292,f9670])).

fof(f2292,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl13_311 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f10764,plain,
    ( ~ spl13_1159
    | ~ spl13_404
    | spl13_969 ),
    inference(avatar_split_clause,[],[f10727,f7744,f3036,f10762])).

fof(f10762,plain,
    ( spl13_1159
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1159])])).

fof(f7744,plain,
    ( spl13_969
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_969])])).

fof(f10727,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK3)
    | ~ spl13_404
    | ~ spl13_969 ),
    inference(unit_resulting_resolution,[],[f7745,f9670])).

fof(f7745,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl13_969 ),
    inference(avatar_component_clause,[],[f7744])).

fof(f10757,plain,
    ( ~ spl13_1157
    | spl13_391
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f10731,f3036,f2913,f10755])).

fof(f10755,plain,
    ( spl13_1157
  <=> ~ r1_tarski(sK10(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1157])])).

fof(f2913,plain,
    ( spl13_391
  <=> ~ m1_subset_1(sK10(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_391])])).

fof(f10731,plain,
    ( ~ r1_tarski(sK10(sK3),sK3)
    | ~ spl13_391
    | ~ spl13_404 ),
    inference(unit_resulting_resolution,[],[f2914,f9670])).

fof(f2914,plain,
    ( ~ m1_subset_1(sK10(sK3),o_0_0_xboole_0)
    | ~ spl13_391 ),
    inference(avatar_component_clause,[],[f2913])).

fof(f10750,plain,
    ( ~ spl13_1155
    | spl13_237
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f10728,f3036,f1707,f10748])).

fof(f10748,plain,
    ( spl13_1155
  <=> ~ r1_tarski(sK4(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1155])])).

fof(f1707,plain,
    ( spl13_237
  <=> ~ m1_subset_1(sK4(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_237])])).

fof(f10728,plain,
    ( ~ r1_tarski(sK4(sK1),sK3)
    | ~ spl13_237
    | ~ spl13_404 ),
    inference(unit_resulting_resolution,[],[f1708,f9670])).

fof(f1708,plain,
    ( ~ m1_subset_1(sK4(sK1),o_0_0_xboole_0)
    | ~ spl13_237 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f10743,plain,
    ( ~ spl13_1153
    | spl13_243
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f10725,f3036,f1743,f10741])).

fof(f10741,plain,
    ( spl13_1153
  <=> ~ r1_tarski(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1153])])).

fof(f1743,plain,
    ( spl13_243
  <=> ~ m1_subset_1(u1_struct_0(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_243])])).

fof(f10725,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK3)
    | ~ spl13_243
    | ~ spl13_404 ),
    inference(unit_resulting_resolution,[],[f1744,f9670])).

fof(f1744,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),o_0_0_xboole_0)
    | ~ spl13_243 ),
    inference(avatar_component_clause,[],[f1743])).

fof(f10707,plain,
    ( ~ spl13_1151
    | spl13_1149 ),
    inference(avatar_split_clause,[],[f10698,f10693,f10705])).

fof(f10705,plain,
    ( spl13_1151
  <=> ~ r2_hidden(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1151])])).

fof(f10698,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK2)
    | ~ spl13_1149 ),
    inference(unit_resulting_resolution,[],[f10694,f121])).

fof(f10695,plain,
    ( ~ spl13_1149
    | ~ spl13_444
    | spl13_1063 ),
    inference(avatar_split_clause,[],[f10678,f9817,f3379,f10693])).

fof(f9817,plain,
    ( spl13_1063
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1063])])).

fof(f10678,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK2)
    | ~ spl13_444
    | ~ spl13_1063 ),
    inference(unit_resulting_resolution,[],[f9818,f3380])).

fof(f9818,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3)
    | ~ spl13_1063 ),
    inference(avatar_component_clause,[],[f9817])).

fof(f10676,plain,
    ( ~ spl13_1147
    | ~ spl13_6
    | ~ spl13_72
    | spl13_309 ),
    inference(avatar_split_clause,[],[f3180,f2282,f437,f161,f10674])).

fof(f2282,plain,
    ( spl13_309
  <=> k1_zfmisc_1(u1_struct_0(sK1)) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_309])])).

fof(f3180,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_72
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f162,f438,f2283,f837])).

fof(f2283,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != o_0_0_xboole_0
    | ~ spl13_309 ),
    inference(avatar_component_clause,[],[f2282])).

fof(f10638,plain,
    ( ~ spl13_1145
    | spl13_1053 ),
    inference(avatar_split_clause,[],[f9549,f9545,f10636])).

fof(f10636,plain,
    ( spl13_1145
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1145])])).

fof(f9549,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_1053 ),
    inference(unit_resulting_resolution,[],[f119,f9546,f130])).

fof(f10587,plain,
    ( ~ spl13_1143
    | ~ spl13_404
    | spl13_989 ),
    inference(avatar_split_clause,[],[f9270,f7868,f3036,f10585])).

fof(f10585,plain,
    ( spl13_1143
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1143])])).

fof(f7868,plain,
    ( spl13_989
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_989])])).

fof(f9270,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_404
    | ~ spl13_989 ),
    inference(backward_demodulation,[],[f3037,f7869])).

fof(f7869,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_989 ),
    inference(avatar_component_clause,[],[f7868])).

fof(f10555,plain,
    ( ~ spl13_1141
    | ~ spl13_6
    | spl13_963 ),
    inference(avatar_split_clause,[],[f7715,f7693,f161,f10553])).

fof(f10553,plain,
    ( spl13_1141
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1141])])).

fof(f7715,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_963 ),
    inference(unit_resulting_resolution,[],[f162,f119,f7694,f837])).

fof(f10538,plain,
    ( ~ spl13_1139
    | spl13_1133 ),
    inference(avatar_split_clause,[],[f10512,f10501,f10536])).

fof(f10536,plain,
    ( spl13_1139
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1139])])).

fof(f10512,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl13_1133 ),
    inference(unit_resulting_resolution,[],[f10502,f121])).

fof(f10529,plain,
    ( ~ spl13_1137
    | spl13_957 ),
    inference(avatar_split_clause,[],[f7679,f7625,f10527])).

fof(f10527,plain,
    ( spl13_1137
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1137])])).

fof(f7625,plain,
    ( spl13_957
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_957])])).

fof(f7679,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_957 ),
    inference(unit_resulting_resolution,[],[f119,f7631])).

fof(f7631,plain,
    ( ! [X0] :
        ( ~ r2_hidden(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | ~ spl13_957 ),
    inference(resolution,[],[f7626,f130])).

fof(f7626,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK2)
    | ~ spl13_957 ),
    inference(avatar_component_clause,[],[f7625])).

fof(f10522,plain,
    ( ~ spl13_1135
    | spl13_1133 ),
    inference(avatar_split_clause,[],[f10510,f10501,f10520])).

fof(f10520,plain,
    ( spl13_1135
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1135])])).

fof(f10510,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),sK2)
    | ~ spl13_1133 ),
    inference(unit_resulting_resolution,[],[f10502,f126])).

fof(f10503,plain,
    ( ~ spl13_1133
    | ~ spl13_234
    | spl13_957 ),
    inference(avatar_split_clause,[],[f9499,f7625,f1660,f10501])).

fof(f9499,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl13_234
    | ~ spl13_957 ),
    inference(unit_resulting_resolution,[],[f7626,f1661,f130])).

fof(f10496,plain,
    ( ~ spl13_1131
    | ~ spl13_404
    | spl13_481 ),
    inference(avatar_split_clause,[],[f9206,f3678,f3036,f10494])).

fof(f10494,plain,
    ( spl13_1131
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1131])])).

fof(f3678,plain,
    ( spl13_481
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_481])])).

fof(f9206,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_404
    | ~ spl13_481 ),
    inference(backward_demodulation,[],[f3037,f3679])).

fof(f3679,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_481 ),
    inference(avatar_component_clause,[],[f3678])).

fof(f10481,plain,
    ( ~ spl13_1129
    | ~ spl13_404
    | spl13_475 ),
    inference(avatar_split_clause,[],[f9203,f3643,f3036,f10479])).

fof(f3643,plain,
    ( spl13_475
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_475])])).

fof(f9203,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_404
    | ~ spl13_475 ),
    inference(backward_demodulation,[],[f3037,f3644])).

fof(f3644,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_475 ),
    inference(avatar_component_clause,[],[f3643])).

fof(f10461,plain,
    ( ~ spl13_1127
    | spl13_1115 ),
    inference(avatar_split_clause,[],[f10395,f10337,f10459])).

fof(f10459,plain,
    ( spl13_1127
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1127])])).

fof(f10395,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1115 ),
    inference(unit_resulting_resolution,[],[f10338,f121])).

fof(f10454,plain,
    ( ~ spl13_1125
    | spl13_1113 ),
    inference(avatar_split_clause,[],[f10381,f10330,f10452])).

fof(f10452,plain,
    ( spl13_1125
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1125])])).

fof(f10381,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_1113 ),
    inference(unit_resulting_resolution,[],[f10331,f121])).

fof(f10447,plain,
    ( ~ spl13_1123
    | ~ spl13_404
    | spl13_927 ),
    inference(avatar_split_clause,[],[f9256,f7263,f3036,f10445])).

fof(f10445,plain,
    ( spl13_1123
  <=> ~ r2_hidden(sK3,sK10(sK10(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1123])])).

fof(f7263,plain,
    ( spl13_927
  <=> ~ r2_hidden(sK3,sK10(sK10(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_927])])).

fof(f9256,plain,
    ( ~ r2_hidden(sK3,sK10(sK10(o_0_0_xboole_0)))
    | ~ spl13_404
    | ~ spl13_927 ),
    inference(backward_demodulation,[],[f3037,f7264])).

fof(f7264,plain,
    ( ~ r2_hidden(sK3,sK10(sK10(k1_zfmisc_1(sK3))))
    | ~ spl13_927 ),
    inference(avatar_component_clause,[],[f7263])).

fof(f10409,plain,
    ( ~ spl13_1121
    | spl13_1115 ),
    inference(avatar_split_clause,[],[f10392,f10337,f10407])).

fof(f10407,plain,
    ( spl13_1121
  <=> ~ r1_tarski(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1121])])).

fof(f10392,plain,
    ( ~ r1_tarski(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1115 ),
    inference(unit_resulting_resolution,[],[f10338,f126])).

fof(f10391,plain,
    ( ~ spl13_1119
    | spl13_1113 ),
    inference(avatar_split_clause,[],[f10379,f10330,f10389])).

fof(f10389,plain,
    ( spl13_1119
  <=> ~ r1_tarski(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1119])])).

fof(f10379,plain,
    ( ~ r1_tarski(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1113 ),
    inference(unit_resulting_resolution,[],[f10331,f126])).

fof(f10350,plain,
    ( ~ spl13_1117
    | ~ spl13_6
    | spl13_239
    | spl13_1101 ),
    inference(avatar_split_clause,[],[f10275,f10244,f1718,f161,f10348])).

fof(f1718,plain,
    ( spl13_239
  <=> o_0_0_xboole_0 != sK10(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_239])])).

fof(f10244,plain,
    ( spl13_1101
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1101])])).

fof(f10275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_239
    | ~ spl13_1101 ),
    inference(unit_resulting_resolution,[],[f1719,f10245,f432])).

fof(f10245,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(o_0_0_xboole_0))
    | ~ spl13_1101 ),
    inference(avatar_component_clause,[],[f10244])).

fof(f1719,plain,
    ( o_0_0_xboole_0 != sK10(o_0_0_xboole_0)
    | ~ spl13_239 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f10339,plain,
    ( ~ spl13_1115
    | ~ spl13_344
    | spl13_1093 ),
    inference(avatar_split_clause,[],[f10249,f10211,f2519,f10337])).

fof(f10249,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_344
    | ~ spl13_1093 ),
    inference(unit_resulting_resolution,[],[f2520,f10212,f130])).

fof(f10332,plain,
    ( ~ spl13_1113
    | ~ spl13_328
    | spl13_1093 ),
    inference(avatar_split_clause,[],[f10248,f10211,f2416,f10330])).

fof(f10248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_328
    | ~ spl13_1093 ),
    inference(unit_resulting_resolution,[],[f2417,f10212,f130])).

fof(f10325,plain,
    ( ~ spl13_1111
    | ~ spl13_404
    | spl13_939 ),
    inference(avatar_split_clause,[],[f9264,f7404,f3036,f10323])).

fof(f7404,plain,
    ( spl13_939
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_939])])).

fof(f9264,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_404
    | ~ spl13_939 ),
    inference(backward_demodulation,[],[f3037,f7405])).

fof(f7405,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_939 ),
    inference(avatar_component_clause,[],[f7404])).

fof(f10318,plain,
    ( spl13_1108
    | ~ spl13_404
    | ~ spl13_924 ),
    inference(avatar_split_clause,[],[f9255,f7240,f3036,f10316])).

fof(f10316,plain,
    ( spl13_1108
  <=> r2_hidden(sK10(sK10(o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1108])])).

fof(f7240,plain,
    ( spl13_924
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_924])])).

fof(f9255,plain,
    ( r2_hidden(sK10(sK10(o_0_0_xboole_0)),sK3)
    | ~ spl13_404
    | ~ spl13_924 ),
    inference(backward_demodulation,[],[f3037,f7241])).

fof(f7241,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK3)
    | ~ spl13_924 ),
    inference(avatar_component_clause,[],[f7240])).

fof(f10311,plain,
    ( spl13_1106
    | ~ spl13_404
    | ~ spl13_922 ),
    inference(avatar_split_clause,[],[f9254,f7233,f3036,f10309])).

fof(f10309,plain,
    ( spl13_1106
  <=> m1_subset_1(sK10(sK10(o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1106])])).

fof(f7233,plain,
    ( spl13_922
  <=> m1_subset_1(sK10(sK10(k1_zfmisc_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_922])])).

fof(f9254,plain,
    ( m1_subset_1(sK10(sK10(o_0_0_xboole_0)),sK3)
    | ~ spl13_404
    | ~ spl13_922 ),
    inference(backward_demodulation,[],[f3037,f7234])).

fof(f7234,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK3))),sK3)
    | ~ spl13_922 ),
    inference(avatar_component_clause,[],[f7233])).

fof(f10290,plain,
    ( ~ spl13_1105
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_386 ),
    inference(avatar_split_clause,[],[f7385,f2887,f1574,f161,f10288])).

fof(f10288,plain,
    ( spl13_1105
  <=> ~ r2_hidden(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1105])])).

fof(f1574,plain,
    ( spl13_228
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_228])])).

fof(f7385,plain,
    ( ~ r2_hidden(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_386 ),
    inference(unit_resulting_resolution,[],[f210,f1575,f6826])).

fof(f6826,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK10(sK3),k1_zfmisc_1(X6))
        | ~ m1_subset_1(X5,X6)
        | r2_hidden(X5,X6) )
    | ~ spl13_386 ),
    inference(resolution,[],[f2942,f121])).

fof(f2942,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(X0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl13_386 ),
    inference(resolution,[],[f2905,f122])).

fof(f2905,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(X0)) )
    | ~ spl13_386 ),
    inference(resolution,[],[f2888,f131])).

fof(f1575,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_228 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f210,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f162,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t7_boole)).

fof(f10283,plain,
    ( ~ spl13_1103
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_366 ),
    inference(avatar_split_clause,[],[f7379,f2695,f1574,f161,f10281])).

fof(f10281,plain,
    ( spl13_1103
  <=> ~ r2_hidden(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1103])])).

fof(f7379,plain,
    ( ~ r2_hidden(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_366 ),
    inference(unit_resulting_resolution,[],[f210,f1575,f6811])).

fof(f6811,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK10(sK2),k1_zfmisc_1(X6))
        | ~ m1_subset_1(X5,X6)
        | r2_hidden(X5,X6) )
    | ~ spl13_366 ),
    inference(resolution,[],[f2790,f121])).

fof(f2790,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(X0))
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl13_366 ),
    inference(resolution,[],[f2728,f122])).

fof(f2728,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(X0)) )
    | ~ spl13_366 ),
    inference(resolution,[],[f2696,f131])).

fof(f10246,plain,
    ( ~ spl13_1101
    | ~ spl13_404
    | spl13_1061 ),
    inference(avatar_split_clause,[],[f9835,f9810,f3036,f10244])).

fof(f9835,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(o_0_0_xboole_0))
    | ~ spl13_404
    | ~ spl13_1061 ),
    inference(forward_demodulation,[],[f9831,f3037])).

fof(f9831,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_1061 ),
    inference(unit_resulting_resolution,[],[f119,f9811,f130])).

fof(f10239,plain,
    ( ~ spl13_1099
    | ~ spl13_404
    | spl13_473 ),
    inference(avatar_split_clause,[],[f9202,f3614,f3036,f10237])).

fof(f10237,plain,
    ( spl13_1099
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1099])])).

fof(f3614,plain,
    ( spl13_473
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_473])])).

fof(f9202,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_404
    | ~ spl13_473 ),
    inference(backward_demodulation,[],[f3037,f3615])).

fof(f3615,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_473 ),
    inference(avatar_component_clause,[],[f3614])).

fof(f10227,plain,
    ( ~ spl13_1097
    | ~ spl13_404
    | spl13_431 ),
    inference(avatar_split_clause,[],[f9195,f3236,f3036,f10225])).

fof(f10225,plain,
    ( spl13_1097
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1097])])).

fof(f3236,plain,
    ( spl13_431
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_431])])).

fof(f9195,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_404
    | ~ spl13_431 ),
    inference(backward_demodulation,[],[f3037,f3237])).

fof(f3237,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_431 ),
    inference(avatar_component_clause,[],[f3236])).

fof(f10220,plain,
    ( ~ spl13_1095
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_386 ),
    inference(avatar_split_clause,[],[f6823,f2887,f1574,f161,f10218])).

fof(f6823,plain,
    ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_386 ),
    inference(unit_resulting_resolution,[],[f1575,f210,f2942])).

fof(f10213,plain,
    ( ~ spl13_1093
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_366 ),
    inference(avatar_split_clause,[],[f6808,f2695,f1574,f161,f10211])).

fof(f6808,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_366 ),
    inference(unit_resulting_resolution,[],[f1575,f210,f2790])).

fof(f10186,plain,
    ( ~ spl13_1091
    | ~ spl13_404
    | spl13_465 ),
    inference(avatar_split_clause,[],[f9199,f3578,f3036,f10184])).

fof(f3578,plain,
    ( spl13_465
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_465])])).

fof(f9199,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_404
    | ~ spl13_465 ),
    inference(backward_demodulation,[],[f3037,f3579])).

fof(f3579,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_465 ),
    inference(avatar_component_clause,[],[f3578])).

fof(f10179,plain,
    ( ~ spl13_1089
    | ~ spl13_404
    | spl13_425 ),
    inference(avatar_split_clause,[],[f9191,f3209,f3036,f10177])).

fof(f3209,plain,
    ( spl13_425
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_425])])).

fof(f9191,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_404
    | ~ spl13_425 ),
    inference(backward_demodulation,[],[f3037,f3210])).

fof(f3210,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_425 ),
    inference(avatar_component_clause,[],[f3209])).

fof(f10106,plain,
    ( ~ spl13_1087
    | spl13_1081 ),
    inference(avatar_split_clause,[],[f10047,f10006,f10104])).

fof(f10104,plain,
    ( spl13_1087
  <=> ~ r2_hidden(sK10(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1087])])).

fof(f10047,plain,
    ( ~ r2_hidden(sK10(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1081 ),
    inference(unit_resulting_resolution,[],[f10007,f121])).

fof(f10099,plain,
    ( ~ spl13_1085
    | spl13_1079 ),
    inference(avatar_split_clause,[],[f10011,f9999,f10097])).

fof(f10097,plain,
    ( spl13_1085
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1085])])).

fof(f10011,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1079 ),
    inference(unit_resulting_resolution,[],[f10000,f121])).

fof(f10044,plain,
    ( ~ spl13_1083
    | spl13_1079 ),
    inference(avatar_split_clause,[],[f10009,f9999,f10042])).

fof(f10042,plain,
    ( spl13_1083
  <=> ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1083])])).

fof(f10009,plain,
    ( ~ r1_tarski(k1_zfmisc_1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl13_1079 ),
    inference(unit_resulting_resolution,[],[f10000,f126])).

fof(f10008,plain,
    ( ~ spl13_1081
    | ~ spl13_6
    | spl13_239 ),
    inference(avatar_split_clause,[],[f9518,f1718,f161,f10006])).

fof(f9518,plain,
    ( ~ m1_subset_1(sK10(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_239 ),
    inference(unit_resulting_resolution,[],[f162,f119,f1719,f837])).

fof(f10001,plain,
    ( ~ spl13_1079
    | ~ spl13_6
    | ~ spl13_234 ),
    inference(avatar_split_clause,[],[f9500,f1660,f161,f9999])).

fof(f9500,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_234 ),
    inference(unit_resulting_resolution,[],[f162,f1661,f131])).

fof(f9931,plain,
    ( spl13_970
    | ~ spl13_960
    | spl13_967 ),
    inference(avatar_split_clause,[],[f7735,f7732,f7658,f7751])).

fof(f7658,plain,
    ( spl13_960
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_960])])).

fof(f7735,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_960
    | ~ spl13_967 ),
    inference(unit_resulting_resolution,[],[f7659,f7733,f122])).

fof(f7659,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_960 ),
    inference(avatar_component_clause,[],[f7658])).

fof(f9930,plain,
    ( ~ spl13_1077
    | ~ spl13_404
    | spl13_479 ),
    inference(avatar_split_clause,[],[f9205,f3663,f3036,f9928])).

fof(f9928,plain,
    ( spl13_1077
  <=> ~ r1_tarski(o_0_0_xboole_0,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1077])])).

fof(f3663,plain,
    ( spl13_479
  <=> ~ r1_tarski(k1_zfmisc_1(sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_479])])).

fof(f9205,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK4(sK1))
    | ~ spl13_404
    | ~ spl13_479 ),
    inference(backward_demodulation,[],[f3037,f3664])).

fof(f3664,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_479 ),
    inference(avatar_component_clause,[],[f3663])).

fof(f9918,plain,
    ( ~ spl13_1075
    | ~ spl13_404
    | spl13_551 ),
    inference(avatar_split_clause,[],[f9218,f4063,f3036,f9916])).

fof(f4063,plain,
    ( spl13_551
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_551])])).

fof(f9218,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(sK1))
    | ~ spl13_404
    | ~ spl13_551 ),
    inference(backward_demodulation,[],[f3037,f4064])).

fof(f4064,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_551 ),
    inference(avatar_component_clause,[],[f4063])).

fof(f9906,plain,
    ( ~ spl13_1073
    | ~ spl13_404
    | spl13_543 ),
    inference(avatar_split_clause,[],[f9216,f4012,f3036,f9904])).

fof(f9904,plain,
    ( spl13_1073
  <=> ~ r2_hidden(o_0_0_xboole_0,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1073])])).

fof(f4012,plain,
    ( spl13_543
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_543])])).

fof(f9216,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK4(sK1))
    | ~ spl13_404
    | ~ spl13_543 ),
    inference(backward_demodulation,[],[f3037,f4013])).

fof(f4013,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_543 ),
    inference(avatar_component_clause,[],[f4012])).

fof(f9891,plain,
    ( ~ spl13_1071
    | ~ spl13_404
    | spl13_901 ),
    inference(avatar_split_clause,[],[f9239,f6906,f3036,f9889])).

fof(f9889,plain,
    ( spl13_1071
  <=> ~ r1_tarski(sK10(o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1071])])).

fof(f6906,plain,
    ( spl13_901
  <=> ~ r1_tarski(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_901])])).

fof(f9239,plain,
    ( ~ r1_tarski(sK10(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl13_404
    | ~ spl13_901 ),
    inference(backward_demodulation,[],[f3037,f6907])).

fof(f6907,plain,
    ( ~ r1_tarski(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0)
    | ~ spl13_901 ),
    inference(avatar_component_clause,[],[f6906])).

fof(f9861,plain,
    ( ~ spl13_1069
    | spl13_1057 ),
    inference(avatar_split_clause,[],[f9822,f9769,f9859])).

fof(f9859,plain,
    ( spl13_1069
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1069])])).

fof(f9822,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1057 ),
    inference(unit_resulting_resolution,[],[f9770,f121])).

fof(f9854,plain,
    ( ~ spl13_1067
    | ~ spl13_404
    | spl13_471 ),
    inference(avatar_split_clause,[],[f9201,f3605,f3036,f9852])).

fof(f9852,plain,
    ( spl13_1067
  <=> ~ r1_tarski(o_0_0_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1067])])).

fof(f3605,plain,
    ( spl13_471
  <=> ~ r1_tarski(k1_zfmisc_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_471])])).

fof(f9201,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_404
    | ~ spl13_471 ),
    inference(backward_demodulation,[],[f3037,f3606])).

fof(f3606,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),u1_struct_0(sK1))
    | ~ spl13_471 ),
    inference(avatar_component_clause,[],[f3605])).

fof(f9847,plain,
    ( ~ spl13_1065
    | ~ spl13_404
    | spl13_427 ),
    inference(avatar_split_clause,[],[f9193,f3222,f3036,f9845])).

fof(f9845,plain,
    ( spl13_1065
  <=> ~ r1_tarski(o_0_0_xboole_0,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1065])])).

fof(f3222,plain,
    ( spl13_427
  <=> ~ r1_tarski(k1_zfmisc_1(sK3),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_427])])).

fof(f9193,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK10(sK2))
    | ~ spl13_404
    | ~ spl13_427 ),
    inference(backward_demodulation,[],[f3037,f3223])).

fof(f3223,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),sK10(sK2))
    | ~ spl13_427 ),
    inference(avatar_component_clause,[],[f3222])).

fof(f9819,plain,
    ( ~ spl13_1063
    | ~ spl13_6
    | spl13_199
    | ~ spl13_492 ),
    inference(avatar_split_clause,[],[f9743,f3732,f1155,f161,f9817])).

fof(f1155,plain,
    ( spl13_199
  <=> u1_struct_0(sK1) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_199])])).

fof(f9743,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3)
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_492 ),
    inference(unit_resulting_resolution,[],[f1156,f3733,f838])).

fof(f1156,plain,
    ( u1_struct_0(sK1) != o_0_0_xboole_0
    | ~ spl13_199 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f9812,plain,
    ( ~ spl13_1061
    | ~ spl13_6
    | spl13_201
    | ~ spl13_492
    | spl13_941 ),
    inference(avatar_split_clause,[],[f9726,f7408,f3732,f1183,f161,f9810])).

fof(f1183,plain,
    ( spl13_201
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_201])])).

fof(f9726,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl13_6
    | ~ spl13_201
    | ~ spl13_492
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f7409,f3733,f1865])).

fof(f1865,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),X0)
        | o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_6
    | ~ spl13_201 ),
    inference(resolution,[],[f1598,f838])).

fof(f1598,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_201 ),
    inference(resolution,[],[f1184,f122])).

fof(f1184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_201 ),
    inference(avatar_component_clause,[],[f1183])).

fof(f9798,plain,
    ( ~ spl13_1059
    | ~ spl13_404
    | spl13_895 ),
    inference(avatar_split_clause,[],[f9236,f6844,f3036,f9796])).

fof(f6844,plain,
    ( spl13_895
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_895])])).

fof(f9236,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK10(o_0_0_xboole_0))
    | ~ spl13_404
    | ~ spl13_895 ),
    inference(backward_demodulation,[],[f3037,f6845])).

fof(f6845,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_895 ),
    inference(avatar_component_clause,[],[f6844])).

fof(f9771,plain,
    ( ~ spl13_1057
    | ~ spl13_6
    | spl13_443 ),
    inference(avatar_split_clause,[],[f3388,f3373,f161,f9769])).

fof(f3388,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f162,f119,f3374,f837])).

fof(f9751,plain,
    ( spl13_328
    | ~ spl13_6
    | spl13_443 ),
    inference(avatar_split_clause,[],[f3386,f3373,f161,f2416])).

fof(f3386,plain,
    ( r2_hidden(sK10(sK2),sK2)
    | ~ spl13_6
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f119,f3374,f432])).

fof(f9636,plain,
    ( ~ spl13_1055
    | spl13_1053 ),
    inference(avatar_split_clause,[],[f9550,f9545,f9634])).

fof(f9634,plain,
    ( spl13_1055
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1055])])).

fof(f9550,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_1053 ),
    inference(unit_resulting_resolution,[],[f9546,f121])).

fof(f9547,plain,
    ( ~ spl13_1053
    | ~ spl13_6
    | spl13_941 ),
    inference(avatar_split_clause,[],[f9411,f7408,f161,f9545])).

fof(f9411,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f162,f119,f7409,f837])).

fof(f9512,plain,
    ( ~ spl13_1051
    | ~ spl13_234 ),
    inference(avatar_split_clause,[],[f9498,f1660,f9510])).

fof(f9510,plain,
    ( spl13_1051
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1051])])).

fof(f9498,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_234 ),
    inference(unit_resulting_resolution,[],[f1661,f128])).

fof(f9493,plain,
    ( ~ spl13_699
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | spl13_711 ),
    inference(avatar_split_clause,[],[f9345,f5586,f285,f182,f154,f147,f140,f5513])).

fof(f5586,plain,
    ( spl13_711
  <=> ~ r1_orders_2(sK1,o_0_0_xboole_0,sK8(sK0,sK1,sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_711])])).

fof(f9345,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9344,f141])).

fof(f9344,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9343,f148])).

fof(f9343,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9342,f155])).

fof(f9342,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9318,f183])).

fof(f9318,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f5665,f286])).

fof(f5665,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_711 ),
    inference(resolution,[],[f5587,f117])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f5587,plain,
    ( ~ r1_orders_2(sK1,o_0_0_xboole_0,sK8(sK0,sK1,sK2,o_0_0_xboole_0))
    | ~ spl13_711 ),
    inference(avatar_component_clause,[],[f5586])).

fof(f9471,plain,
    ( ~ spl13_1049
    | ~ spl13_404
    | spl13_897 ),
    inference(avatar_split_clause,[],[f9237,f6873,f3036,f9469])).

fof(f9469,plain,
    ( spl13_1049
  <=> ~ v1_xboole_0(sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1049])])).

fof(f6873,plain,
    ( spl13_897
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_897])])).

fof(f9237,plain,
    ( ~ v1_xboole_0(sK10(o_0_0_xboole_0))
    | ~ spl13_404
    | ~ spl13_897 ),
    inference(backward_demodulation,[],[f3037,f6874])).

fof(f6874,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_897 ),
    inference(avatar_component_clause,[],[f6873])).

fof(f9365,plain,
    ( spl13_324
    | ~ spl13_46
    | ~ spl13_404 ),
    inference(avatar_split_clause,[],[f9181,f3036,f325,f2379])).

fof(f2379,plain,
    ( spl13_324
  <=> m1_subset_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_324])])).

fof(f325,plain,
    ( spl13_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f9181,plain,
    ( m1_subset_1(sK2,o_0_0_xboole_0)
    | ~ spl13_46
    | ~ spl13_404 ),
    inference(backward_demodulation,[],[f3037,f326])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f325])).

fof(f9358,plain,
    ( ~ spl13_321
    | ~ spl13_6
    | spl13_443 ),
    inference(avatar_split_clause,[],[f3382,f3373,f161,f2362])).

fof(f2362,plain,
    ( spl13_321
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_321])])).

fof(f3382,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl13_6
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f3374,f202])).

fof(f9355,plain,
    ( spl13_701
    | ~ spl13_736 ),
    inference(avatar_contradiction_clause,[],[f9354])).

fof(f9354,plain,
    ( $false
    | ~ spl13_701
    | ~ spl13_736 ),
    inference(subsumption_resolution,[],[f5805,f5549])).

fof(f5549,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_701 ),
    inference(avatar_component_clause,[],[f5548])).

fof(f5548,plain,
    ( spl13_701
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_701])])).

fof(f9351,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_736
    | spl13_813 ),
    inference(avatar_contradiction_clause,[],[f9350])).

fof(f9350,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_736
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f5805,f9349])).

fof(f9349,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9348,f141])).

fof(f9348,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9347,f148])).

fof(f9347,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9346,f155])).

fof(f9346,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9327,f183])).

fof(f9327,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f6818,f286])).

fof(f6818,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_813 ),
    inference(resolution,[],[f6264,f116])).

fof(f6264,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_813 ),
    inference(avatar_component_clause,[],[f6263])).

fof(f6263,plain,
    ( spl13_813
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_813])])).

fof(f9341,plain,
    ( spl13_705
    | ~ spl13_740 ),
    inference(avatar_contradiction_clause,[],[f9340])).

fof(f9340,plain,
    ( $false
    | ~ spl13_705
    | ~ spl13_740 ),
    inference(subsumption_resolution,[],[f5828,f5563])).

fof(f5828,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_740 ),
    inference(unit_resulting_resolution,[],[f5801,f121])).

fof(f5801,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_740 ),
    inference(avatar_component_clause,[],[f5800])).

fof(f5800,plain,
    ( spl13_740
  <=> r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_740])])).

fof(f9338,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_698
    | spl13_705 ),
    inference(avatar_contradiction_clause,[],[f9337])).

fof(f9337,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_698
    | ~ spl13_705 ),
    inference(subsumption_resolution,[],[f5563,f5531])).

fof(f5531,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_698 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f5517,f116])).

fof(f5517,plain,
    ( m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_698 ),
    inference(avatar_component_clause,[],[f5516])).

fof(f5516,plain,
    ( spl13_698
  <=> m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_698])])).

fof(f340,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | ~ spl13_51 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl13_51
  <=> ~ r1_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_51])])).

fof(f9333,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_700
    | spl13_813 ),
    inference(avatar_contradiction_clause,[],[f9332])).

fof(f9332,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9331,f141])).

fof(f9331,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9330,f148])).

fof(f9330,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9329,f155])).

fof(f9329,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9328,f183])).

fof(f9328,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f9327,f5552])).

fof(f5552,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_700 ),
    inference(avatar_component_clause,[],[f5551])).

fof(f9326,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_700
    | spl13_813 ),
    inference(avatar_contradiction_clause,[],[f9325])).

fof(f9325,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(subsumption_resolution,[],[f6814,f286])).

fof(f6814,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_700
    | ~ spl13_813 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f5552,f6264,f116])).

fof(f9324,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_698
    | spl13_711 ),
    inference(avatar_contradiction_clause,[],[f9323])).

fof(f9323,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9322,f141])).

fof(f9322,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9321,f148])).

fof(f9321,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9320,f155])).

fof(f9320,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9319,f183])).

fof(f9319,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f9318,f5517])).

fof(f9317,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_698
    | spl13_711 ),
    inference(avatar_contradiction_clause,[],[f9316])).

fof(f9316,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(subsumption_resolution,[],[f5664,f286])).

fof(f5664,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_698
    | ~ spl13_711 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f5517,f5587,f117])).

fof(f9315,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_698
    | spl13_703 ),
    inference(avatar_contradiction_clause,[],[f9314])).

fof(f9314,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f9313,f141])).

fof(f9313,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f9312,f148])).

fof(f9312,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f9311,f155])).

fof(f9311,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f9310,f183])).

fof(f9310,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f9309,f5517])).

fof(f9309,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_37
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f5634,f286])).

fof(f5634,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_703 ),
    inference(resolution,[],[f5559,f116])).

fof(f5559,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_703 ),
    inference(avatar_component_clause,[],[f5558])).

fof(f5558,plain,
    ( spl13_703
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_703])])).

fof(f9308,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_698
    | spl13_703 ),
    inference(avatar_contradiction_clause,[],[f9307])).

fof(f9307,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(subsumption_resolution,[],[f5630,f286])).

fof(f5630,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_698
    | ~ spl13_703 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f5517,f5559,f116])).

fof(f9305,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_704
    | spl13_841 ),
    inference(avatar_contradiction_clause,[],[f9304])).

fof(f9304,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_704
    | ~ spl13_841 ),
    inference(subsumption_resolution,[],[f286,f6998])).

fof(f6998,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_704
    | ~ spl13_841 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f5566,f6393,f116])).

fof(f6393,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_841 ),
    inference(avatar_component_clause,[],[f6392])).

fof(f6392,plain,
    ( spl13_841
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_841])])).

fof(f5566,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_704 ),
    inference(avatar_component_clause,[],[f5565])).

fof(f5565,plain,
    ( spl13_704
  <=> m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_704])])).

fof(f9303,plain,
    ( ~ spl13_72
    | ~ spl13_266
    | ~ spl13_348
    | spl13_647 ),
    inference(avatar_contradiction_clause,[],[f9302])).

fof(f9302,plain,
    ( $false
    | ~ spl13_72
    | ~ spl13_266
    | ~ spl13_348
    | ~ spl13_647 ),
    inference(subsumption_resolution,[],[f2575,f8305])).

fof(f8305,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_72
    | ~ spl13_266
    | ~ spl13_647 ),
    inference(unit_resulting_resolution,[],[f4957,f438,f2171])).

fof(f4957,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_647 ),
    inference(avatar_component_clause,[],[f4956])).

fof(f4956,plain,
    ( spl13_647
  <=> ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_647])])).

fof(f9301,plain,
    ( ~ spl13_72
    | ~ spl13_266
    | ~ spl13_352
    | spl13_651 ),
    inference(avatar_contradiction_clause,[],[f9300])).

fof(f9300,plain,
    ( $false
    | ~ spl13_72
    | ~ spl13_266
    | ~ spl13_352
    | ~ spl13_651 ),
    inference(subsumption_resolution,[],[f2618,f8306])).

fof(f8306,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_72
    | ~ spl13_266
    | ~ spl13_651 ),
    inference(unit_resulting_resolution,[],[f4971,f438,f2171])).

fof(f4971,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_651 ),
    inference(avatar_component_clause,[],[f4970])).

fof(f4970,plain,
    ( spl13_651
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_651])])).

fof(f2618,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_352 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2617,plain,
    ( spl13_352
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_352])])).

fof(f9291,plain,
    ( ~ spl13_6
    | ~ spl13_90
    | ~ spl13_404
    | ~ spl13_914 ),
    inference(avatar_contradiction_clause,[],[f9290])).

fof(f9290,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_90
    | ~ spl13_404
    | ~ spl13_914 ),
    inference(subsumption_resolution,[],[f9289,f210])).

fof(f9289,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_90
    | ~ spl13_404
    | ~ spl13_914 ),
    inference(forward_demodulation,[],[f9248,f529])).

fof(f529,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl13_90
  <=> o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f9248,plain,
    ( r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_404
    | ~ spl13_914 ),
    inference(backward_demodulation,[],[f3037,f7094])).

fof(f7094,plain,
    ( r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | ~ spl13_914 ),
    inference(avatar_component_clause,[],[f7093])).

fof(f7093,plain,
    ( spl13_914
  <=> r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_914])])).

fof(f9288,plain,
    ( ~ spl13_6
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(avatar_contradiction_clause,[],[f9287])).

fof(f9287,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(subsumption_resolution,[],[f9246,f162])).

fof(f9246,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(backward_demodulation,[],[f3037,f7078])).

fof(f7078,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl13_422 ),
    inference(resolution,[],[f3152,f128])).

fof(f3152,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
    | ~ spl13_422 ),
    inference(avatar_component_clause,[],[f3151])).

fof(f3151,plain,
    ( spl13_422
  <=> r2_hidden(sK10(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_422])])).

fof(f9286,plain,
    ( ~ spl13_6
    | ~ spl13_404
    | ~ spl13_906 ),
    inference(avatar_contradiction_clause,[],[f9285])).

fof(f9285,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_404
    | ~ spl13_906 ),
    inference(subsumption_resolution,[],[f9243,f210])).

fof(f9243,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_404
    | ~ spl13_906 ),
    inference(backward_demodulation,[],[f3037,f6976])).

fof(f6976,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl13_906 ),
    inference(avatar_component_clause,[],[f6975])).

fof(f6975,plain,
    ( spl13_906
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_906])])).

fof(f9280,plain,
    ( ~ spl13_6
    | ~ spl13_92
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(avatar_contradiction_clause,[],[f9279])).

fof(f9279,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(subsumption_resolution,[],[f9190,f545])).

fof(f545,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl13_92
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f9190,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(backward_demodulation,[],[f3037,f3159])).

fof(f3159,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_422 ),
    inference(unit_resulting_resolution,[],[f162,f3152,f131])).

fof(f9278,plain,
    ( ~ spl13_6
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(avatar_contradiction_clause,[],[f9277])).

fof(f9277,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(subsumption_resolution,[],[f9189,f210])).

fof(f9189,plain,
    ( r2_hidden(sK10(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl13_404
    | ~ spl13_422 ),
    inference(backward_demodulation,[],[f3037,f3152])).

fof(f9180,plain,
    ( ~ spl13_408
    | ~ spl13_422 ),
    inference(avatar_contradiction_clause,[],[f9179])).

fof(f9179,plain,
    ( $false
    | ~ spl13_408
    | ~ spl13_422 ),
    inference(subsumption_resolution,[],[f3062,f7078])).

fof(f3062,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl13_408 ),
    inference(avatar_component_clause,[],[f3061])).

fof(f3061,plain,
    ( spl13_408
  <=> v1_xboole_0(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_408])])).

fof(f9178,plain,
    ( spl13_643
    | ~ spl13_676 ),
    inference(avatar_contradiction_clause,[],[f9177])).

fof(f9177,plain,
    ( $false
    | ~ spl13_643
    | ~ spl13_676 ),
    inference(subsumption_resolution,[],[f4859,f5219])).

fof(f5219,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_676 ),
    inference(unit_resulting_resolution,[],[f5086,f121])).

fof(f5086,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_676 ),
    inference(avatar_component_clause,[],[f5085])).

fof(f5085,plain,
    ( spl13_676
  <=> r2_hidden(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_676])])).

fof(f4859,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_643 ),
    inference(avatar_component_clause,[],[f4858])).

fof(f4858,plain,
    ( spl13_643
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_643])])).

fof(f9176,plain,
    ( ~ spl13_960
    | spl13_967
    | spl13_971 ),
    inference(avatar_contradiction_clause,[],[f9175])).

fof(f9175,plain,
    ( $false
    | ~ spl13_960
    | ~ spl13_967
    | ~ spl13_971 ),
    inference(subsumption_resolution,[],[f7749,f7735])).

fof(f7749,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_971 ),
    inference(avatar_component_clause,[],[f7748])).

fof(f7748,plain,
    ( spl13_971
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_971])])).

fof(f9168,plain,
    ( ~ spl13_6
    | ~ spl13_320
    | spl13_443 ),
    inference(avatar_contradiction_clause,[],[f9167])).

fof(f9167,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_320
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f2360,f3382])).

fof(f2360,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_320 ),
    inference(avatar_component_clause,[],[f2359])).

fof(f2359,plain,
    ( spl13_320
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_320])])).

fof(f9166,plain,
    ( ~ spl13_6
    | spl13_329
    | spl13_443 ),
    inference(avatar_contradiction_clause,[],[f9165])).

fof(f9165,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_329
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f2414,f3386])).

fof(f2414,plain,
    ( ~ r2_hidden(sK10(sK2),sK2)
    | ~ spl13_329 ),
    inference(avatar_component_clause,[],[f2413])).

fof(f2413,plain,
    ( spl13_329
  <=> ~ r2_hidden(sK10(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_329])])).

fof(f9147,plain,
    ( ~ spl13_90
    | spl13_923
    | ~ spl13_940 ),
    inference(avatar_contradiction_clause,[],[f9146])).

fof(f9146,plain,
    ( $false
    | ~ spl13_90
    | ~ spl13_923
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f9145,f119])).

fof(f9145,plain,
    ( ~ m1_subset_1(sK10(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl13_90
    | ~ spl13_923
    | ~ spl13_940 ),
    inference(forward_demodulation,[],[f9144,f529])).

fof(f9144,plain,
    ( ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl13_923
    | ~ spl13_940 ),
    inference(forward_demodulation,[],[f7231,f7412])).

fof(f7412,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl13_940 ),
    inference(avatar_component_clause,[],[f7411])).

fof(f7411,plain,
    ( spl13_940
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_940])])).

fof(f7231,plain,
    ( ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(sK3))),sK3)
    | ~ spl13_923 ),
    inference(avatar_component_clause,[],[f7230])).

fof(f7230,plain,
    ( spl13_923
  <=> ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_923])])).

fof(f9139,plain,
    ( ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1034 ),
    inference(avatar_contradiction_clause,[],[f9138])).

fof(f9138,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1034 ),
    inference(subsumption_resolution,[],[f8945,f210])).

fof(f8945,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,sK7(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl13_940
    | ~ spl13_1034 ),
    inference(backward_demodulation,[],[f7412,f8192])).

fof(f8192,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1034 ),
    inference(avatar_component_clause,[],[f8191])).

fof(f8191,plain,
    ( spl13_1034
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1034])])).

fof(f9137,plain,
    ( ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1024 ),
    inference(avatar_contradiction_clause,[],[f9136])).

fof(f9136,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1024 ),
    inference(subsumption_resolution,[],[f8943,f210])).

fof(f8943,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,sK8(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl13_940
    | ~ spl13_1024 ),
    inference(backward_demodulation,[],[f7412,f8125])).

fof(f8125,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1024 ),
    inference(avatar_component_clause,[],[f8124])).

fof(f8124,plain,
    ( spl13_1024
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1024])])).

fof(f9135,plain,
    ( ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1016 ),
    inference(avatar_contradiction_clause,[],[f9134])).

fof(f9134,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_940
    | ~ spl13_1016 ),
    inference(subsumption_resolution,[],[f8942,f210])).

fof(f8942,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl13_940
    | ~ spl13_1016 ),
    inference(backward_demodulation,[],[f7412,f8088])).

fof(f8088,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK3)
    | ~ spl13_1016 ),
    inference(avatar_component_clause,[],[f8087])).

fof(f8087,plain,
    ( spl13_1016
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1016])])).

fof(f9071,plain,
    ( ~ spl13_6
    | ~ spl13_194
    | spl13_603
    | spl13_757
    | ~ spl13_778
    | ~ spl13_940 ),
    inference(avatar_contradiction_clause,[],[f9070])).

fof(f9070,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_194
    | ~ spl13_603
    | ~ spl13_757
    | ~ spl13_778
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f9069,f8740])).

fof(f8740,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl13_757
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f5936])).

fof(f5936,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_757 ),
    inference(avatar_component_clause,[],[f5935])).

fof(f5935,plain,
    ( spl13_757
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_757])])).

fof(f9069,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_194
    | ~ spl13_603
    | ~ spl13_778
    | ~ spl13_940 ),
    inference(forward_demodulation,[],[f8751,f8983])).

fof(f8983,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_194
    | ~ spl13_603
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f8655,f1082])).

fof(f1082,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_194 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1081,plain,
    ( spl13_194
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_194])])).

fof(f8655,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_603
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f4522])).

fof(f4522,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_603 ),
    inference(resolution,[],[f4515,f432])).

fof(f4515,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl13_603 ),
    inference(avatar_component_clause,[],[f4514])).

fof(f4514,plain,
    ( spl13_603
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_603])])).

fof(f8751,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_778
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f6078])).

fof(f6078,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_778 ),
    inference(avatar_component_clause,[],[f6077])).

fof(f6077,plain,
    ( spl13_778
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_778])])).

fof(f9068,plain,
    ( ~ spl13_6
    | ~ spl13_194
    | spl13_603
    | spl13_761
    | ~ spl13_776
    | ~ spl13_940 ),
    inference(avatar_contradiction_clause,[],[f9067])).

fof(f9067,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_194
    | ~ spl13_603
    | ~ spl13_761
    | ~ spl13_776
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f9066,f8742])).

fof(f8742,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl13_761
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f5984])).

fof(f5984,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_761 ),
    inference(avatar_component_clause,[],[f5983])).

fof(f5983,plain,
    ( spl13_761
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_761])])).

fof(f9066,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_194
    | ~ spl13_603
    | ~ spl13_776
    | ~ spl13_940 ),
    inference(forward_demodulation,[],[f8750,f8983])).

fof(f8750,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,o_0_0_xboole_0,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_776
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f6070])).

fof(f6070,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_776 ),
    inference(avatar_component_clause,[],[f6069])).

fof(f6069,plain,
    ( spl13_776
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_776])])).

fof(f8966,plain,
    ( spl13_391
    | ~ spl13_940 ),
    inference(avatar_contradiction_clause,[],[f8965])).

fof(f8965,plain,
    ( $false
    | ~ spl13_391
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f8538,f119])).

fof(f8538,plain,
    ( ~ m1_subset_1(sK10(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl13_391
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f2914])).

fof(f8959,plain,
    ( ~ spl13_6
    | ~ spl13_46
    | spl13_443
    | ~ spl13_940 ),
    inference(avatar_contradiction_clause,[],[f8958])).

fof(f8958,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_443
    | ~ spl13_940 ),
    inference(subsumption_resolution,[],[f8471,f3388])).

fof(f8471,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_46
    | ~ spl13_940 ),
    inference(backward_demodulation,[],[f7412,f326])).

fof(f8456,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_638
    | spl13_931
    | ~ spl13_972 ),
    inference(avatar_contradiction_clause,[],[f8455])).

fof(f8455,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_638
    | ~ spl13_931
    | ~ spl13_972 ),
    inference(subsumption_resolution,[],[f7316,f8454])).

fof(f8454,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_638
    | ~ spl13_972 ),
    inference(subsumption_resolution,[],[f8248,f4848])).

fof(f4848,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_638 ),
    inference(avatar_component_clause,[],[f4847])).

fof(f4847,plain,
    ( spl13_638
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_638])])).

fof(f8248,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_972 ),
    inference(resolution,[],[f7759,f4258])).

fof(f4258,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2) )
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f4257,f141])).

fof(f4257,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2)
        | v2_struct_0(sK0) )
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f4256,f148])).

fof(f4256,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f4255,f155])).

fof(f4255,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(subsumption_resolution,[],[f4254,f183])).

fof(f4254,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_36 ),
    inference(resolution,[],[f289,f115])).

fof(f115,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f289,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl13_36
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f7759,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)))
    | ~ spl13_972 ),
    inference(avatar_component_clause,[],[f7758])).

fof(f7758,plain,
    ( spl13_972
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_972])])).

fof(f7316,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_931 ),
    inference(avatar_component_clause,[],[f7315])).

fof(f7315,plain,
    ( spl13_931
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_931])])).

fof(f8453,plain,
    ( ~ spl13_6
    | ~ spl13_322
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8452])).

fof(f8452,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_322
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f7414,f2367])).

fof(f2367,plain,
    ( v1_xboole_0(sK3)
    | ~ spl13_322 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f2366,plain,
    ( spl13_322
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_322])])).

fof(f7414,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f7409,f202])).

fof(f8451,plain,
    ( ~ spl13_6
    | ~ spl13_228
    | ~ spl13_322
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8450])).

fof(f8450,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_322
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f7435,f2367])).

fof(f7435,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_228
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f210,f1575,f7409,f431])).

fof(f8449,plain,
    ( ~ spl13_6
    | ~ spl13_322
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8448])).

fof(f8448,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_322
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f7436,f2367])).

fof(f7436,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f210,f119,f7409,f431])).

fof(f8447,plain,
    ( ~ spl13_6
    | ~ spl13_322
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8446])).

fof(f8446,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_322
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f7437,f2367])).

fof(f7437,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f162,f7409,f127])).

fof(f8445,plain,
    ( ~ spl13_6
    | ~ spl13_322
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8444])).

fof(f8444,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_322
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f7445,f2367])).

fof(f7445,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f162,f7409,f127])).

fof(f8443,plain,
    ( ~ spl13_322
    | ~ spl13_904 ),
    inference(avatar_contradiction_clause,[],[f8442])).

fof(f8442,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_904 ),
    inference(subsumption_resolution,[],[f7322,f2367])).

fof(f7322,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_904 ),
    inference(unit_resulting_resolution,[],[f119,f7198])).

fof(f7198,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK10(k1_zfmisc_1(sK3)),k1_zfmisc_1(X0)) )
    | ~ spl13_904 ),
    inference(resolution,[],[f6925,f131])).

fof(f8441,plain,
    ( ~ spl13_322
    | ~ spl13_924 ),
    inference(avatar_contradiction_clause,[],[f8440])).

fof(f8440,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_924 ),
    inference(subsumption_resolution,[],[f7257,f2367])).

fof(f7257,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_924 ),
    inference(resolution,[],[f7241,f128])).

fof(f8439,plain,
    ( ~ spl13_322
    | ~ spl13_924 ),
    inference(avatar_contradiction_clause,[],[f8438])).

fof(f8438,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_924 ),
    inference(subsumption_resolution,[],[f7252,f2367])).

fof(f7252,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_924 ),
    inference(unit_resulting_resolution,[],[f7241,f128])).

fof(f8437,plain,
    ( ~ spl13_322
    | ~ spl13_904 ),
    inference(avatar_contradiction_clause,[],[f8436])).

fof(f8436,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_904 ),
    inference(subsumption_resolution,[],[f7193,f2367])).

fof(f7193,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_904 ),
    inference(unit_resulting_resolution,[],[f119,f6925,f131])).

fof(f8435,plain,
    ( ~ spl13_6
    | ~ spl13_322
    | spl13_893 ),
    inference(avatar_contradiction_clause,[],[f8434])).

fof(f8434,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_322
    | ~ spl13_893 ),
    inference(subsumption_resolution,[],[f7017,f2367])).

fof(f7017,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_893 ),
    inference(unit_resulting_resolution,[],[f119,f119,f6836,f837])).

fof(f6836,plain,
    ( o_0_0_xboole_0 != sK10(k1_zfmisc_1(sK3))
    | ~ spl13_893 ),
    inference(avatar_component_clause,[],[f6835])).

fof(f6835,plain,
    ( spl13_893
  <=> o_0_0_xboole_0 != sK10(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_893])])).

fof(f8433,plain,
    ( ~ spl13_322
    | ~ spl13_764 ),
    inference(avatar_contradiction_clause,[],[f8432])).

fof(f8432,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_764 ),
    inference(subsumption_resolution,[],[f6014,f2367])).

fof(f6014,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_764 ),
    inference(resolution,[],[f5998,f128])).

fof(f5998,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_764 ),
    inference(avatar_component_clause,[],[f5997])).

fof(f5997,plain,
    ( spl13_764
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_764])])).

fof(f8431,plain,
    ( ~ spl13_322
    | ~ spl13_764 ),
    inference(avatar_contradiction_clause,[],[f8430])).

fof(f8430,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_764 ),
    inference(subsumption_resolution,[],[f6008,f2367])).

fof(f6008,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_764 ),
    inference(unit_resulting_resolution,[],[f5998,f128])).

fof(f8429,plain,
    ( ~ spl13_6
    | ~ spl13_46
    | ~ spl13_322
    | spl13_443
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8428])).

fof(f8428,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_322
    | ~ spl13_443
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5955,f2367])).

fof(f5955,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_443
    | ~ spl13_748 ),
    inference(unit_resulting_resolution,[],[f326,f3374,f5911,f837])).

fof(f5911,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_748 ),
    inference(avatar_component_clause,[],[f5910])).

fof(f5910,plain,
    ( spl13_748
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_748])])).

fof(f8427,plain,
    ( ~ spl13_6
    | ~ spl13_46
    | ~ spl13_322
    | ~ spl13_394
    | spl13_443 ),
    inference(avatar_contradiction_clause,[],[f8426])).

fof(f8426,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_322
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f3389,f2367])).

fof(f3389,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f2938,f326,f3374,f837])).

fof(f2938,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_394 ),
    inference(avatar_component_clause,[],[f2937])).

fof(f2937,plain,
    ( spl13_394
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_394])])).

fof(f8425,plain,
    ( ~ spl13_322
    | ~ spl13_344 ),
    inference(avatar_contradiction_clause,[],[f8424])).

fof(f8424,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2530,f2367])).

fof(f2530,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_344 ),
    inference(resolution,[],[f2520,f128])).

fof(f8423,plain,
    ( ~ spl13_322
    | ~ spl13_344 ),
    inference(avatar_contradiction_clause,[],[f8422])).

fof(f8422,plain,
    ( $false
    | ~ spl13_322
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2525,f2367])).

fof(f2525,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_344 ),
    inference(unit_resulting_resolution,[],[f2520,f128])).

fof(f8421,plain,
    ( ~ spl13_46
    | ~ spl13_322
    | ~ spl13_328 ),
    inference(avatar_contradiction_clause,[],[f8420])).

fof(f8420,plain,
    ( $false
    | ~ spl13_46
    | ~ spl13_322
    | ~ spl13_328 ),
    inference(subsumption_resolution,[],[f2440,f2367])).

fof(f2440,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_46
    | ~ spl13_328 ),
    inference(unit_resulting_resolution,[],[f326,f2417,f131])).

fof(f8409,plain,
    ( ~ spl13_6
    | spl13_291
    | ~ spl13_394
    | spl13_443 ),
    inference(avatar_contradiction_clause,[],[f8408])).

fof(f8408,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_291
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f3385,f2209])).

fof(f2209,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_291 ),
    inference(avatar_component_clause,[],[f2208])).

fof(f2208,plain,
    ( spl13_291
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_291])])).

fof(f3385,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_6
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f2938,f3374,f432])).

fof(f8407,plain,
    ( ~ spl13_6
    | spl13_291
    | ~ spl13_394
    | spl13_443 ),
    inference(avatar_contradiction_clause,[],[f8406])).

fof(f8406,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_291
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(subsumption_resolution,[],[f3399,f2209])).

fof(f3399,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_6
    | ~ spl13_394
    | ~ spl13_443 ),
    inference(unit_resulting_resolution,[],[f162,f2938,f3374,f431])).

fof(f8405,plain,
    ( spl13_291
    | spl13_321
    | ~ spl13_394 ),
    inference(avatar_contradiction_clause,[],[f8404])).

fof(f8404,plain,
    ( $false
    | ~ spl13_291
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(subsumption_resolution,[],[f3059,f2209])).

fof(f3059,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(resolution,[],[f2938,f2374])).

fof(f2374,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl13_321 ),
    inference(resolution,[],[f2363,f122])).

fof(f2363,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl13_321 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f8403,plain,
    ( spl13_291
    | spl13_321
    | ~ spl13_394 ),
    inference(avatar_contradiction_clause,[],[f8402])).

fof(f8402,plain,
    ( $false
    | ~ spl13_291
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(subsumption_resolution,[],[f3057,f2209])).

fof(f3057,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(unit_resulting_resolution,[],[f2938,f2374])).

fof(f8401,plain,
    ( spl13_291
    | spl13_321
    | ~ spl13_394 ),
    inference(avatar_contradiction_clause,[],[f8400])).

fof(f8400,plain,
    ( $false
    | ~ spl13_291
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(subsumption_resolution,[],[f3058,f2209])).

fof(f3058,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_321
    | ~ spl13_394 ),
    inference(unit_resulting_resolution,[],[f2363,f2938,f122])).

fof(f8399,plain,
    ( spl13_585
    | ~ spl13_604 ),
    inference(avatar_contradiction_clause,[],[f8398])).

fof(f8398,plain,
    ( $false
    | ~ spl13_585
    | ~ spl13_604 ),
    inference(subsumption_resolution,[],[f4546,f4396])).

fof(f4546,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_604 ),
    inference(unit_resulting_resolution,[],[f4528,f121])).

fof(f4528,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_604 ),
    inference(avatar_component_clause,[],[f4527])).

fof(f4527,plain,
    ( spl13_604
  <=> r2_hidden(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_604])])).

fof(f8397,plain,
    ( spl13_713
    | ~ spl13_726 ),
    inference(avatar_contradiction_clause,[],[f8396])).

fof(f8396,plain,
    ( $false
    | ~ spl13_713
    | ~ spl13_726 ),
    inference(subsumption_resolution,[],[f5759,f5591])).

fof(f5591,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_713 ),
    inference(avatar_component_clause,[],[f5590])).

fof(f5590,plain,
    ( spl13_713
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_713])])).

fof(f5759,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_726 ),
    inference(unit_resulting_resolution,[],[f5738,f121])).

fof(f5738,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_726 ),
    inference(avatar_component_clause,[],[f5737])).

fof(f5737,plain,
    ( spl13_726
  <=> r2_hidden(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_726])])).

fof(f8395,plain,
    ( spl13_321
    | spl13_735
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8394])).

fof(f8394,plain,
    ( $false
    | ~ spl13_321
    | ~ spl13_735
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5959,f5777])).

fof(f5777,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_735 ),
    inference(avatar_component_clause,[],[f5776])).

fof(f5776,plain,
    ( spl13_735
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_735])])).

fof(f5959,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_321
    | ~ spl13_748 ),
    inference(resolution,[],[f5911,f2374])).

fof(f8393,plain,
    ( spl13_321
    | spl13_735
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8392])).

fof(f8392,plain,
    ( $false
    | ~ spl13_321
    | ~ spl13_735
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5950,f5777])).

fof(f5950,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_321
    | ~ spl13_748 ),
    inference(unit_resulting_resolution,[],[f5911,f2374])).

fof(f8391,plain,
    ( spl13_321
    | spl13_735
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8390])).

fof(f8390,plain,
    ( $false
    | ~ spl13_321
    | ~ spl13_735
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5951,f5777])).

fof(f5951,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_321
    | ~ spl13_748 ),
    inference(unit_resulting_resolution,[],[f2363,f5911,f122])).

fof(f8389,plain,
    ( ~ spl13_6
    | spl13_443
    | spl13_735
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8388])).

fof(f8388,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_735
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5952,f5777])).

fof(f5952,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_748 ),
    inference(unit_resulting_resolution,[],[f162,f3374,f5911,f431])).

fof(f8387,plain,
    ( ~ spl13_6
    | spl13_443
    | spl13_735
    | ~ spl13_748 ),
    inference(avatar_contradiction_clause,[],[f8386])).

fof(f8386,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_735
    | ~ spl13_748 ),
    inference(subsumption_resolution,[],[f5953,f5777])).

fof(f5953,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_6
    | ~ spl13_443
    | ~ spl13_748 ),
    inference(unit_resulting_resolution,[],[f3374,f5911,f432])).

fof(f8385,plain,
    ( ~ spl13_6
    | spl13_291
    | ~ spl13_394
    | spl13_443
    | ~ spl13_680 ),
    inference(avatar_contradiction_clause,[],[f8384])).

fof(f8384,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_291
    | ~ spl13_394
    | ~ spl13_443
    | ~ spl13_680 ),
    inference(subsumption_resolution,[],[f8383,f8352])).

fof(f8352,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_6
    | ~ spl13_394
    | ~ spl13_443
    | ~ spl13_680 ),
    inference(forward_demodulation,[],[f3385,f5233])).

fof(f5233,plain,
    ( o_0_0_xboole_0 = sK10(u1_struct_0(sK1))
    | ~ spl13_680 ),
    inference(avatar_component_clause,[],[f5232])).

fof(f5232,plain,
    ( spl13_680
  <=> o_0_0_xboole_0 = sK10(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_680])])).

fof(f8383,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_291
    | ~ spl13_680 ),
    inference(forward_demodulation,[],[f2209,f5233])).

fof(f8382,plain,
    ( ~ spl13_46
    | ~ spl13_322
    | ~ spl13_930 ),
    inference(avatar_contradiction_clause,[],[f8381])).

fof(f8381,plain,
    ( $false
    | ~ spl13_46
    | ~ spl13_322
    | ~ spl13_930 ),
    inference(subsumption_resolution,[],[f2367,f7489])).

fof(f7489,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_46
    | ~ spl13_930 ),
    inference(unit_resulting_resolution,[],[f326,f7319,f131])).

fof(f7319,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_930 ),
    inference(avatar_component_clause,[],[f7318])).

fof(f7318,plain,
    ( spl13_930
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_930])])).

fof(f8380,plain,
    ( ~ spl13_6
    | spl13_331
    | spl13_941 ),
    inference(avatar_contradiction_clause,[],[f8379])).

fof(f8379,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_331
    | ~ spl13_941 ),
    inference(subsumption_resolution,[],[f2421,f7421])).

fof(f7421,plain,
    ( r2_hidden(sK10(sK3),sK3)
    | ~ spl13_6
    | ~ spl13_941 ),
    inference(unit_resulting_resolution,[],[f119,f7409,f432])).

fof(f2421,plain,
    ( ~ r2_hidden(sK10(sK3),sK3)
    | ~ spl13_331 ),
    inference(avatar_component_clause,[],[f2420])).

fof(f2420,plain,
    ( spl13_331
  <=> ~ r2_hidden(sK10(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_331])])).

fof(f8378,plain,
    ( spl13_585
    | ~ spl13_604
    | ~ spl13_680 ),
    inference(avatar_contradiction_clause,[],[f8377])).

fof(f8377,plain,
    ( $false
    | ~ spl13_585
    | ~ spl13_604
    | ~ spl13_680 ),
    inference(subsumption_resolution,[],[f8376,f8362])).

fof(f8362,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_604
    | ~ spl13_680 ),
    inference(forward_demodulation,[],[f4546,f5233])).

fof(f8376,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_585
    | ~ spl13_680 ),
    inference(forward_demodulation,[],[f4396,f5233])).

fof(f8373,plain,
    ( spl13_641
    | ~ spl13_672 ),
    inference(avatar_contradiction_clause,[],[f8372])).

fof(f8372,plain,
    ( $false
    | ~ spl13_641
    | ~ spl13_672 ),
    inference(subsumption_resolution,[],[f4852,f5202])).

fof(f5202,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_672 ),
    inference(unit_resulting_resolution,[],[f5072,f121])).

fof(f5072,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_672 ),
    inference(avatar_component_clause,[],[f5071])).

fof(f5071,plain,
    ( spl13_672
  <=> r2_hidden(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_672])])).

fof(f4852,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_641 ),
    inference(avatar_component_clause,[],[f4851])).

fof(f4851,plain,
    ( spl13_641
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_641])])).

fof(f8371,plain,
    ( spl13_665
    | ~ spl13_796 ),
    inference(avatar_contradiction_clause,[],[f8370])).

fof(f8370,plain,
    ( $false
    | ~ spl13_665
    | ~ spl13_796 ),
    inference(subsumption_resolution,[],[f5041,f6198])).

fof(f6198,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_796 ),
    inference(unit_resulting_resolution,[],[f6150,f121])).

fof(f6150,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_796 ),
    inference(avatar_component_clause,[],[f6149])).

fof(f6149,plain,
    ( spl13_796
  <=> r2_hidden(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_796])])).

fof(f5041,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_665 ),
    inference(avatar_component_clause,[],[f5040])).

fof(f5040,plain,
    ( spl13_665
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_665])])).

fof(f8368,plain,
    ( ~ spl13_604
    | ~ spl13_680
    | spl13_713 ),
    inference(avatar_contradiction_clause,[],[f8367])).

fof(f8367,plain,
    ( $false
    | ~ spl13_604
    | ~ spl13_680
    | ~ spl13_713 ),
    inference(subsumption_resolution,[],[f5591,f8362])).

fof(f8366,plain,
    ( ~ spl13_6
    | ~ spl13_394
    | spl13_443
    | ~ spl13_680
    | spl13_735 ),
    inference(avatar_contradiction_clause,[],[f8365])).

fof(f8365,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_394
    | ~ spl13_443
    | ~ spl13_680
    | ~ spl13_735 ),
    inference(subsumption_resolution,[],[f5777,f8352])).

fof(f8336,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | spl13_323
    | ~ spl13_642
    | spl13_935
    | ~ spl13_984 ),
    inference(avatar_contradiction_clause,[],[f8335])).

fof(f8335,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | ~ spl13_323
    | ~ spl13_642
    | ~ spl13_935
    | ~ spl13_984 ),
    inference(subsumption_resolution,[],[f8334,f7609])).

fof(f7609,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_46
    | ~ spl13_323
    | ~ spl13_935 ),
    inference(unit_resulting_resolution,[],[f7373,f3350])).

fof(f3350,plain,
    ( ! [X15] :
        ( ~ r2_hidden(X15,sK2)
        | r2_hidden(X15,sK3) )
    | ~ spl13_46
    | ~ spl13_323 ),
    inference(resolution,[],[f2554,f326])).

fof(f2554,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK3))
        | r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_323 ),
    inference(resolution,[],[f2377,f130])).

fof(f2377,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | r2_hidden(X0,sK3) )
    | ~ spl13_323 ),
    inference(resolution,[],[f2370,f122])).

fof(f7373,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK3)
    | ~ spl13_935 ),
    inference(avatar_component_clause,[],[f7372])).

fof(f7372,plain,
    ( spl13_935
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_935])])).

fof(f8334,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_642
    | ~ spl13_984 ),
    inference(subsumption_resolution,[],[f8329,f4862])).

fof(f4862,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_642 ),
    inference(avatar_component_clause,[],[f4861])).

fof(f4861,plain,
    ( spl13_642
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_642])])).

fof(f8329,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_984 ),
    inference(resolution,[],[f7849,f4258])).

fof(f7849,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)))
    | ~ spl13_984 ),
    inference(avatar_component_clause,[],[f7848])).

fof(f7848,plain,
    ( spl13_984
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_984])])).

fof(f8333,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | spl13_323
    | ~ spl13_642
    | spl13_935
    | ~ spl13_984 ),
    inference(avatar_contradiction_clause,[],[f8332])).

fof(f8332,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | ~ spl13_323
    | ~ spl13_642
    | ~ spl13_935
    | ~ spl13_984 ),
    inference(subsumption_resolution,[],[f8327,f7609])).

fof(f8327,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_642
    | ~ spl13_984 ),
    inference(unit_resulting_resolution,[],[f4862,f7849,f4258])).

fof(f8331,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | spl13_323
    | ~ spl13_642
    | spl13_935
    | ~ spl13_984 ),
    inference(avatar_contradiction_clause,[],[f8330])).

fof(f8330,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_46
    | ~ spl13_323
    | ~ spl13_642
    | ~ spl13_935
    | ~ spl13_984 ),
    inference(subsumption_resolution,[],[f8328,f7609])).

fof(f8328,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_642
    | ~ spl13_984 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f289,f4862,f7849,f115])).

fof(f8268,plain,
    ( spl13_1046
    | ~ spl13_132
    | ~ spl13_564 ),
    inference(avatar_split_clause,[],[f4193,f4189,f724,f8266])).

fof(f8266,plain,
    ( spl13_1046
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK5(sK12))),sK5(sK5(sK5(sK5(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1046])])).

fof(f724,plain,
    ( spl13_132
  <=> l1_struct_0(sK5(sK5(sK5(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f4189,plain,
    ( spl13_564
  <=> l1_waybel_0(sK5(sK5(sK5(sK5(sK12)))),sK5(sK5(sK5(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_564])])).

fof(f4193,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK5(sK12))),sK5(sK5(sK5(sK5(sK12))))))
    | ~ spl13_132
    | ~ spl13_564 ),
    inference(unit_resulting_resolution,[],[f725,f4190,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_u1_waybel_0)).

fof(f4190,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK12)))),sK5(sK5(sK5(sK12))))
    | ~ spl13_564 ),
    inference(avatar_component_clause,[],[f4189])).

fof(f725,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK12))))
    | ~ spl13_132 ),
    inference(avatar_component_clause,[],[f724])).

fof(f8258,plain,
    ( spl13_1044
    | ~ spl13_126
    | ~ spl13_558 ),
    inference(avatar_split_clause,[],[f4139,f4135,f692,f8256])).

fof(f8256,plain,
    ( spl13_1044
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK5(sK0))),sK5(sK5(sK5(sK5(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1044])])).

fof(f692,plain,
    ( spl13_126
  <=> l1_struct_0(sK5(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f4135,plain,
    ( spl13_558
  <=> l1_waybel_0(sK5(sK5(sK5(sK5(sK0)))),sK5(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_558])])).

fof(f4139,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK5(sK0))),sK5(sK5(sK5(sK5(sK0))))))
    | ~ spl13_126
    | ~ spl13_558 ),
    inference(unit_resulting_resolution,[],[f693,f4136,f123])).

fof(f4136,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK0)))),sK5(sK5(sK5(sK0))))
    | ~ spl13_558 ),
    inference(avatar_component_clause,[],[f4135])).

fof(f693,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK0))))
    | ~ spl13_126 ),
    inference(avatar_component_clause,[],[f692])).

fof(f8236,plain,
    ( ~ spl13_1043
    | spl13_1027 ),
    inference(avatar_split_clause,[],[f8153,f8131,f8234])).

fof(f8234,plain,
    ( spl13_1043
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK4(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1043])])).

fof(f8131,plain,
    ( spl13_1027
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1027])])).

fof(f8153,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK4(sK1))))))
    | ~ spl13_1027 ),
    inference(unit_resulting_resolution,[],[f119,f8132,f130])).

fof(f8132,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK10(sK4(sK1))))
    | ~ spl13_1027 ),
    inference(avatar_component_clause,[],[f8131])).

fof(f8221,plain,
    ( ~ spl13_1041
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5448,f5232,f4398,f339,f182,f154,f147,f140,f8219])).

fof(f8219,plain,
    ( spl13_1041
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1041])])).

fof(f4398,plain,
    ( spl13_584
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_584])])).

fof(f5448,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4440])).

fof(f4440,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f4399,f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f4399,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_584 ),
    inference(avatar_component_clause,[],[f4398])).

fof(f8208,plain,
    ( ~ spl13_1039
    | spl13_1019 ),
    inference(avatar_split_clause,[],[f8102,f8099,f8206])).

fof(f8206,plain,
    ( spl13_1039
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1039])])).

fof(f8099,plain,
    ( spl13_1019
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1019])])).

fof(f8102,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK10(sK4(sK1)))))
    | ~ spl13_1019 ),
    inference(unit_resulting_resolution,[],[f119,f8100,f130])).

fof(f8100,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(sK4(sK1)))
    | ~ spl13_1019 ),
    inference(avatar_component_clause,[],[f8099])).

fof(f8200,plain,
    ( ~ spl13_1037
    | spl13_1027 ),
    inference(avatar_split_clause,[],[f8154,f8131,f8198])).

fof(f8198,plain,
    ( spl13_1037
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1037])])).

fof(f8154,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK10(sK4(sK1))))
    | ~ spl13_1027 ),
    inference(unit_resulting_resolution,[],[f8132,f121])).

fof(f8193,plain,
    ( spl13_1034
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5445,f5232,f4398,f359,f182,f154,f147,f140,f8191])).

fof(f359,plain,
    ( spl13_56
  <=> r2_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f5445,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4436])).

fof(f4436,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f360,f4399,f111])).

fof(f111,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X5)),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f360,plain,
    ( r2_waybel_0(sK0,sK1,sK3)
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f359])).

fof(f8171,plain,
    ( ~ spl13_1033
    | spl13_1027 ),
    inference(avatar_split_clause,[],[f8152,f8131,f8169])).

fof(f8169,plain,
    ( spl13_1033
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1033])])).

fof(f8152,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK10(sK4(sK1)))
    | ~ spl13_1027 ),
    inference(unit_resulting_resolution,[],[f8132,f126])).

fof(f8164,plain,
    ( spl13_1030
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5444,f5232,f4398,f294,f182,f154,f147,f140,f8162])).

fof(f8162,plain,
    ( spl13_1030
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1030])])).

fof(f5444,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4435])).

fof(f4435,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f4399,f111])).

fof(f8140,plain,
    ( ~ spl13_1029
    | spl13_1007 ),
    inference(avatar_split_clause,[],[f8091,f8018,f8138])).

fof(f8138,plain,
    ( spl13_1029
  <=> ~ r2_hidden(sK4(sK1),sK10(k1_zfmisc_1(sK10(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1029])])).

fof(f8018,plain,
    ( spl13_1007
  <=> ~ m1_subset_1(sK4(sK1),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1007])])).

fof(f8091,plain,
    ( ~ r2_hidden(sK4(sK1),sK10(k1_zfmisc_1(sK10(sK4(sK1)))))
    | ~ spl13_1007 ),
    inference(unit_resulting_resolution,[],[f119,f8019,f130])).

fof(f8019,plain,
    ( ~ m1_subset_1(sK4(sK1),sK10(sK4(sK1)))
    | ~ spl13_1007 ),
    inference(avatar_component_clause,[],[f8018])).

fof(f8133,plain,
    ( ~ spl13_1027
    | ~ spl13_318
    | spl13_1007 ),
    inference(avatar_split_clause,[],[f8090,f8018,f2342,f8131])).

fof(f8090,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK10(sK4(sK1))))
    | ~ spl13_318
    | ~ spl13_1007 ),
    inference(unit_resulting_resolution,[],[f2343,f8019,f130])).

fof(f8126,plain,
    ( spl13_1024
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5426,f5232,f934,f359,f182,f154,f147,f140,f8124])).

fof(f934,plain,
    ( spl13_170
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_170])])).

fof(f5426,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4265])).

fof(f4265,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f935,f360,f111])).

fof(f935,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_170 ),
    inference(avatar_component_clause,[],[f934])).

fof(f8119,plain,
    ( spl13_1022
    | ~ spl13_6
    | spl13_1005 ),
    inference(avatar_split_clause,[],[f8036,f8009,f161,f8117])).

fof(f8009,plain,
    ( spl13_1005
  <=> o_0_0_xboole_0 != sK10(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1005])])).

fof(f8036,plain,
    ( r2_hidden(sK10(sK10(sK4(sK1))),sK10(sK4(sK1)))
    | ~ spl13_6
    | ~ spl13_1005 ),
    inference(unit_resulting_resolution,[],[f162,f119,f8010,f431])).

fof(f8010,plain,
    ( o_0_0_xboole_0 != sK10(sK4(sK1))
    | ~ spl13_1005 ),
    inference(avatar_component_clause,[],[f8009])).

fof(f8112,plain,
    ( ~ spl13_1021
    | ~ spl13_6
    | spl13_1005 ),
    inference(avatar_split_clause,[],[f8026,f8009,f161,f8110])).

fof(f8110,plain,
    ( spl13_1021
  <=> ~ r2_hidden(sK10(sK4(sK1)),sK10(sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1021])])).

fof(f8026,plain,
    ( ~ r2_hidden(sK10(sK4(sK1)),sK10(sK10(sK4(sK1))))
    | ~ spl13_6
    | ~ spl13_1005 ),
    inference(unit_resulting_resolution,[],[f119,f8010,f838])).

fof(f8101,plain,
    ( ~ spl13_1019
    | ~ spl13_6
    | spl13_273
    | spl13_1005 ),
    inference(avatar_split_clause,[],[f8034,f8009,f2110,f161,f8099])).

fof(f2110,plain,
    ( spl13_273
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_273])])).

fof(f8034,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(sK4(sK1)))
    | ~ spl13_6
    | ~ spl13_273
    | ~ spl13_1005 ),
    inference(unit_resulting_resolution,[],[f162,f2111,f8010,f431])).

fof(f2111,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(sK4(sK1)))
    | ~ spl13_273 ),
    inference(avatar_component_clause,[],[f2110])).

fof(f8089,plain,
    ( spl13_1016
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5422,f5232,f883,f359,f182,f154,f147,f140,f8087])).

fof(f883,plain,
    ( spl13_162
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_162])])).

fof(f5422,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4260])).

fof(f4260,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f884,f360,f111])).

fof(f884,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_162 ),
    inference(avatar_component_clause,[],[f883])).

fof(f8082,plain,
    ( ~ spl13_1015
    | ~ spl13_240
    | spl13_1013 ),
    inference(avatar_split_clause,[],[f8064,f8061,f1735,f8080])).

fof(f8080,plain,
    ( spl13_1015
  <=> ~ r1_tarski(sK10(sK4(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1015])])).

fof(f1735,plain,
    ( spl13_240
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_240])])).

fof(f8064,plain,
    ( ~ r1_tarski(sK10(sK4(sK1)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_1013 ),
    inference(unit_resulting_resolution,[],[f8062,f1738])).

fof(f1738,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | m1_subset_1(X0,o_0_0_xboole_0) )
    | ~ spl13_240 ),
    inference(superposition,[],[f126,f1736])).

fof(f1736,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_240 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f8063,plain,
    ( ~ spl13_1013
    | ~ spl13_6
    | ~ spl13_240
    | spl13_1005 ),
    inference(avatar_split_clause,[],[f8030,f8009,f1735,f161,f8061])).

fof(f8030,plain,
    ( ~ m1_subset_1(sK10(sK4(sK1)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_1005 ),
    inference(unit_resulting_resolution,[],[f119,f8010,f3204])).

fof(f3204,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl13_6
    | ~ spl13_240 ),
    inference(forward_demodulation,[],[f3184,f1736])).

fof(f3184,plain,
    ( ! [X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ m1_subset_1(X1,X0) )
    | ~ spl13_6 ),
    inference(resolution,[],[f837,f162])).

fof(f8052,plain,
    ( spl13_1010
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5340,f5232,f934,f294,f182,f154,f147,f140,f8050])).

fof(f8050,plain,
    ( spl13_1010
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1010])])).

fof(f5340,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f1967])).

fof(f1967,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f935,f111])).

fof(f8045,plain,
    ( ~ spl13_1009
    | ~ spl13_6
    | spl13_1005 ),
    inference(avatar_split_clause,[],[f8037,f8009,f161,f8043])).

fof(f8043,plain,
    ( spl13_1009
  <=> ~ v1_xboole_0(sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1009])])).

fof(f8037,plain,
    ( ~ v1_xboole_0(sK10(sK4(sK1)))
    | ~ spl13_6
    | ~ spl13_1005 ),
    inference(unit_resulting_resolution,[],[f162,f8010,f127])).

fof(f8020,plain,
    ( spl13_1004
    | ~ spl13_1007
    | ~ spl13_6
    | spl13_265 ),
    inference(avatar_split_clause,[],[f2066,f2049,f161,f8018,f8012])).

fof(f8012,plain,
    ( spl13_1004
  <=> o_0_0_xboole_0 = sK10(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1004])])).

fof(f2049,plain,
    ( spl13_265
  <=> ~ r2_hidden(sK4(sK1),sK10(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_265])])).

fof(f2066,plain,
    ( ~ m1_subset_1(sK4(sK1),sK10(sK4(sK1)))
    | o_0_0_xboole_0 = sK10(sK4(sK1))
    | ~ spl13_6
    | ~ spl13_265 ),
    inference(resolution,[],[f2050,f432])).

fof(f2050,plain,
    ( ~ r2_hidden(sK4(sK1),sK10(sK4(sK1)))
    | ~ spl13_265 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f7999,plain,
    ( spl13_1002
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5336,f5232,f883,f294,f182,f154,f147,f140,f7997])).

fof(f7997,plain,
    ( spl13_1002
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1002])])).

fof(f5336,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f1878])).

fof(f1878,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f884,f111])).

fof(f7992,plain,
    ( ~ spl13_1001
    | ~ spl13_6
    | spl13_257
    | spl13_649 ),
    inference(avatar_split_clause,[],[f4994,f4963,f1996,f161,f7990])).

fof(f7990,plain,
    ( spl13_1001
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1001])])).

fof(f1996,plain,
    ( spl13_257
  <=> o_0_0_xboole_0 != sK4(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_257])])).

fof(f4963,plain,
    ( spl13_649
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_649])])).

fof(f4994,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_649 ),
    inference(unit_resulting_resolution,[],[f1997,f4964,f432])).

fof(f4964,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_649 ),
    inference(avatar_component_clause,[],[f4963])).

fof(f1997,plain,
    ( o_0_0_xboole_0 != sK4(sK1)
    | ~ spl13_257 ),
    inference(avatar_component_clause,[],[f1996])).

fof(f7985,plain,
    ( ~ spl13_999
    | ~ spl13_6
    | spl13_257
    | spl13_645 ),
    inference(avatar_split_clause,[],[f4976,f4949,f1996,f161,f7983])).

fof(f7983,plain,
    ( spl13_999
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_999])])).

fof(f4949,plain,
    ( spl13_645
  <=> ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_645])])).

fof(f4976,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_645 ),
    inference(unit_resulting_resolution,[],[f1997,f4950,f432])).

fof(f4950,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_645 ),
    inference(avatar_component_clause,[],[f4949])).

fof(f7961,plain,
    ( ~ spl13_997
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5330,f5232,f934,f339,f182,f154,f147,f140,f7959])).

fof(f7959,plain,
    ( spl13_997
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_997])])).

fof(f5330,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f1037])).

fof(f1037,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f935,f118])).

fof(f7947,plain,
    ( ~ spl13_995
    | spl13_983 ),
    inference(avatar_split_clause,[],[f7852,f7841,f7945])).

fof(f7841,plain,
    ( spl13_983
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_983])])).

fof(f7852,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | ~ spl13_983 ),
    inference(unit_resulting_resolution,[],[f119,f7842,f130])).

fof(f7842,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_983 ),
    inference(avatar_component_clause,[],[f7841])).

fof(f7938,plain,
    ( ~ spl13_993
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5328,f5232,f883,f339,f182,f154,f147,f140,f7936])).

fof(f7936,plain,
    ( spl13_993
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_993])])).

fof(f5328,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f999])).

fof(f999,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f884,f118])).

fof(f7907,plain,
    ( ~ spl13_991
    | spl13_965 ),
    inference(avatar_split_clause,[],[f7821,f7702,f7905])).

fof(f7905,plain,
    ( spl13_991
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_991])])).

fof(f7702,plain,
    ( spl13_965
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_965])])).

fof(f7821,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl13_965 ),
    inference(unit_resulting_resolution,[],[f119,f7703,f130])).

fof(f7703,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2))
    | ~ spl13_965 ),
    inference(avatar_component_clause,[],[f7702])).

fof(f7870,plain,
    ( ~ spl13_989
    | spl13_983 ),
    inference(avatar_split_clause,[],[f7853,f7841,f7868])).

fof(f7853,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_983 ),
    inference(unit_resulting_resolution,[],[f7842,f121])).

fof(f7863,plain,
    ( ~ spl13_987
    | spl13_983 ),
    inference(avatar_split_clause,[],[f7851,f7841,f7861])).

fof(f7861,plain,
    ( spl13_987
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_987])])).

fof(f7851,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))
    | ~ spl13_983 ),
    inference(unit_resulting_resolution,[],[f7842,f126])).

fof(f7850,plain,
    ( spl13_984
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4327,f903,f339,f182,f154,f147,f140,f7848])).

fof(f903,plain,
    ( spl13_166
  <=> m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_166])])).

fof(f4327,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f904,f117])).

fof(f904,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_166 ),
    inference(avatar_component_clause,[],[f903])).

fof(f7843,plain,
    ( ~ spl13_983
    | spl13_911
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f7784,f7751,f6995,f7841])).

fof(f6995,plain,
    ( spl13_911
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_911])])).

fof(f7784,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_911
    | ~ spl13_970 ),
    inference(unit_resulting_resolution,[],[f6996,f7752,f130])).

fof(f6996,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl13_911 ),
    inference(avatar_component_clause,[],[f6995])).

fof(f7832,plain,
    ( ~ spl13_981
    | spl13_321
    | spl13_959
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f7789,f7751,f7638,f2362,f7830])).

fof(f7830,plain,
    ( spl13_981
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_981])])).

fof(f7638,plain,
    ( spl13_959
  <=> ~ r2_hidden(o_0_0_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_959])])).

fof(f7789,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2))
    | ~ spl13_321
    | ~ spl13_959
    | ~ spl13_970 ),
    inference(unit_resulting_resolution,[],[f7639,f7752,f3327])).

fof(f3327,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_zfmisc_1(sK2))
        | ~ r2_hidden(X5,X6)
        | r2_hidden(X5,sK2) )
    | ~ spl13_321 ),
    inference(resolution,[],[f2546,f121])).

fof(f2546,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_321 ),
    inference(resolution,[],[f2374,f130])).

fof(f7639,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK2)
    | ~ spl13_959 ),
    inference(avatar_component_clause,[],[f7638])).

fof(f7819,plain,
    ( spl13_978
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4322,f903,f359,f182,f154,f147,f140,f7817])).

fof(f7817,plain,
    ( spl13_978
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_978])])).

fof(f4322,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f360,f904,f110])).

fof(f110,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X1,X5,sK7(X0,X1,X2,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f7812,plain,
    ( ~ spl13_977
    | spl13_321
    | spl13_959
    | ~ spl13_970 ),
    inference(avatar_split_clause,[],[f7788,f7751,f7638,f2362,f7810])).

fof(f7810,plain,
    ( spl13_977
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_977])])).

fof(f7788,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK2)
    | ~ spl13_321
    | ~ spl13_959
    | ~ spl13_970 ),
    inference(unit_resulting_resolution,[],[f7639,f7752,f3325])).

fof(f3325,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X0,sK2) )
    | ~ spl13_321 ),
    inference(resolution,[],[f2546,f126])).

fof(f7805,plain,
    ( ~ spl13_975
    | ~ spl13_240
    | spl13_969 ),
    inference(avatar_split_clause,[],[f7761,f7744,f1735,f7803])).

fof(f7803,plain,
    ( spl13_975
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_975])])).

fof(f7761,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_969 ),
    inference(unit_resulting_resolution,[],[f7745,f1738])).

fof(f7760,plain,
    ( spl13_972
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4321,f903,f294,f182,f154,f147,f140,f7758])).

fof(f4321,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f904,f110])).

fof(f7753,plain,
    ( spl13_970
    | ~ spl13_6
    | ~ spl13_936
    | spl13_963 ),
    inference(avatar_split_clause,[],[f7726,f7693,f7398,f161,f7751])).

fof(f7398,plain,
    ( spl13_936
  <=> o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_936])])).

fof(f7726,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_6
    | ~ spl13_936
    | ~ spl13_963 ),
    inference(forward_demodulation,[],[f7713,f7399])).

fof(f7399,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK2))
    | ~ spl13_936 ),
    inference(avatar_component_clause,[],[f7398])).

fof(f7713,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2))
    | ~ spl13_6
    | ~ spl13_963 ),
    inference(unit_resulting_resolution,[],[f119,f7694,f432])).

fof(f7746,plain,
    ( ~ spl13_969
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_960
    | spl13_963 ),
    inference(avatar_split_clause,[],[f7718,f7693,f7658,f1735,f161,f7744])).

fof(f7718,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_960
    | ~ spl13_963 ),
    inference(unit_resulting_resolution,[],[f7659,f7694,f3204])).

fof(f7734,plain,
    ( ~ spl13_967
    | ~ spl13_6
    | spl13_963 ),
    inference(avatar_split_clause,[],[f7722,f7693,f161,f7732])).

fof(f7722,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl13_6
    | ~ spl13_963 ),
    inference(unit_resulting_resolution,[],[f162,f7694,f127])).

fof(f7704,plain,
    ( spl13_962
    | ~ spl13_965
    | ~ spl13_6
    | spl13_957
    | ~ spl13_960 ),
    inference(avatar_split_clause,[],[f7688,f7658,f7625,f161,f7702,f7696])).

fof(f7696,plain,
    ( spl13_962
  <=> k1_zfmisc_1(sK2) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_962])])).

fof(f7688,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2))
    | k1_zfmisc_1(sK2) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_957
    | ~ spl13_960 ),
    inference(resolution,[],[f7681,f7659])).

fof(f7681,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
        | o_0_0_xboole_0 = X0 )
    | ~ spl13_6
    | ~ spl13_957 ),
    inference(resolution,[],[f7631,f432])).

fof(f7660,plain,
    ( spl13_960
    | ~ spl13_936 ),
    inference(avatar_split_clause,[],[f7651,f7398,f7658])).

fof(f7651,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl13_936 ),
    inference(superposition,[],[f119,f7399])).

fof(f7640,plain,
    ( ~ spl13_959
    | spl13_957 ),
    inference(avatar_split_clause,[],[f7630,f7625,f7638])).

fof(f7630,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK2)
    | ~ spl13_957 ),
    inference(unit_resulting_resolution,[],[f7626,f121])).

fof(f7627,plain,
    ( ~ spl13_957
    | ~ spl13_238
    | ~ spl13_936
    | spl13_955 ),
    inference(avatar_split_clause,[],[f7602,f7571,f7398,f1721,f7625])).

fof(f7571,plain,
    ( spl13_955
  <=> ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_955])])).

fof(f7602,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK2)
    | ~ spl13_238
    | ~ spl13_936
    | ~ spl13_955 ),
    inference(forward_demodulation,[],[f7594,f1722])).

fof(f1722,plain,
    ( o_0_0_xboole_0 = sK10(o_0_0_xboole_0)
    | ~ spl13_238 ),
    inference(avatar_component_clause,[],[f1721])).

fof(f7594,plain,
    ( ~ m1_subset_1(sK10(o_0_0_xboole_0),sK2)
    | ~ spl13_936
    | ~ spl13_955 ),
    inference(backward_demodulation,[],[f7399,f7572])).

fof(f7572,plain,
    ( ~ m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK2)
    | ~ spl13_955 ),
    inference(avatar_component_clause,[],[f7571])).

fof(f7576,plain,
    ( spl13_954
    | ~ spl13_950 ),
    inference(avatar_split_clause,[],[f7558,f7541,f7574])).

fof(f7541,plain,
    ( spl13_950
  <=> r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_950])])).

fof(f7558,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK2))),sK2)
    | ~ spl13_950 ),
    inference(unit_resulting_resolution,[],[f119,f7542,f130])).

fof(f7542,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_950 ),
    inference(avatar_component_clause,[],[f7541])).

fof(f7550,plain,
    ( ~ spl13_953
    | spl13_939 ),
    inference(avatar_split_clause,[],[f7515,f7404,f7548])).

fof(f7515,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK2)))))
    | ~ spl13_939 ),
    inference(unit_resulting_resolution,[],[f119,f7405,f130])).

fof(f7543,plain,
    ( spl13_950
    | ~ spl13_6
    | spl13_937 ),
    inference(avatar_split_clause,[],[f7462,f7395,f161,f7541])).

fof(f7462,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK2))),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_6
    | ~ spl13_937 ),
    inference(unit_resulting_resolution,[],[f162,f119,f7396,f431])).

fof(f7525,plain,
    ( ~ spl13_949
    | ~ spl13_6
    | spl13_937 ),
    inference(avatar_split_clause,[],[f7456,f7395,f161,f7523])).

fof(f7523,plain,
    ( spl13_949
  <=> ~ r2_hidden(sK10(k1_zfmisc_1(sK2)),sK10(sK10(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_949])])).

fof(f7456,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(sK2)),sK10(sK10(k1_zfmisc_1(sK2))))
    | ~ spl13_6
    | ~ spl13_937 ),
    inference(unit_resulting_resolution,[],[f119,f7396,f838])).

fof(f7514,plain,
    ( ~ spl13_947
    | ~ spl13_240
    | spl13_945 ),
    inference(avatar_split_clause,[],[f7500,f7479,f1735,f7512])).

fof(f7512,plain,
    ( spl13_947
  <=> ~ r1_tarski(sK10(k1_zfmisc_1(sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_947])])).

fof(f7479,plain,
    ( spl13_945
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_945])])).

fof(f7500,plain,
    ( ~ r1_tarski(sK10(k1_zfmisc_1(sK2)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_945 ),
    inference(unit_resulting_resolution,[],[f7480,f1738])).

fof(f7480,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),o_0_0_xboole_0)
    | ~ spl13_945 ),
    inference(avatar_component_clause,[],[f7479])).

fof(f7481,plain,
    ( ~ spl13_945
    | ~ spl13_6
    | ~ spl13_240
    | spl13_937 ),
    inference(avatar_split_clause,[],[f7457,f7395,f1735,f161,f7479])).

fof(f7457,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK2)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_937 ),
    inference(unit_resulting_resolution,[],[f119,f7396,f3204])).

fof(f7471,plain,
    ( ~ spl13_943
    | ~ spl13_6
    | spl13_937 ),
    inference(avatar_split_clause,[],[f7463,f7395,f161,f7469])).

fof(f7469,plain,
    ( spl13_943
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_943])])).

fof(f7463,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_6
    | ~ spl13_937 ),
    inference(unit_resulting_resolution,[],[f162,f7396,f127])).

fof(f7413,plain,
    ( spl13_940
    | ~ spl13_761
    | ~ spl13_6
    | spl13_261
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5348,f5232,f2026,f161,f5983,f7411])).

fof(f2026,plain,
    ( spl13_261
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_261])])).

fof(f5348,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | o_0_0_xboole_0 = sK3
    | ~ spl13_6
    | ~ spl13_261
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2222])).

fof(f2222,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | o_0_0_xboole_0 = sK3
    | ~ spl13_6
    | ~ spl13_261 ),
    inference(resolution,[],[f2027,f432])).

fof(f2027,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_261 ),
    inference(avatar_component_clause,[],[f2026])).

fof(f7406,plain,
    ( spl13_936
    | ~ spl13_939
    | ~ spl13_6
    | spl13_429 ),
    inference(avatar_split_clause,[],[f3239,f3229,f161,f7404,f7398])).

fof(f3229,plain,
    ( spl13_429
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_429])])).

fof(f3239,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2)))
    | o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK2))
    | ~ spl13_6
    | ~ spl13_429 ),
    inference(resolution,[],[f3230,f432])).

fof(f3230,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_429 ),
    inference(avatar_component_clause,[],[f3229])).

fof(f7374,plain,
    ( ~ spl13_935
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4328,f903,f339,f182,f154,f147,f140,f7372])).

fof(f4328,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f904,f118])).

fof(f7347,plain,
    ( spl13_932
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4324,f903,f359,f182,f154,f147,f140,f7345])).

fof(f7345,plain,
    ( spl13_932
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_932])])).

fof(f4324,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f360,f904,f111])).

fof(f7320,plain,
    ( spl13_930
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4323,f903,f294,f182,f154,f147,f140,f7318])).

fof(f4323,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f904,f111])).

fof(f7313,plain,
    ( ~ spl13_929
    | spl13_913 ),
    inference(avatar_split_clause,[],[f7127,f7089,f7311])).

fof(f7089,plain,
    ( spl13_913
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_913])])).

fof(f7127,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | ~ spl13_913 ),
    inference(unit_resulting_resolution,[],[f119,f7090,f130])).

fof(f7090,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_913 ),
    inference(avatar_component_clause,[],[f7089])).

fof(f7265,plain,
    ( ~ spl13_927
    | ~ spl13_924 ),
    inference(avatar_split_clause,[],[f7250,f7240,f7263])).

fof(f7250,plain,
    ( ~ r2_hidden(sK3,sK10(sK10(k1_zfmisc_1(sK3))))
    | ~ spl13_924 ),
    inference(unit_resulting_resolution,[],[f7241,f120])).

fof(f7242,plain,
    ( spl13_924
    | spl13_323
    | ~ spl13_422
    | ~ spl13_904 ),
    inference(avatar_split_clause,[],[f7195,f6924,f3151,f2369,f7240])).

fof(f7195,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK3)
    | ~ spl13_323
    | ~ spl13_422
    | ~ spl13_904 ),
    inference(unit_resulting_resolution,[],[f3152,f6925,f3347])).

fof(f3347,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k1_zfmisc_1(sK3))
        | ~ r2_hidden(X5,X6)
        | r2_hidden(X5,sK3) )
    | ~ spl13_323 ),
    inference(resolution,[],[f2554,f121])).

fof(f7235,plain,
    ( spl13_922
    | ~ spl13_904 ),
    inference(avatar_split_clause,[],[f7191,f6924,f7233])).

fof(f7191,plain,
    ( m1_subset_1(sK10(sK10(k1_zfmisc_1(sK3))),sK3)
    | ~ spl13_904 ),
    inference(unit_resulting_resolution,[],[f119,f6925,f130])).

fof(f7184,plain,
    ( ~ spl13_921
    | spl13_895 ),
    inference(avatar_split_clause,[],[f6909,f6844,f7182])).

fof(f6909,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(sK3)))))
    | ~ spl13_895 ),
    inference(unit_resulting_resolution,[],[f119,f6845,f130])).

fof(f7146,plain,
    ( ~ spl13_919
    | spl13_913 ),
    inference(avatar_split_clause,[],[f7128,f7089,f7144])).

fof(f7144,plain,
    ( spl13_919
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_919])])).

fof(f7128,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_913 ),
    inference(unit_resulting_resolution,[],[f7090,f121])).

fof(f7138,plain,
    ( ~ spl13_917
    | spl13_913 ),
    inference(avatar_split_clause,[],[f7126,f7089,f7136])).

fof(f7136,plain,
    ( spl13_917
  <=> ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_917])])).

fof(f7126,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k1_zfmisc_1(sK3))
    | ~ spl13_913 ),
    inference(unit_resulting_resolution,[],[f7090,f126])).

fof(f7098,plain,
    ( ~ spl13_915
    | spl13_911 ),
    inference(avatar_split_clause,[],[f7007,f6995,f7096])).

fof(f7096,plain,
    ( spl13_915
  <=> ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_915])])).

fof(f7007,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | ~ spl13_911 ),
    inference(unit_resulting_resolution,[],[f119,f6996,f130])).

fof(f7091,plain,
    ( ~ spl13_913
    | ~ spl13_694
    | spl13_911 ),
    inference(avatar_split_clause,[],[f7006,f6995,f5492,f7089])).

fof(f5492,plain,
    ( spl13_694
  <=> r2_hidden(o_0_0_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_694])])).

fof(f7006,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl13_694
    | ~ spl13_911 ),
    inference(unit_resulting_resolution,[],[f5493,f6996,f130])).

fof(f5493,plain,
    ( r2_hidden(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_694 ),
    inference(avatar_component_clause,[],[f5492])).

fof(f6997,plain,
    ( ~ spl13_911
    | ~ spl13_6
    | spl13_405
    | spl13_907 ),
    inference(avatar_split_clause,[],[f6982,f6972,f3033,f161,f6995])).

fof(f3033,plain,
    ( spl13_405
  <=> k1_zfmisc_1(sK3) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_405])])).

fof(f6972,plain,
    ( spl13_907
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_907])])).

fof(f6982,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl13_6
    | ~ spl13_405
    | ~ spl13_907 ),
    inference(unit_resulting_resolution,[],[f3034,f6973,f432])).

fof(f6973,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl13_907 ),
    inference(avatar_component_clause,[],[f6972])).

fof(f3034,plain,
    ( k1_zfmisc_1(sK3) != o_0_0_xboole_0
    | ~ spl13_405 ),
    inference(avatar_component_clause,[],[f3033])).

fof(f6990,plain,
    ( ~ spl13_909
    | spl13_409
    | spl13_907 ),
    inference(avatar_split_clause,[],[f6978,f6972,f3064,f6988])).

fof(f6988,plain,
    ( spl13_909
  <=> ~ r1_tarski(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_909])])).

fof(f3064,plain,
    ( spl13_409
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_409])])).

fof(f6978,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK3)
    | ~ spl13_409
    | ~ spl13_907 ),
    inference(unit_resulting_resolution,[],[f6973,f3260])).

fof(f3260,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | r2_hidden(X0,k1_zfmisc_1(sK3)) )
    | ~ spl13_409 ),
    inference(resolution,[],[f3069,f126])).

fof(f3069,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
        | r2_hidden(X0,k1_zfmisc_1(sK3)) )
    | ~ spl13_409 ),
    inference(resolution,[],[f3065,f122])).

fof(f3065,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl13_409 ),
    inference(avatar_component_clause,[],[f3064])).

fof(f6977,plain,
    ( spl13_906
    | ~ spl13_422
    | ~ spl13_892 ),
    inference(avatar_split_clause,[],[f6928,f6838,f3151,f6975])).

fof(f6838,plain,
    ( spl13_892
  <=> o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_892])])).

fof(f6928,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl13_422
    | ~ spl13_892 ),
    inference(backward_demodulation,[],[f6839,f3152])).

fof(f6839,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK3))
    | ~ spl13_892 ),
    inference(avatar_component_clause,[],[f6838])).

fof(f6926,plain,
    ( spl13_904
    | ~ spl13_6
    | spl13_893 ),
    inference(avatar_split_clause,[],[f6866,f6835,f161,f6924])).

fof(f6866,plain,
    ( r2_hidden(sK10(sK10(k1_zfmisc_1(sK3))),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_6
    | ~ spl13_893 ),
    inference(unit_resulting_resolution,[],[f162,f119,f6836,f431])).

fof(f6919,plain,
    ( ~ spl13_903
    | ~ spl13_6
    | spl13_893 ),
    inference(avatar_split_clause,[],[f6859,f6835,f161,f6917])).

fof(f6859,plain,
    ( ~ r2_hidden(sK10(k1_zfmisc_1(sK3)),sK10(sK10(k1_zfmisc_1(sK3))))
    | ~ spl13_6
    | ~ spl13_893 ),
    inference(unit_resulting_resolution,[],[f119,f6836,f838])).

fof(f6908,plain,
    ( ~ spl13_901
    | ~ spl13_240
    | spl13_899 ),
    inference(avatar_split_clause,[],[f6886,f6883,f1735,f6906])).

fof(f6883,plain,
    ( spl13_899
  <=> ~ m1_subset_1(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_899])])).

fof(f6886,plain,
    ( ~ r1_tarski(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_899 ),
    inference(unit_resulting_resolution,[],[f6884,f1738])).

fof(f6884,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0)
    | ~ spl13_899 ),
    inference(avatar_component_clause,[],[f6883])).

fof(f6885,plain,
    ( ~ spl13_899
    | ~ spl13_6
    | ~ spl13_240
    | spl13_893 ),
    inference(avatar_split_clause,[],[f6861,f6835,f1735,f161,f6883])).

fof(f6861,plain,
    ( ~ m1_subset_1(sK10(k1_zfmisc_1(sK3)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_893 ),
    inference(unit_resulting_resolution,[],[f119,f6836,f3204])).

fof(f6875,plain,
    ( ~ spl13_897
    | ~ spl13_6
    | spl13_893 ),
    inference(avatar_split_clause,[],[f6867,f6835,f161,f6873])).

fof(f6867,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_6
    | ~ spl13_893 ),
    inference(unit_resulting_resolution,[],[f162,f6836,f127])).

fof(f6846,plain,
    ( spl13_892
    | ~ spl13_895
    | ~ spl13_6
    | spl13_421 ),
    inference(avatar_split_clause,[],[f3154,f3144,f161,f6844,f6838])).

fof(f3144,plain,
    ( spl13_421
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_421])])).

fof(f3154,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3)))
    | o_0_0_xboole_0 = sK10(k1_zfmisc_1(sK3))
    | ~ spl13_6
    | ~ spl13_421 ),
    inference(resolution,[],[f3145,f432])).

fof(f3145,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_421 ),
    inference(avatar_component_clause,[],[f3144])).

fof(f6807,plain,
    ( ~ spl13_891
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_704
    | spl13_771 ),
    inference(avatar_split_clause,[],[f6039,f6035,f5565,f288,f182,f154,f147,f140,f6805])).

fof(f6805,plain,
    ( spl13_891
  <=> ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK8(sK0,sK1,sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_891])])).

fof(f6035,plain,
    ( spl13_771
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_771])])).

fof(f6039,plain,
    ( ~ r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK8(sK0,sK1,sK3,o_0_0_xboole_0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36
    | ~ spl13_704
    | ~ spl13_771 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f289,f5566,f6036,f115])).

fof(f6036,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK2)
    | ~ spl13_771 ),
    inference(avatar_component_clause,[],[f6035])).

fof(f6717,plain,
    ( ~ spl13_889
    | spl13_877 ),
    inference(avatar_split_clause,[],[f6617,f6613,f6715])).

fof(f6715,plain,
    ( spl13_889
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_889])])).

fof(f6613,plain,
    ( spl13_877
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_877])])).

fof(f6617,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK3))))))
    | ~ spl13_877 ),
    inference(unit_resulting_resolution,[],[f119,f6614,f130])).

fof(f6614,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK3))))
    | ~ spl13_877 ),
    inference(avatar_component_clause,[],[f6613])).

fof(f6684,plain,
    ( ~ spl13_887
    | spl13_865 ),
    inference(avatar_split_clause,[],[f6605,f6539,f6682])).

fof(f6682,plain,
    ( spl13_887
  <=> ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(sK10(sK10(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_887])])).

fof(f6539,plain,
    ( spl13_865
  <=> ~ m1_subset_1(sK10(sK3),sK10(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_865])])).

fof(f6605,plain,
    ( ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(sK10(sK10(sK3)))))
    | ~ spl13_865 ),
    inference(unit_resulting_resolution,[],[f119,f6540,f130])).

fof(f6540,plain,
    ( ~ m1_subset_1(sK10(sK3),sK10(sK10(sK3)))
    | ~ spl13_865 ),
    inference(avatar_component_clause,[],[f6539])).

fof(f6677,plain,
    ( spl13_884
    | ~ spl13_6
    | spl13_863 ),
    inference(avatar_split_clause,[],[f6553,f6530,f161,f6675])).

fof(f6530,plain,
    ( spl13_863
  <=> o_0_0_xboole_0 != sK10(sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_863])])).

fof(f6553,plain,
    ( r2_hidden(sK10(sK10(sK10(sK3))),sK10(sK10(sK3)))
    | ~ spl13_6
    | ~ spl13_863 ),
    inference(unit_resulting_resolution,[],[f162,f119,f6531,f431])).

fof(f6531,plain,
    ( o_0_0_xboole_0 != sK10(sK10(sK3))
    | ~ spl13_863 ),
    inference(avatar_component_clause,[],[f6530])).

fof(f6670,plain,
    ( ~ spl13_883
    | ~ spl13_6
    | spl13_863 ),
    inference(avatar_split_clause,[],[f6546,f6530,f161,f6668])).

fof(f6668,plain,
    ( spl13_883
  <=> ~ r2_hidden(sK10(sK10(sK3)),sK10(sK10(sK10(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_883])])).

fof(f6546,plain,
    ( ~ r2_hidden(sK10(sK10(sK3)),sK10(sK10(sK10(sK3))))
    | ~ spl13_6
    | ~ spl13_863 ),
    inference(unit_resulting_resolution,[],[f119,f6531,f838])).

fof(f6662,plain,
    ( ~ spl13_881
    | spl13_877 ),
    inference(avatar_split_clause,[],[f6618,f6613,f6660])).

fof(f6660,plain,
    ( spl13_881
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK10(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_881])])).

fof(f6618,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK10(sK3))))
    | ~ spl13_877 ),
    inference(unit_resulting_resolution,[],[f6614,f121])).

fof(f6628,plain,
    ( ~ spl13_879
    | spl13_877 ),
    inference(avatar_split_clause,[],[f6616,f6613,f6626])).

fof(f6626,plain,
    ( spl13_879
  <=> ~ r1_tarski(sK3,sK10(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_879])])).

fof(f6616,plain,
    ( ~ r1_tarski(sK3,sK10(sK10(sK3)))
    | ~ spl13_877 ),
    inference(unit_resulting_resolution,[],[f6614,f126])).

fof(f6615,plain,
    ( ~ spl13_877
    | ~ spl13_330
    | spl13_865 ),
    inference(avatar_split_clause,[],[f6604,f6539,f2423,f6613])).

fof(f2423,plain,
    ( spl13_330
  <=> r2_hidden(sK10(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_330])])).

fof(f6604,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK3))))
    | ~ spl13_330
    | ~ spl13_865 ),
    inference(unit_resulting_resolution,[],[f2424,f6540,f130])).

fof(f2424,plain,
    ( r2_hidden(sK10(sK3),sK3)
    | ~ spl13_330 ),
    inference(avatar_component_clause,[],[f2423])).

fof(f6603,plain,
    ( spl13_874
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5446,f5232,f4398,f339,f182,f154,f147,f140,f6601])).

fof(f6601,plain,
    ( spl13_874
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_874])])).

fof(f5446,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4438])).

fof(f4438,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f4399,f116])).

fof(f6596,plain,
    ( ~ spl13_873
    | ~ spl13_240
    | spl13_871 ),
    inference(avatar_split_clause,[],[f6580,f6577,f1735,f6594])).

fof(f6594,plain,
    ( spl13_873
  <=> ~ r1_tarski(sK10(sK10(sK3)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_873])])).

fof(f6580,plain,
    ( ~ r1_tarski(sK10(sK10(sK3)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_871 ),
    inference(unit_resulting_resolution,[],[f6578,f1738])).

fof(f6579,plain,
    ( ~ spl13_871
    | ~ spl13_6
    | ~ spl13_240
    | spl13_863 ),
    inference(avatar_split_clause,[],[f6548,f6530,f1735,f161,f6577])).

fof(f6548,plain,
    ( ~ m1_subset_1(sK10(sK10(sK3)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_863 ),
    inference(unit_resulting_resolution,[],[f119,f6531,f3204])).

fof(f6569,plain,
    ( spl13_868
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5441,f5232,f4398,f359,f182,f154,f147,f140,f6567])).

fof(f6567,plain,
    ( spl13_868
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_868])])).

fof(f5441,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4432])).

fof(f4432,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f360,f4399,f109])).

fof(f6562,plain,
    ( ~ spl13_867
    | ~ spl13_6
    | spl13_863 ),
    inference(avatar_split_clause,[],[f6554,f6530,f161,f6560])).

fof(f6560,plain,
    ( spl13_867
  <=> ~ v1_xboole_0(sK10(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_867])])).

fof(f6554,plain,
    ( ~ v1_xboole_0(sK10(sK10(sK3)))
    | ~ spl13_6
    | ~ spl13_863 ),
    inference(unit_resulting_resolution,[],[f162,f6531,f127])).

fof(f6541,plain,
    ( spl13_862
    | ~ spl13_865
    | ~ spl13_6
    | spl13_385 ),
    inference(avatar_split_clause,[],[f2898,f2880,f161,f6539,f6533])).

fof(f6533,plain,
    ( spl13_862
  <=> o_0_0_xboole_0 = sK10(sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_862])])).

fof(f2880,plain,
    ( spl13_385
  <=> ~ r2_hidden(sK10(sK3),sK10(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_385])])).

fof(f2898,plain,
    ( ~ m1_subset_1(sK10(sK3),sK10(sK10(sK3)))
    | o_0_0_xboole_0 = sK10(sK10(sK3))
    | ~ spl13_6
    | ~ spl13_385 ),
    inference(resolution,[],[f2881,f432])).

fof(f2881,plain,
    ( ~ r2_hidden(sK10(sK3),sK10(sK10(sK3)))
    | ~ spl13_385 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f6527,plain,
    ( ~ spl13_861
    | spl13_847 ),
    inference(avatar_split_clause,[],[f6459,f6436,f6525])).

fof(f6525,plain,
    ( spl13_861
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_861])])).

fof(f6459,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))))
    | ~ spl13_847 ),
    inference(unit_resulting_resolution,[],[f119,f6437,f130])).

fof(f6520,plain,
    ( spl13_858
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5440,f5232,f4398,f294,f182,f154,f147,f140,f6518])).

fof(f6518,plain,
    ( spl13_858
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_858])])).

fof(f5440,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4431])).

fof(f4431,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f4399,f109])).

fof(f6486,plain,
    ( ~ spl13_857
    | spl13_847 ),
    inference(avatar_split_clause,[],[f6460,f6436,f6484])).

fof(f6460,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_847 ),
    inference(unit_resulting_resolution,[],[f6437,f121])).

fof(f6477,plain,
    ( ~ spl13_855
    | spl13_847 ),
    inference(avatar_split_clause,[],[f6458,f6436,f6475])).

fof(f6458,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_847 ),
    inference(unit_resulting_resolution,[],[f6437,f126])).

fof(f6470,plain,
    ( spl13_852
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5436,f5232,f934,f359,f182,f154,f147,f140,f6468])).

fof(f6468,plain,
    ( spl13_852
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_852])])).

fof(f5436,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4283])).

fof(f4283,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f935,f360,f109])).

fof(f6452,plain,
    ( ~ spl13_851
    | spl13_823 ),
    inference(avatar_split_clause,[],[f6342,f6317,f6450])).

fof(f6450,plain,
    ( spl13_851
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_851])])).

fof(f6317,plain,
    ( spl13_823
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_823])])).

fof(f6342,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))))
    | ~ spl13_823 ),
    inference(unit_resulting_resolution,[],[f119,f6318,f130])).

fof(f6318,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_823 ),
    inference(avatar_component_clause,[],[f6317])).

fof(f6445,plain,
    ( ~ spl13_849
    | spl13_821 ),
    inference(avatar_split_clause,[],[f6322,f6310,f6443])).

fof(f6443,plain,
    ( spl13_849
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_849])])).

fof(f6310,plain,
    ( spl13_821
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_821])])).

fof(f6322,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2))))))
    | ~ spl13_821 ),
    inference(unit_resulting_resolution,[],[f119,f6311,f130])).

fof(f6311,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_821 ),
    inference(avatar_component_clause,[],[f6310])).

fof(f6438,plain,
    ( ~ spl13_847
    | ~ spl13_412
    | spl13_821 ),
    inference(avatar_split_clause,[],[f6321,f6310,f3089,f6436])).

fof(f3089,plain,
    ( spl13_412
  <=> r2_hidden(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_412])])).

fof(f6321,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_412
    | ~ spl13_821 ),
    inference(unit_resulting_resolution,[],[f3090,f6311,f130])).

fof(f3090,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK3))
    | ~ spl13_412 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f6431,plain,
    ( spl13_844
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5432,f5232,f883,f359,f182,f154,f147,f140,f6429])).

fof(f6429,plain,
    ( spl13_844
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_844])])).

fof(f5432,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4278])).

fof(f4278,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f884,f360,f109])).

fof(f6405,plain,
    ( ~ spl13_843
    | spl13_809 ),
    inference(avatar_split_clause,[],[f6302,f6235,f6403])).

fof(f6403,plain,
    ( spl13_843
  <=> ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(sK10(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_843])])).

fof(f6235,plain,
    ( spl13_809
  <=> ~ m1_subset_1(sK10(sK2),sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_809])])).

fof(f6302,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(sK10(sK10(sK2)))))
    | ~ spl13_809 ),
    inference(unit_resulting_resolution,[],[f119,f6236,f130])).

fof(f6236,plain,
    ( ~ m1_subset_1(sK10(sK2),sK10(sK10(sK2)))
    | ~ spl13_809 ),
    inference(avatar_component_clause,[],[f6235])).

fof(f6397,plain,
    ( spl13_840
    | ~ spl13_544
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5383,f5232,f4019,f6395])).

fof(f6395,plain,
    ( spl13_840
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_840])])).

fof(f4019,plain,
    ( spl13_544
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_544])])).

fof(f5383,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_544
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4020])).

fof(f4020,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_544 ),
    inference(avatar_component_clause,[],[f4019])).

fof(f6390,plain,
    ( spl13_838
    | ~ spl13_6
    | spl13_807 ),
    inference(avatar_split_clause,[],[f6249,f6226,f161,f6388])).

fof(f6226,plain,
    ( spl13_807
  <=> o_0_0_xboole_0 != sK10(sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_807])])).

fof(f6249,plain,
    ( r2_hidden(sK10(sK10(sK10(sK2))),sK10(sK10(sK2)))
    | ~ spl13_6
    | ~ spl13_807 ),
    inference(unit_resulting_resolution,[],[f162,f119,f6227,f431])).

fof(f6227,plain,
    ( o_0_0_xboole_0 != sK10(sK10(sK2))
    | ~ spl13_807 ),
    inference(avatar_component_clause,[],[f6226])).

fof(f6383,plain,
    ( ~ spl13_837
    | ~ spl13_6
    | spl13_807 ),
    inference(avatar_split_clause,[],[f6242,f6226,f161,f6381])).

fof(f6381,plain,
    ( spl13_837
  <=> ~ r2_hidden(sK10(sK10(sK2)),sK10(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_837])])).

fof(f6242,plain,
    ( ~ r2_hidden(sK10(sK10(sK2)),sK10(sK10(sK10(sK2))))
    | ~ spl13_6
    | ~ spl13_807 ),
    inference(unit_resulting_resolution,[],[f119,f6227,f838])).

fof(f6374,plain,
    ( ~ spl13_835
    | spl13_823 ),
    inference(avatar_split_clause,[],[f6343,f6317,f6372])).

fof(f6372,plain,
    ( spl13_835
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_835])])).

fof(f6343,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_823 ),
    inference(unit_resulting_resolution,[],[f6318,f121])).

fof(f6367,plain,
    ( spl13_832
    | ~ spl13_538
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5382,f5232,f3987,f6365])).

fof(f6365,plain,
    ( spl13_832
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_832])])).

fof(f3987,plain,
    ( spl13_538
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_538])])).

fof(f5382,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_538
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3988])).

fof(f3988,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_538 ),
    inference(avatar_component_clause,[],[f3987])).

fof(f6360,plain,
    ( ~ spl13_831
    | spl13_821 ),
    inference(avatar_split_clause,[],[f6323,f6310,f6358])).

fof(f6358,plain,
    ( spl13_831
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK10(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_831])])).

fof(f6323,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_821 ),
    inference(unit_resulting_resolution,[],[f6311,f121])).

fof(f6353,plain,
    ( ~ spl13_829
    | spl13_823 ),
    inference(avatar_split_clause,[],[f6341,f6317,f6351])).

fof(f6351,plain,
    ( spl13_829
  <=> ~ r1_tarski(sK3,sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_829])])).

fof(f6341,plain,
    ( ~ r1_tarski(sK3,sK10(sK10(sK2)))
    | ~ spl13_823 ),
    inference(unit_resulting_resolution,[],[f6318,f126])).

fof(f6340,plain,
    ( ~ spl13_827
    | spl13_533
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5381,f5232,f3959,f6338])).

fof(f6338,plain,
    ( spl13_827
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_827])])).

fof(f3959,plain,
    ( spl13_533
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_533])])).

fof(f5381,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_533
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3960])).

fof(f3960,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_533 ),
    inference(avatar_component_clause,[],[f3959])).

fof(f6333,plain,
    ( ~ spl13_825
    | spl13_821 ),
    inference(avatar_split_clause,[],[f6320,f6310,f6331])).

fof(f6331,plain,
    ( spl13_825
  <=> ~ r1_tarski(sK2,sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_825])])).

fof(f6320,plain,
    ( ~ r1_tarski(sK2,sK10(sK10(sK2)))
    | ~ spl13_821 ),
    inference(unit_resulting_resolution,[],[f6311,f126])).

fof(f6319,plain,
    ( ~ spl13_823
    | ~ spl13_344
    | spl13_809 ),
    inference(avatar_split_clause,[],[f6301,f6235,f2519,f6317])).

fof(f6301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_344
    | ~ spl13_809 ),
    inference(unit_resulting_resolution,[],[f2520,f6236,f130])).

fof(f6312,plain,
    ( ~ spl13_821
    | ~ spl13_328
    | spl13_809 ),
    inference(avatar_split_clause,[],[f6300,f6235,f2416,f6310])).

fof(f6300,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK10(sK2))))
    | ~ spl13_328
    | ~ spl13_809 ),
    inference(unit_resulting_resolution,[],[f2417,f6236,f130])).

fof(f6299,plain,
    ( ~ spl13_819
    | spl13_529
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5380,f5232,f3932,f6297])).

fof(f6297,plain,
    ( spl13_819
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_819])])).

fof(f3932,plain,
    ( spl13_529
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_529])])).

fof(f5380,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_529
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3933])).

fof(f3933,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_529 ),
    inference(avatar_component_clause,[],[f3932])).

fof(f6292,plain,
    ( ~ spl13_817
    | ~ spl13_240
    | spl13_815 ),
    inference(avatar_split_clause,[],[f6276,f6273,f1735,f6290])).

fof(f6290,plain,
    ( spl13_817
  <=> ~ r1_tarski(sK10(sK10(sK2)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_817])])).

fof(f6276,plain,
    ( ~ r1_tarski(sK10(sK10(sK2)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_815 ),
    inference(unit_resulting_resolution,[],[f6274,f1738])).

fof(f6275,plain,
    ( ~ spl13_815
    | ~ spl13_6
    | ~ spl13_240
    | spl13_807 ),
    inference(avatar_split_clause,[],[f6244,f6226,f1735,f161,f6273])).

fof(f6244,plain,
    ( ~ m1_subset_1(sK10(sK10(sK2)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_807 ),
    inference(unit_resulting_resolution,[],[f119,f6227,f3204])).

fof(f6265,plain,
    ( ~ spl13_813
    | spl13_525
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5379,f5232,f3909,f6263])).

fof(f3909,plain,
    ( spl13_525
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_525])])).

fof(f5379,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_525
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3910])).

fof(f3910,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_525 ),
    inference(avatar_component_clause,[],[f3909])).

fof(f6258,plain,
    ( ~ spl13_811
    | ~ spl13_6
    | spl13_807 ),
    inference(avatar_split_clause,[],[f6250,f6226,f161,f6256])).

fof(f6256,plain,
    ( spl13_811
  <=> ~ v1_xboole_0(sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_811])])).

fof(f6250,plain,
    ( ~ v1_xboole_0(sK10(sK10(sK2)))
    | ~ spl13_6
    | ~ spl13_807 ),
    inference(unit_resulting_resolution,[],[f162,f6227,f127])).

fof(f6237,plain,
    ( spl13_806
    | ~ spl13_809
    | ~ spl13_6
    | spl13_365 ),
    inference(avatar_split_clause,[],[f2721,f2688,f161,f6235,f6229])).

fof(f6229,plain,
    ( spl13_806
  <=> o_0_0_xboole_0 = sK10(sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_806])])).

fof(f2688,plain,
    ( spl13_365
  <=> ~ r2_hidden(sK10(sK2),sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_365])])).

fof(f2721,plain,
    ( ~ m1_subset_1(sK10(sK2),sK10(sK10(sK2)))
    | o_0_0_xboole_0 = sK10(sK10(sK2))
    | ~ spl13_6
    | ~ spl13_365 ),
    inference(resolution,[],[f2689,f432])).

fof(f2689,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(sK10(sK2)))
    | ~ spl13_365 ),
    inference(avatar_component_clause,[],[f2688])).

fof(f6219,plain,
    ( spl13_804
    | ~ spl13_522
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5377,f5232,f3882,f6217])).

fof(f6217,plain,
    ( spl13_804
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_804])])).

fof(f3882,plain,
    ( spl13_522
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_522])])).

fof(f5377,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_522
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3883])).

fof(f3883,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_522 ),
    inference(avatar_component_clause,[],[f3882])).

fof(f6184,plain,
    ( spl13_802
    | ~ spl13_504
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5376,f5232,f3802,f6182])).

fof(f6182,plain,
    ( spl13_802
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_802])])).

fof(f3802,plain,
    ( spl13_504
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_504])])).

fof(f5376,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_504
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3803])).

fof(f3803,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_504 ),
    inference(avatar_component_clause,[],[f3802])).

fof(f6166,plain,
    ( ~ spl13_801
    | ~ spl13_6
    | spl13_199
    | ~ spl13_664 ),
    inference(avatar_split_clause,[],[f5185,f5043,f1155,f161,f6164])).

fof(f6164,plain,
    ( spl13_801
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_801])])).

fof(f5043,plain,
    ( spl13_664
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_664])])).

fof(f5185,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_664 ),
    inference(unit_resulting_resolution,[],[f1156,f5044,f838])).

fof(f5044,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_664 ),
    inference(avatar_component_clause,[],[f5043])).

fof(f6158,plain,
    ( spl13_798
    | ~ spl13_500
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5375,f5232,f3767,f6156])).

fof(f6156,plain,
    ( spl13_798
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_798])])).

fof(f3767,plain,
    ( spl13_500
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_500])])).

fof(f5375,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_500
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3768])).

fof(f3768,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_500 ),
    inference(avatar_component_clause,[],[f3767])).

fof(f6151,plain,
    ( spl13_796
    | ~ spl13_6
    | spl13_199
    | ~ spl13_664 ),
    inference(avatar_split_clause,[],[f5182,f5043,f1155,f161,f6149])).

fof(f5182,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_664 ),
    inference(unit_resulting_resolution,[],[f1156,f5044,f432])).

fof(f6144,plain,
    ( ~ spl13_795
    | ~ spl13_6
    | spl13_199
    | ~ spl13_658 ),
    inference(avatar_split_clause,[],[f5146,f5022,f1155,f161,f6142])).

fof(f6142,plain,
    ( spl13_795
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_795])])).

fof(f5022,plain,
    ( spl13_658
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_658])])).

fof(f5146,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_658 ),
    inference(unit_resulting_resolution,[],[f1156,f5023,f838])).

fof(f5023,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_658 ),
    inference(avatar_component_clause,[],[f5022])).

fof(f6137,plain,
    ( spl13_792
    | ~ spl13_6
    | spl13_199
    | ~ spl13_658 ),
    inference(avatar_split_clause,[],[f5143,f5022,f1155,f161,f6135])).

fof(f6135,plain,
    ( spl13_792
  <=> r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_792])])).

fof(f5143,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_658 ),
    inference(unit_resulting_resolution,[],[f1156,f5023,f432])).

fof(f6130,plain,
    ( ~ spl13_791
    | ~ spl13_6
    | spl13_199
    | ~ spl13_654 ),
    inference(avatar_split_clause,[],[f5119,f5006,f1155,f161,f6128])).

fof(f6128,plain,
    ( spl13_791
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_791])])).

fof(f5006,plain,
    ( spl13_654
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_654])])).

fof(f5119,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_654 ),
    inference(unit_resulting_resolution,[],[f1156,f5007,f838])).

fof(f5007,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_654 ),
    inference(avatar_component_clause,[],[f5006])).

fof(f6123,plain,
    ( spl13_788
    | ~ spl13_6
    | spl13_199
    | ~ spl13_654 ),
    inference(avatar_split_clause,[],[f5116,f5006,f1155,f161,f6121])).

fof(f6121,plain,
    ( spl13_788
  <=> r2_hidden(sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_788])])).

fof(f5116,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_654 ),
    inference(unit_resulting_resolution,[],[f1156,f5007,f432])).

fof(f6116,plain,
    ( spl13_786
    | ~ spl13_490
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5374,f5232,f3727,f6114])).

fof(f6114,plain,
    ( spl13_786
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_786])])).

fof(f3727,plain,
    ( spl13_490
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_490])])).

fof(f5374,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_490
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3728])).

fof(f3728,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_490 ),
    inference(avatar_component_clause,[],[f3727])).

fof(f6109,plain,
    ( spl13_784
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_166
    | spl13_201 ),
    inference(avatar_split_clause,[],[f4335,f1183,f903,f876,f633,f460,f6107])).

fof(f6107,plain,
    ( spl13_784
  <=> m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_784])])).

fof(f460,plain,
    ( spl13_76
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f633,plain,
    ( spl13_112
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f876,plain,
    ( spl13_160
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_160])])).

fof(f4335,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_166
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f461,f634,f877,f904,f761])).

fof(f761,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_funct_1(X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f760])).

fof(f760,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_funct_1(X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f132,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',redefinition_k3_funct_2)).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_k3_funct_2)).

fof(f877,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_160 ),
    inference(avatar_component_clause,[],[f876])).

fof(f634,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f633])).

fof(f461,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl13_76 ),
    inference(avatar_component_clause,[],[f460])).

fof(f6100,plain,
    ( spl13_782
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_148
    | ~ spl13_160
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1832,f1183,f876,f811,f633,f460,f6098])).

fof(f6098,plain,
    ( spl13_782
  <=> m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_782])])).

fof(f811,plain,
    ( spl13_148
  <=> m1_subset_1(sK6(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f1832,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_148
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(backward_demodulation,[],[f1826,f1829])).

fof(f1829,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_148
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f812,f461,f634,f877,f132])).

fof(f812,plain,
    ( m1_subset_1(sK6(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_148 ),
    inference(avatar_component_clause,[],[f811])).

fof(f1826,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK6(sK0,sK1,o_0_0_xboole_0)) = k1_funct_1(u1_waybel_0(sK0,sK1),sK6(sK0,sK1,o_0_0_xboole_0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_148
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f812,f461,f634,f877,f133])).

fof(f6092,plain,
    ( ~ spl13_781
    | spl13_439
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5469,f5232,f3332,f6090])).

fof(f6090,plain,
    ( spl13_781
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_781])])).

fof(f3332,plain,
    ( spl13_439
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_439])])).

fof(f5469,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_439
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f5264])).

fof(f5264,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_439 ),
    inference(unit_resulting_resolution,[],[f3333,f121])).

fof(f3333,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_439 ),
    inference(avatar_component_clause,[],[f3332])).

fof(f6079,plain,
    ( spl13_778
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5449,f5232,f4398,f182,f154,f147,f140,f6077])).

fof(f5449,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4441])).

fof(f4441,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f4399,f129])).

fof(f6071,plain,
    ( spl13_776
    | ~ spl13_440
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5372,f5232,f3365,f6069])).

fof(f3365,plain,
    ( spl13_440
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_440])])).

fof(f5372,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_440
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3366])).

fof(f3366,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_440 ),
    inference(avatar_component_clause,[],[f3365])).

fof(f6064,plain,
    ( ~ spl13_775
    | spl13_611
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5460,f5232,f4565,f6062])).

fof(f6062,plain,
    ( spl13_775
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_775])])).

fof(f4565,plain,
    ( spl13_611
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_611])])).

fof(f5460,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_611
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4579])).

fof(f4579,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_611 ),
    inference(unit_resulting_resolution,[],[f119,f4566,f130])).

fof(f4566,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1))
    | ~ spl13_611 ),
    inference(avatar_component_clause,[],[f4565])).

fof(f6053,plain,
    ( ~ spl13_773
    | spl13_261
    | ~ spl13_444
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5373,f5232,f3379,f2026,f6051])).

fof(f6051,plain,
    ( spl13_773
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_773])])).

fof(f5373,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK2)
    | ~ spl13_261
    | ~ spl13_444
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3404])).

fof(f3404,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_261
    | ~ spl13_444 ),
    inference(unit_resulting_resolution,[],[f2027,f3380])).

fof(f6037,plain,
    ( ~ spl13_771
    | ~ spl13_46
    | spl13_261
    | spl13_323
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5370,f5232,f2369,f2026,f325,f6035])).

fof(f5370,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK2)
    | ~ spl13_46
    | ~ spl13_261
    | ~ spl13_323
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3343])).

fof(f3343,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_46
    | ~ spl13_261
    | ~ spl13_323 ),
    inference(unit_resulting_resolution,[],[f2027,f326,f2554])).

fof(f6030,plain,
    ( ~ spl13_769
    | spl13_439
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5369,f5232,f3332,f6028])).

fof(f6028,plain,
    ( spl13_769
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_769])])).

fof(f5369,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_439
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3333])).

fof(f6022,plain,
    ( ~ spl13_767
    | ~ spl13_764 ),
    inference(avatar_split_clause,[],[f6006,f5997,f6020])).

fof(f6020,plain,
    ( spl13_767
  <=> ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_767])])).

fof(f6006,plain,
    ( ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)))
    | ~ spl13_764 ),
    inference(unit_resulting_resolution,[],[f5998,f120])).

fof(f5999,plain,
    ( spl13_764
    | spl13_323
    | ~ spl13_396
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5366,f5232,f2962,f2369,f5997])).

fof(f2962,plain,
    ( spl13_396
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_396])])).

fof(f5366,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_323
    | ~ spl13_396
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3093])).

fof(f3093,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_323
    | ~ spl13_396 ),
    inference(unit_resulting_resolution,[],[f2370,f2963,f122])).

fof(f2963,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_396 ),
    inference(avatar_component_clause,[],[f2962])).

fof(f5992,plain,
    ( spl13_762
    | ~ spl13_436
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5367,f5232,f3284,f5990])).

fof(f5990,plain,
    ( spl13_762
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_762])])).

fof(f3284,plain,
    ( spl13_436
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_436])])).

fof(f5367,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_436
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f3285])).

fof(f3285,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_436 ),
    inference(avatar_component_clause,[],[f3284])).

fof(f5985,plain,
    ( ~ spl13_761
    | spl13_261
    | spl13_323
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5362,f5232,f2369,f2026,f5983])).

fof(f5362,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_261
    | ~ spl13_323
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2376])).

fof(f2376,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_261
    | ~ spl13_323 ),
    inference(unit_resulting_resolution,[],[f2027,f2370,f122])).

fof(f5947,plain,
    ( ~ spl13_759
    | ~ spl13_6
    | spl13_281
    | spl13_443
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5480,f5232,f3373,f2149,f161,f5945])).

fof(f5945,plain,
    ( spl13_759
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_759])])).

fof(f5480,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_6
    | ~ spl13_281
    | ~ spl13_443
    | ~ spl13_680 ),
    inference(subsumption_resolution,[],[f5358,f3374])).

fof(f5358,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | o_0_0_xboole_0 = sK2
    | ~ spl13_6
    | ~ spl13_281
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2273])).

fof(f5940,plain,
    ( spl13_756
    | ~ spl13_666
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5464,f5232,f5050,f5938])).

fof(f5938,plain,
    ( spl13_756
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_756])])).

fof(f5050,plain,
    ( spl13_666
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_666])])).

fof(f5464,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_666
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f5051])).

fof(f5051,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_666 ),
    inference(avatar_component_clause,[],[f5050])).

fof(f5933,plain,
    ( ~ spl13_755
    | spl13_657
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5463,f5232,f5014,f5931])).

fof(f5931,plain,
    ( spl13_755
  <=> ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_755])])).

fof(f5014,plain,
    ( spl13_657
  <=> ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_657])])).

fof(f5463,plain,
    ( ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)))
    | ~ spl13_657
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f5015])).

fof(f5015,plain,
    ( ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))))
    | ~ spl13_657 ),
    inference(avatar_component_clause,[],[f5014])).

fof(f5926,plain,
    ( ~ spl13_753
    | spl13_653
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5462,f5232,f4982,f5924])).

fof(f5924,plain,
    ( spl13_753
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_753])])).

fof(f4982,plain,
    ( spl13_653
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_653])])).

fof(f5462,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_653
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4983])).

fof(f4983,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_653 ),
    inference(avatar_component_clause,[],[f4982])).

fof(f5919,plain,
    ( spl13_750
    | ~ spl13_396
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5365,f5232,f2962,f5917])).

fof(f5365,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK3)
    | ~ spl13_396
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2963])).

fof(f5912,plain,
    ( spl13_748
    | ~ spl13_394
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5364,f5232,f2937,f5910])).

fof(f5364,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_394
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2938])).

fof(f5905,plain,
    ( ~ spl13_747
    | spl13_389
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5363,f5232,f2895,f5903])).

fof(f5903,plain,
    ( spl13_747
  <=> ~ r2_hidden(sK2,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_747])])).

fof(f2895,plain,
    ( spl13_389
  <=> ~ r2_hidden(sK2,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_389])])).

fof(f5363,plain,
    ( ~ r2_hidden(sK2,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)))
    | ~ spl13_389
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2896])).

fof(f2896,plain,
    ( ~ r2_hidden(sK2,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))))
    | ~ spl13_389 ),
    inference(avatar_component_clause,[],[f2895])).

fof(f5842,plain,
    ( ~ spl13_745
    | spl13_611
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5458,f5232,f4565,f5840])).

fof(f5840,plain,
    ( spl13_745
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_745])])).

fof(f5458,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK4(sK1))
    | ~ spl13_611
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4566])).

fof(f5819,plain,
    ( spl13_742
    | ~ spl13_598
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5452,f5232,f4500,f5817])).

fof(f5817,plain,
    ( spl13_742
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_742])])).

fof(f4500,plain,
    ( spl13_598
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_598])])).

fof(f5452,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_598
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4501])).

fof(f4501,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_598 ),
    inference(avatar_component_clause,[],[f4500])).

fof(f5802,plain,
    ( spl13_740
    | ~ spl13_306
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5359,f5232,f2278,f5800])).

fof(f2278,plain,
    ( spl13_306
  <=> r2_hidden(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_306])])).

fof(f5359,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_306
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2279])).

fof(f2279,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_306 ),
    inference(avatar_component_clause,[],[f2278])).

fof(f5795,plain,
    ( ~ spl13_739
    | spl13_305
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5357,f5232,f2267,f5793])).

fof(f5793,plain,
    ( spl13_739
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_739])])).

fof(f2267,plain,
    ( spl13_305
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_305])])).

fof(f5357,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_305
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2268])).

fof(f2268,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_305 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f5788,plain,
    ( spl13_736
    | ~ spl13_302
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5356,f5232,f2263,f5786])).

fof(f2263,plain,
    ( spl13_302
  <=> r2_hidden(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_302])])).

fof(f5356,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_302
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2264])).

fof(f2264,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_302 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f5781,plain,
    ( spl13_734
    | ~ spl13_290
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5347,f5232,f2211,f5779])).

fof(f5779,plain,
    ( spl13_734
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_734])])).

fof(f2211,plain,
    ( spl13_290
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_290])])).

fof(f5347,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_290
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2212])).

fof(f2212,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_290 ),
    inference(avatar_component_clause,[],[f2211])).

fof(f5774,plain,
    ( spl13_732
    | ~ spl13_300
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5355,f5232,f2256,f5772])).

fof(f5772,plain,
    ( spl13_732
  <=> m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_732])])).

fof(f2256,plain,
    ( spl13_300
  <=> m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_300])])).

fof(f5355,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl13_300
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2257])).

fof(f2257,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl13_300 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f5754,plain,
    ( ~ spl13_731
    | spl13_281
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5345,f5232,f2149,f5752])).

fof(f5752,plain,
    ( spl13_731
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_731])])).

fof(f5345,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,o_0_0_xboole_0)),sK2)
    | ~ spl13_281
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2150])).

fof(f5746,plain,
    ( ~ spl13_729
    | spl13_609
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5456,f5232,f4541,f5744])).

fof(f5744,plain,
    ( spl13_729
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_729])])).

fof(f4541,plain,
    ( spl13_609
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_609])])).

fof(f5456,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,o_0_0_xboole_0))
    | ~ spl13_609
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4542])).

fof(f4542,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_609 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f5739,plain,
    ( spl13_726
    | ~ spl13_604
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5454,f5232,f4527,f5737])).

fof(f5454,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_604
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4528])).

fof(f5732,plain,
    ( ~ spl13_725
    | spl13_299
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5351,f5232,f2246,f5730])).

fof(f5730,plain,
    ( spl13_725
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_725])])).

fof(f2246,plain,
    ( spl13_299
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_299])])).

fof(f5351,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,o_0_0_xboole_0))
    | ~ spl13_299
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2247])).

fof(f2247,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_299 ),
    inference(avatar_component_clause,[],[f2246])).

fof(f5725,plain,
    ( ~ spl13_723
    | spl13_297
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5350,f5232,f2239,f5723])).

fof(f5723,plain,
    ( spl13_723
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_723])])).

fof(f2239,plain,
    ( spl13_297
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_297])])).

fof(f5350,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK2,o_0_0_xboole_0))
    | ~ spl13_297
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2240])).

fof(f2240,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_297 ),
    inference(avatar_component_clause,[],[f2239])).

fof(f5718,plain,
    ( ~ spl13_721
    | spl13_261
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5343,f5232,f2026,f5716])).

fof(f5716,plain,
    ( spl13_721
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_721])])).

fof(f5343,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,o_0_0_xboole_0)),sK3)
    | ~ spl13_261
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2027])).

fof(f5711,plain,
    ( ~ spl13_719
    | spl13_295
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5349,f5232,f2232,f5709])).

fof(f5709,plain,
    ( spl13_719
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_719])])).

fof(f2232,plain,
    ( spl13_295
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_295])])).

fof(f5349,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,o_0_0_xboole_0))
    | ~ spl13_295
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2233])).

fof(f2233,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_295 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f5699,plain,
    ( ~ spl13_717
    | spl13_601
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5453,f5232,f4507,f5697])).

fof(f5697,plain,
    ( spl13_717
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_717])])).

fof(f4507,plain,
    ( spl13_601
  <=> ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_601])])).

fof(f5453,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,o_0_0_xboole_0),sK4(sK1))
    | ~ spl13_601
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4508])).

fof(f4508,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1))
    | ~ spl13_601 ),
    inference(avatar_component_clause,[],[f4507])).

fof(f5602,plain,
    ( spl13_714
    | ~ spl13_606
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5455,f5232,f4534,f5600])).

fof(f5600,plain,
    ( spl13_714
  <=> r1_orders_2(sK1,o_0_0_xboole_0,sK7(sK0,sK1,sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_714])])).

fof(f4534,plain,
    ( spl13_606
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_606])])).

fof(f5455,plain,
    ( r1_orders_2(sK1,o_0_0_xboole_0,sK7(sK0,sK1,sK3,o_0_0_xboole_0))
    | ~ spl13_606
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4535])).

fof(f4535,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_606 ),
    inference(avatar_component_clause,[],[f4534])).

fof(f5595,plain,
    ( spl13_712
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5438,f5232,f4398,f5593])).

fof(f5438,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_584
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f4399])).

fof(f5588,plain,
    ( ~ spl13_711
    | spl13_285
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5346,f5232,f2175,f5586])).

fof(f2175,plain,
    ( spl13_285
  <=> ~ r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_285])])).

fof(f5346,plain,
    ( ~ r1_orders_2(sK1,o_0_0_xboole_0,sK8(sK0,sK1,sK2,o_0_0_xboole_0))
    | ~ spl13_285
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2176])).

fof(f2176,plain,
    ( ~ r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_285 ),
    inference(avatar_component_clause,[],[f2175])).

fof(f5581,plain,
    ( spl13_708
    | ~ spl13_268
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5344,f5232,f2063,f5579])).

fof(f5579,plain,
    ( spl13_708
  <=> r1_orders_2(sK1,o_0_0_xboole_0,sK8(sK0,sK1,sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_708])])).

fof(f2063,plain,
    ( spl13_268
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_268])])).

fof(f5344,plain,
    ( r1_orders_2(sK1,o_0_0_xboole_0,sK8(sK0,sK1,sK3,o_0_0_xboole_0))
    | ~ spl13_268
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f2064])).

fof(f2064,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_268 ),
    inference(avatar_component_clause,[],[f2063])).

fof(f5574,plain,
    ( spl13_706
    | ~ spl13_196
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5331,f5232,f1088,f5572])).

fof(f5572,plain,
    ( spl13_706
  <=> r1_orders_2(sK1,o_0_0_xboole_0,sK7(sK0,sK1,sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_706])])).

fof(f1088,plain,
    ( spl13_196
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_196])])).

fof(f5331,plain,
    ( r1_orders_2(sK1,o_0_0_xboole_0,sK7(sK0,sK1,sK2,o_0_0_xboole_0))
    | ~ spl13_196
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f1089])).

fof(f1089,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_196 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f5567,plain,
    ( spl13_704
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5326,f5232,f934,f5565])).

fof(f5326,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_170
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f935])).

fof(f5560,plain,
    ( ~ spl13_703
    | spl13_165
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5325,f5232,f887,f5558])).

fof(f887,plain,
    ( spl13_165
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_165])])).

fof(f5325,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_165
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f888])).

fof(f888,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_165 ),
    inference(avatar_component_clause,[],[f887])).

fof(f5553,plain,
    ( spl13_700
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5324,f5232,f883,f5551])).

fof(f5324,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_162
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f884])).

fof(f5518,plain,
    ( spl13_698
    | ~ spl13_694 ),
    inference(avatar_split_clause,[],[f5497,f5492,f5516])).

fof(f5497,plain,
    ( m1_subset_1(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_694 ),
    inference(unit_resulting_resolution,[],[f5493,f121])).

fof(f5511,plain,
    ( spl13_696
    | ~ spl13_150
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5323,f5232,f833,f5509])).

fof(f5509,plain,
    ( spl13_696
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_696])])).

fof(f833,plain,
    ( spl13_150
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK10(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f5323,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK0))
    | ~ spl13_150
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f834])).

fof(f834,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl13_150 ),
    inference(avatar_component_clause,[],[f833])).

fof(f5494,plain,
    ( spl13_694
    | ~ spl13_204
    | ~ spl13_680 ),
    inference(avatar_split_clause,[],[f5333,f5232,f1214,f5492])).

fof(f5333,plain,
    ( r2_hidden(o_0_0_xboole_0,u1_struct_0(sK1))
    | ~ spl13_204
    | ~ spl13_680 ),
    inference(backward_demodulation,[],[f5233,f1215])).

fof(f1215,plain,
    ( r2_hidden(sK10(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl13_204 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f5322,plain,
    ( spl13_692
    | ~ spl13_6
    | spl13_681 ),
    inference(avatar_split_clause,[],[f5252,f5229,f161,f5320])).

fof(f5320,plain,
    ( spl13_692
  <=> r2_hidden(sK10(sK10(u1_struct_0(sK1))),sK10(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_692])])).

fof(f5252,plain,
    ( r2_hidden(sK10(sK10(u1_struct_0(sK1))),sK10(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_681 ),
    inference(unit_resulting_resolution,[],[f162,f119,f5230,f431])).

fof(f5315,plain,
    ( ~ spl13_691
    | ~ spl13_6
    | spl13_681 ),
    inference(avatar_split_clause,[],[f5245,f5229,f161,f5313])).

fof(f5313,plain,
    ( spl13_691
  <=> ~ r2_hidden(sK10(u1_struct_0(sK1)),sK10(sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_691])])).

fof(f5245,plain,
    ( ~ r2_hidden(sK10(u1_struct_0(sK1)),sK10(sK10(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_681 ),
    inference(unit_resulting_resolution,[],[f119,f5230,f838])).

fof(f5294,plain,
    ( ~ spl13_689
    | ~ spl13_240
    | spl13_687 ),
    inference(avatar_split_clause,[],[f5278,f5275,f1735,f5292])).

fof(f5292,plain,
    ( spl13_689
  <=> ~ r1_tarski(sK10(u1_struct_0(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_689])])).

fof(f5278,plain,
    ( ~ r1_tarski(sK10(u1_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_687 ),
    inference(unit_resulting_resolution,[],[f5276,f1738])).

fof(f5277,plain,
    ( ~ spl13_687
    | ~ spl13_6
    | ~ spl13_240
    | spl13_681 ),
    inference(avatar_split_clause,[],[f5247,f5229,f1735,f161,f5275])).

fof(f5247,plain,
    ( ~ m1_subset_1(sK10(u1_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_681 ),
    inference(unit_resulting_resolution,[],[f119,f5230,f3204])).

fof(f5261,plain,
    ( ~ spl13_685
    | ~ spl13_6
    | spl13_681 ),
    inference(avatar_split_clause,[],[f5253,f5229,f161,f5259])).

fof(f5259,plain,
    ( spl13_685
  <=> ~ v1_xboole_0(sK10(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_685])])).

fof(f5253,plain,
    ( ~ v1_xboole_0(sK10(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_681 ),
    inference(unit_resulting_resolution,[],[f162,f5230,f127])).

fof(f5240,plain,
    ( spl13_680
    | ~ spl13_683
    | ~ spl13_6
    | spl13_203 ),
    inference(avatar_split_clause,[],[f1355,f1192,f161,f5238,f5232])).

fof(f1192,plain,
    ( spl13_203
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_203])])).

fof(f1355,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK10(u1_struct_0(sK1)))
    | o_0_0_xboole_0 = sK10(u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_203 ),
    inference(resolution,[],[f1193,f432])).

fof(f1193,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(u1_struct_0(sK1)))
    | ~ spl13_203 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f5095,plain,
    ( ~ spl13_679
    | ~ spl13_6
    | spl13_199
    | ~ spl13_642 ),
    inference(avatar_split_clause,[],[f4941,f4861,f1155,f161,f5093])).

fof(f5093,plain,
    ( spl13_679
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_679])])).

fof(f4941,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_642 ),
    inference(unit_resulting_resolution,[],[f1156,f4862,f838])).

fof(f5087,plain,
    ( spl13_676
    | ~ spl13_6
    | spl13_199
    | ~ spl13_642 ),
    inference(avatar_split_clause,[],[f4938,f4861,f1155,f161,f5085])).

fof(f4938,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_642 ),
    inference(unit_resulting_resolution,[],[f1156,f4862,f432])).

fof(f5080,plain,
    ( ~ spl13_675
    | ~ spl13_6
    | spl13_199
    | ~ spl13_640 ),
    inference(avatar_split_clause,[],[f4914,f4854,f1155,f161,f5078])).

fof(f5078,plain,
    ( spl13_675
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_675])])).

fof(f4854,plain,
    ( spl13_640
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_640])])).

fof(f4914,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_640 ),
    inference(unit_resulting_resolution,[],[f1156,f4855,f838])).

fof(f4855,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_640 ),
    inference(avatar_component_clause,[],[f4854])).

fof(f5073,plain,
    ( spl13_672
    | ~ spl13_6
    | spl13_199
    | ~ spl13_640 ),
    inference(avatar_split_clause,[],[f4911,f4854,f1155,f161,f5071])).

fof(f4911,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_640 ),
    inference(unit_resulting_resolution,[],[f1156,f4855,f432])).

fof(f5066,plain,
    ( ~ spl13_671
    | ~ spl13_6
    | spl13_199
    | ~ spl13_638 ),
    inference(avatar_split_clause,[],[f4887,f4847,f1155,f161,f5064])).

fof(f5064,plain,
    ( spl13_671
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_671])])).

fof(f4887,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_638 ),
    inference(unit_resulting_resolution,[],[f1156,f4848,f838])).

fof(f5059,plain,
    ( spl13_668
    | ~ spl13_6
    | spl13_199
    | ~ spl13_638 ),
    inference(avatar_split_clause,[],[f4884,f4847,f1155,f161,f5057])).

fof(f5057,plain,
    ( spl13_668
  <=> r2_hidden(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_668])])).

fof(f4884,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_638 ),
    inference(unit_resulting_resolution,[],[f1156,f4848,f432])).

fof(f5052,plain,
    ( spl13_666
    | ~ spl13_598 ),
    inference(avatar_split_clause,[],[f4570,f4500,f5050])).

fof(f4570,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_598 ),
    inference(unit_resulting_resolution,[],[f4501,f121])).

fof(f5045,plain,
    ( spl13_664
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f4277,f811,f359,f182,f154,f147,f140,f5043])).

fof(f4277,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_148 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f812,f360,f109])).

fof(f5038,plain,
    ( ~ spl13_663
    | ~ spl13_6
    | spl13_199
    | ~ spl13_342 ),
    inference(avatar_split_clause,[],[f2718,f2510,f1155,f161,f5036])).

fof(f5036,plain,
    ( spl13_663
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_663])])).

fof(f2510,plain,
    ( spl13_342
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_342])])).

fof(f2718,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_342 ),
    inference(unit_resulting_resolution,[],[f1156,f2511,f838])).

fof(f2511,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_342 ),
    inference(avatar_component_clause,[],[f2510])).

fof(f5031,plain,
    ( spl13_660
    | ~ spl13_6
    | spl13_199
    | ~ spl13_342 ),
    inference(avatar_split_clause,[],[f2716,f2510,f1155,f161,f5029])).

fof(f5029,plain,
    ( spl13_660
  <=> r2_hidden(sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_660])])).

fof(f2716,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_342 ),
    inference(unit_resulting_resolution,[],[f1156,f2511,f432])).

fof(f5024,plain,
    ( spl13_658
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f1408,f811,f294,f182,f154,f147,f140,f5022])).

fof(f1408,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_148 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f812,f109])).

fof(f5017,plain,
    ( spl13_256
    | ~ spl13_279
    | ~ spl13_6
    | spl13_179 ),
    inference(avatar_split_clause,[],[f989,f985,f161,f2142,f1999])).

fof(f1999,plain,
    ( spl13_256
  <=> o_0_0_xboole_0 = sK4(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_256])])).

fof(f2142,plain,
    ( spl13_279
  <=> ~ m1_subset_1(sK9(sK0,sK1,sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_279])])).

fof(f985,plain,
    ( spl13_179
  <=> ~ r2_hidden(sK9(sK0,sK1,sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_179])])).

fof(f989,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK3),sK4(sK1))
    | o_0_0_xboole_0 = sK4(sK1)
    | ~ spl13_6
    | ~ spl13_179 ),
    inference(resolution,[],[f986,f432])).

fof(f986,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_179 ),
    inference(avatar_component_clause,[],[f985])).

fof(f5016,plain,
    ( ~ spl13_657
    | ~ spl13_598 ),
    inference(avatar_split_clause,[],[f4569,f4500,f5014])).

fof(f4569,plain,
    ( ~ r2_hidden(sK3,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))))
    | ~ spl13_598 ),
    inference(unit_resulting_resolution,[],[f4501,f120])).

fof(f5009,plain,
    ( spl13_256
    | ~ spl13_277
    | ~ spl13_6
    | spl13_177 ),
    inference(avatar_split_clause,[],[f988,f978,f161,f2135,f1999])).

fof(f2135,plain,
    ( spl13_277
  <=> ~ m1_subset_1(sK9(sK0,sK1,sK2),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_277])])).

fof(f978,plain,
    ( spl13_177
  <=> ~ r2_hidden(sK9(sK0,sK1,sK2),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_177])])).

fof(f988,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2),sK4(sK1))
    | o_0_0_xboole_0 = sK4(sK1)
    | ~ spl13_6
    | ~ spl13_177 ),
    inference(resolution,[],[f979,f432])).

fof(f979,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),sK4(sK1))
    | ~ spl13_177 ),
    inference(avatar_component_clause,[],[f978])).

fof(f5008,plain,
    ( spl13_654
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f957,f811,f339,f182,f154,f147,f140,f5006])).

fof(f957,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_148 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f812,f340,f116])).

fof(f4984,plain,
    ( ~ spl13_653
    | spl13_165 ),
    inference(avatar_split_clause,[],[f4367,f887,f4982])).

fof(f4367,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_165 ),
    inference(unit_resulting_resolution,[],[f119,f888,f130])).

fof(f4972,plain,
    ( ~ spl13_651
    | spl13_353 ),
    inference(avatar_split_clause,[],[f4812,f2614,f4970])).

fof(f2614,plain,
    ( spl13_353
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_353])])).

fof(f4812,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_353 ),
    inference(unit_resulting_resolution,[],[f2615,f121])).

fof(f2615,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_353 ),
    inference(avatar_component_clause,[],[f2614])).

fof(f4965,plain,
    ( ~ spl13_649
    | ~ spl13_72
    | spl13_353 ),
    inference(avatar_split_clause,[],[f4810,f2614,f437,f4963])).

fof(f4810,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_353 ),
    inference(unit_resulting_resolution,[],[f438,f2615,f130])).

fof(f4958,plain,
    ( ~ spl13_647
    | spl13_349 ),
    inference(avatar_split_clause,[],[f4768,f2571,f4956])).

fof(f2571,plain,
    ( spl13_349
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_349])])).

fof(f4768,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_349 ),
    inference(unit_resulting_resolution,[],[f2572,f121])).

fof(f2572,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_349 ),
    inference(avatar_component_clause,[],[f2571])).

fof(f4951,plain,
    ( ~ spl13_645
    | ~ spl13_72
    | spl13_349 ),
    inference(avatar_split_clause,[],[f4766,f2571,f437,f4949])).

fof(f4766,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_349 ),
    inference(unit_resulting_resolution,[],[f438,f2572,f130])).

fof(f4863,plain,
    ( spl13_642
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4326,f903,f339,f182,f154,f147,f140,f4861])).

fof(f4326,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f904,f116])).

fof(f4856,plain,
    ( spl13_640
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4320,f903,f359,f182,f154,f147,f140,f4854])).

fof(f4320,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f360,f904,f109])).

fof(f4849,plain,
    ( spl13_638
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4319,f903,f294,f182,f154,f147,f140,f4847])).

fof(f4319,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f904,f109])).

fof(f4799,plain,
    ( ~ spl13_637
    | ~ spl13_6
    | spl13_199
    | ~ spl13_620 ),
    inference(avatar_split_clause,[],[f4747,f4621,f1155,f161,f4797])).

fof(f4797,plain,
    ( spl13_637
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_637])])).

fof(f4621,plain,
    ( spl13_620
  <=> m1_subset_1(sK7(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_620])])).

fof(f4747,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK10(sK4(sK1))))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_620 ),
    inference(unit_resulting_resolution,[],[f1156,f4622,f838])).

fof(f4622,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_620 ),
    inference(avatar_component_clause,[],[f4621])).

fof(f4792,plain,
    ( spl13_634
    | ~ spl13_6
    | spl13_199
    | ~ spl13_620 ),
    inference(avatar_split_clause,[],[f4744,f4621,f1155,f161,f4790])).

fof(f4790,plain,
    ( spl13_634
  <=> r2_hidden(sK7(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_634])])).

fof(f4744,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_620 ),
    inference(unit_resulting_resolution,[],[f1156,f4622,f432])).

fof(f4785,plain,
    ( ~ spl13_633
    | ~ spl13_6
    | spl13_199
    | ~ spl13_616 ),
    inference(avatar_split_clause,[],[f4720,f4601,f1155,f161,f4783])).

fof(f4783,plain,
    ( spl13_633
  <=> ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_633])])).

fof(f4601,plain,
    ( spl13_616
  <=> m1_subset_1(sK8(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_616])])).

fof(f4720,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK10(sK4(sK1))))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_616 ),
    inference(unit_resulting_resolution,[],[f1156,f4602,f838])).

fof(f4602,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_616 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f4778,plain,
    ( spl13_630
    | ~ spl13_6
    | spl13_199
    | ~ spl13_616 ),
    inference(avatar_split_clause,[],[f4717,f4601,f1155,f161,f4776])).

fof(f4776,plain,
    ( spl13_630
  <=> r2_hidden(sK8(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_630])])).

fof(f4717,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_616 ),
    inference(unit_resulting_resolution,[],[f1156,f4602,f432])).

fof(f4764,plain,
    ( ~ spl13_629
    | ~ spl13_6
    | spl13_199
    | ~ spl13_614 ),
    inference(avatar_split_clause,[],[f4687,f4594,f1155,f161,f4762])).

fof(f4762,plain,
    ( spl13_629
  <=> ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK10(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_629])])).

fof(f4594,plain,
    ( spl13_614
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_614])])).

fof(f4687,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK10(sK4(sK1))))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_614 ),
    inference(unit_resulting_resolution,[],[f1156,f4595,f838])).

fof(f4595,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_614 ),
    inference(avatar_component_clause,[],[f4594])).

fof(f4757,plain,
    ( spl13_626
    | ~ spl13_6
    | spl13_199
    | ~ spl13_614 ),
    inference(avatar_split_clause,[],[f4684,f4594,f1155,f161,f4755])).

fof(f4755,plain,
    ( spl13_626
  <=> r2_hidden(sK7(sK0,sK1,sK2,sK10(sK4(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_626])])).

fof(f4684,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_614 ),
    inference(unit_resulting_resolution,[],[f1156,f4595,f432])).

fof(f4662,plain,
    ( spl13_624
    | ~ spl13_622 ),
    inference(avatar_split_clause,[],[f4655,f4651,f4660])).

fof(f4660,plain,
    ( spl13_624
  <=> l1_struct_0(sK5(sK5(sK5(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_624])])).

fof(f4651,plain,
    ( spl13_622
  <=> l1_orders_2(sK5(sK5(sK5(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_622])])).

fof(f4655,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK5(sK1)))))
    | ~ spl13_622 ),
    inference(unit_resulting_resolution,[],[f4652,f102])).

fof(f102,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_l1_orders_2)).

fof(f4652,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK1)))))
    | ~ spl13_622 ),
    inference(avatar_component_clause,[],[f4651])).

fof(f4653,plain,
    ( spl13_622
    | ~ spl13_144
    | ~ spl13_612 ),
    inference(avatar_split_clause,[],[f4627,f4587,f786,f4651])).

fof(f786,plain,
    ( spl13_144
  <=> l1_struct_0(sK5(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f4587,plain,
    ( spl13_612
  <=> l1_waybel_0(sK5(sK5(sK5(sK5(sK1)))),sK5(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_612])])).

fof(f4627,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK1)))))
    | ~ spl13_144
    | ~ spl13_612 ),
    inference(unit_resulting_resolution,[],[f787,f4588,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_l1_waybel_0)).

fof(f4588,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK1)))),sK5(sK5(sK5(sK1))))
    | ~ spl13_612 ),
    inference(avatar_component_clause,[],[f4587])).

fof(f787,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK1))))
    | ~ spl13_144 ),
    inference(avatar_component_clause,[],[f786])).

fof(f4623,plain,
    ( spl13_620
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f4284,f2083,f359,f182,f154,f147,f140,f4621])).

fof(f2083,plain,
    ( spl13_270
  <=> m1_subset_1(sK10(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_270])])).

fof(f4284,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f2084,f360,f109])).

fof(f2084,plain,
    ( m1_subset_1(sK10(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_270 ),
    inference(avatar_component_clause,[],[f2083])).

fof(f4610,plain,
    ( spl13_618
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | spl13_201
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2105,f2083,f1183,f876,f633,f460,f4608])).

fof(f4608,plain,
    ( spl13_618
  <=> m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK10(sK4(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_618])])).

fof(f2105,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK10(sK4(sK1))),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201
    | ~ spl13_270 ),
    inference(backward_demodulation,[],[f2102,f2103])).

fof(f2103,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK10(sK4(sK1))),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f1184,f461,f634,f877,f2084,f132])).

fof(f2102,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK10(sK4(sK1))) = k1_funct_1(u1_waybel_0(sK0,sK1),sK10(sK4(sK1)))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f1184,f461,f634,f877,f2084,f133])).

fof(f4603,plain,
    ( spl13_616
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2092,f2083,f339,f182,f154,f147,f140,f4601])).

fof(f2092,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f2084,f116])).

fof(f4596,plain,
    ( spl13_614
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2088,f2083,f294,f182,f154,f147,f140,f4594])).

fof(f2088,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK10(sK4(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f2084,f109])).

fof(f4589,plain,
    ( spl13_612
    | ~ spl13_144 ),
    inference(avatar_split_clause,[],[f806,f786,f4587])).

fof(f806,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK1)))),sK5(sK5(sK5(sK1))))
    | ~ spl13_144 ),
    inference(unit_resulting_resolution,[],[f787,f107])).

fof(f107,plain,(
    ! [X0] :
      ( l1_waybel_0(sK5(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_waybel_0(sK5(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',existence_l1_waybel_0)).

fof(f4567,plain,
    ( ~ spl13_611
    | ~ spl13_6
    | spl13_257
    | spl13_601 ),
    inference(avatar_split_clause,[],[f4520,f4507,f1996,f161,f4565])).

fof(f4520,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_601 ),
    inference(unit_resulting_resolution,[],[f1997,f4508,f432])).

fof(f4543,plain,
    ( ~ spl13_609
    | ~ spl13_6
    | spl13_199
    | ~ spl13_584 ),
    inference(avatar_split_clause,[],[f4449,f4398,f1155,f161,f4541])).

fof(f4449,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f1156,f4399,f838])).

fof(f4536,plain,
    ( spl13_606
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f4276,f359,f182,f154,f147,f140,f4534])).

fof(f4276,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f360,f110])).

fof(f4529,plain,
    ( spl13_604
    | ~ spl13_6
    | spl13_199
    | ~ spl13_584 ),
    inference(avatar_split_clause,[],[f4446,f4398,f1155,f161,f4527])).

fof(f4446,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_584 ),
    inference(unit_resulting_resolution,[],[f1156,f4399,f432])).

fof(f4516,plain,
    ( ~ spl13_603
    | spl13_187 ),
    inference(avatar_split_clause,[],[f4485,f1047,f4514])).

fof(f1047,plain,
    ( spl13_187
  <=> ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_187])])).

fof(f4485,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl13_187 ),
    inference(unit_resulting_resolution,[],[f1048,f121])).

fof(f1048,plain,
    ( ~ m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl13_187 ),
    inference(avatar_component_clause,[],[f1047])).

fof(f4509,plain,
    ( ~ spl13_601
    | ~ spl13_72
    | spl13_165 ),
    inference(avatar_split_clause,[],[f4366,f887,f437,f4507])).

fof(f4366,plain,
    ( ~ r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_165 ),
    inference(unit_resulting_resolution,[],[f438,f888,f130])).

fof(f4502,plain,
    ( spl13_598
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f4267,f359,f182,f154,f147,f140,f4500])).

fof(f4267,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f360,f111])).

fof(f4495,plain,
    ( spl13_596
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_166 ),
    inference(avatar_split_clause,[],[f4329,f903,f182,f154,f147,f140,f4493])).

fof(f4493,plain,
    ( spl13_596
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_596])])).

fof(f4329,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_166 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f904,f129])).

fof(f4481,plain,
    ( ~ spl13_595
    | spl13_589 ),
    inference(avatar_split_clause,[],[f4453,f4424,f4479])).

fof(f4479,plain,
    ( spl13_595
  <=> ~ r2_hidden(sK6(sK0,sK1,sK3),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_595])])).

fof(f4424,plain,
    ( spl13_589
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_589])])).

fof(f4453,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_589 ),
    inference(unit_resulting_resolution,[],[f119,f4425,f130])).

fof(f4425,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_589 ),
    inference(avatar_component_clause,[],[f4424])).

fof(f4471,plain,
    ( ~ spl13_593
    | spl13_103 ),
    inference(avatar_split_clause,[],[f4309,f593,f4469])).

fof(f4469,plain,
    ( spl13_593
  <=> ~ r2_hidden(sK6(sK0,sK1,sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_593])])).

fof(f593,plain,
    ( spl13_103
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_103])])).

fof(f4309,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f119,f594,f130])).

fof(f594,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_103 ),
    inference(avatar_component_clause,[],[f593])).

fof(f4463,plain,
    ( ~ spl13_591
    | spl13_577 ),
    inference(avatar_split_clause,[],[f4360,f4356,f4461])).

fof(f4461,plain,
    ( spl13_591
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_591])])).

fof(f4356,plain,
    ( spl13_577
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_577])])).

fof(f4360,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))))
    | ~ spl13_577 ),
    inference(unit_resulting_resolution,[],[f119,f4357,f130])).

fof(f4357,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_577 ),
    inference(avatar_component_clause,[],[f4356])).

fof(f4426,plain,
    ( ~ spl13_589
    | ~ spl13_6
    | spl13_257
    | spl13_583 ),
    inference(avatar_split_clause,[],[f4404,f4391,f1996,f161,f4424])).

fof(f4391,plain,
    ( spl13_583
  <=> ~ r2_hidden(sK6(sK0,sK1,sK3),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_583])])).

fof(f4404,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_583 ),
    inference(unit_resulting_resolution,[],[f1997,f4392,f432])).

fof(f4392,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_583 ),
    inference(avatar_component_clause,[],[f4391])).

fof(f4412,plain,
    ( ~ spl13_587
    | ~ spl13_6
    | ~ spl13_166
    | spl13_199 ),
    inference(avatar_split_clause,[],[f4337,f1155,f903,f161,f4410])).

fof(f4410,plain,
    ( spl13_587
  <=> ~ r2_hidden(u1_struct_0(sK1),sK9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_587])])).

fof(f4337,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK9(sK0,sK1,sK2))
    | ~ spl13_6
    | ~ spl13_166
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f1156,f904,f838])).

fof(f4400,plain,
    ( spl13_584
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f4285,f359,f182,f154,f147,f140,f4398])).

fof(f4285,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f360,f109])).

fof(f4393,plain,
    ( ~ spl13_583
    | ~ spl13_72
    | spl13_103 ),
    inference(avatar_split_clause,[],[f4308,f593,f437,f4391])).

fof(f4308,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f438,f594,f130])).

fof(f4385,plain,
    ( ~ spl13_581
    | spl13_577 ),
    inference(avatar_split_clause,[],[f4361,f4356,f4383])).

fof(f4383,plain,
    ( spl13_581
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_581])])).

fof(f4361,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_577 ),
    inference(unit_resulting_resolution,[],[f4357,f121])).

fof(f4378,plain,
    ( ~ spl13_579
    | spl13_577 ),
    inference(avatar_split_clause,[],[f4359,f4356,f4376])).

fof(f4376,plain,
    ( spl13_579
  <=> ~ r1_tarski(u1_struct_0(sK1),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_579])])).

fof(f4359,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK4(sK1))
    | ~ spl13_577 ),
    inference(unit_resulting_resolution,[],[f4357,f126])).

fof(f4358,plain,
    ( ~ spl13_577
    | ~ spl13_168
    | spl13_277 ),
    inference(avatar_split_clause,[],[f4345,f2135,f923,f4356])).

fof(f923,plain,
    ( spl13_168
  <=> r2_hidden(sK9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_168])])).

fof(f4345,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_168
    | ~ spl13_277 ),
    inference(unit_resulting_resolution,[],[f2136,f924,f130])).

fof(f924,plain,
    ( r2_hidden(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_168 ),
    inference(avatar_component_clause,[],[f923])).

fof(f2136,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2),sK4(sK1))
    | ~ spl13_277 ),
    inference(avatar_component_clause,[],[f2135])).

fof(f4306,plain,
    ( spl13_574
    | ~ spl13_572 ),
    inference(avatar_split_clause,[],[f4299,f4295,f4304])).

fof(f4304,plain,
    ( spl13_574
  <=> l1_struct_0(sK5(sK5(sK5(sK5(sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_574])])).

fof(f4295,plain,
    ( spl13_572
  <=> l1_orders_2(sK5(sK5(sK5(sK5(sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_572])])).

fof(f4299,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK5(sK11)))))
    | ~ spl13_572 ),
    inference(unit_resulting_resolution,[],[f4296,f102])).

fof(f4296,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK11)))))
    | ~ spl13_572 ),
    inference(avatar_component_clause,[],[f4295])).

fof(f4297,plain,
    ( spl13_572
    | ~ spl13_138
    | ~ spl13_570 ),
    inference(avatar_split_clause,[],[f4246,f4243,f756,f4295])).

fof(f756,plain,
    ( spl13_138
  <=> l1_struct_0(sK5(sK5(sK5(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f4243,plain,
    ( spl13_570
  <=> l1_waybel_0(sK5(sK5(sK5(sK5(sK11)))),sK5(sK5(sK5(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_570])])).

fof(f4246,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK11)))))
    | ~ spl13_138
    | ~ spl13_570 ),
    inference(unit_resulting_resolution,[],[f757,f4244,f106])).

fof(f4244,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK11)))),sK5(sK5(sK5(sK11))))
    | ~ spl13_570 ),
    inference(avatar_component_clause,[],[f4243])).

fof(f757,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK11))))
    | ~ spl13_138 ),
    inference(avatar_component_clause,[],[f756])).

fof(f4252,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_57
    | spl13_323
    | ~ spl13_348
    | ~ spl13_412
    | ~ spl13_446
    | ~ spl13_512 ),
    inference(avatar_contradiction_clause,[],[f4251])).

fof(f4251,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_57
    | ~ spl13_323
    | ~ spl13_348
    | ~ spl13_412
    | ~ spl13_446
    | ~ spl13_512 ),
    inference(subsumption_resolution,[],[f4250,f3631])).

fof(f3631,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK3)
    | ~ spl13_323
    | ~ spl13_412
    | ~ spl13_446 ),
    inference(unit_resulting_resolution,[],[f3090,f3429,f3347])).

fof(f4250,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_57
    | ~ spl13_348
    | ~ spl13_512 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f363,f2575,f3832,f113])).

fof(f4245,plain,
    ( spl13_570
    | ~ spl13_138 ),
    inference(avatar_split_clause,[],[f759,f756,f4243])).

fof(f759,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK11)))),sK5(sK5(sK5(sK11))))
    | ~ spl13_138 ),
    inference(unit_resulting_resolution,[],[f757,f107])).

fof(f4237,plain,
    ( spl13_568
    | ~ spl13_566 ),
    inference(avatar_split_clause,[],[f4230,f4200,f4235])).

fof(f4235,plain,
    ( spl13_568
  <=> l1_struct_0(sK5(sK5(sK5(sK5(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_568])])).

fof(f4200,plain,
    ( spl13_566
  <=> l1_orders_2(sK5(sK5(sK5(sK5(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_566])])).

fof(f4230,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK5(sK12)))))
    | ~ spl13_566 ),
    inference(unit_resulting_resolution,[],[f4201,f102])).

fof(f4201,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK12)))))
    | ~ spl13_566 ),
    inference(avatar_component_clause,[],[f4200])).

fof(f4202,plain,
    ( spl13_566
    | ~ spl13_132
    | ~ spl13_564 ),
    inference(avatar_split_clause,[],[f4192,f4189,f724,f4200])).

fof(f4192,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK12)))))
    | ~ spl13_132
    | ~ spl13_564 ),
    inference(unit_resulting_resolution,[],[f725,f4190,f106])).

fof(f4191,plain,
    ( spl13_564
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f727,f724,f4189])).

fof(f727,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK12)))),sK5(sK5(sK5(sK12))))
    | ~ spl13_132 ),
    inference(unit_resulting_resolution,[],[f725,f107])).

fof(f4183,plain,
    ( spl13_562
    | ~ spl13_560 ),
    inference(avatar_split_clause,[],[f4150,f4146,f4181])).

fof(f4181,plain,
    ( spl13_562
  <=> l1_struct_0(sK5(sK5(sK5(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_562])])).

fof(f4146,plain,
    ( spl13_560
  <=> l1_orders_2(sK5(sK5(sK5(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_560])])).

fof(f4150,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK5(sK0)))))
    | ~ spl13_560 ),
    inference(unit_resulting_resolution,[],[f4147,f102])).

fof(f4147,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK0)))))
    | ~ spl13_560 ),
    inference(avatar_component_clause,[],[f4146])).

fof(f4148,plain,
    ( spl13_560
    | ~ spl13_126
    | ~ spl13_558 ),
    inference(avatar_split_clause,[],[f4138,f4135,f692,f4146])).

fof(f4138,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK5(sK0)))))
    | ~ spl13_126
    | ~ spl13_558 ),
    inference(unit_resulting_resolution,[],[f693,f4136,f106])).

fof(f4137,plain,
    ( spl13_558
    | ~ spl13_126 ),
    inference(avatar_split_clause,[],[f695,f692,f4135])).

fof(f695,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK5(sK0)))),sK5(sK5(sK5(sK0))))
    | ~ spl13_126 ),
    inference(unit_resulting_resolution,[],[f693,f107])).

fof(f4093,plain,
    ( ~ spl13_557
    | spl13_551 ),
    inference(avatar_split_clause,[],[f4066,f4063,f4091])).

fof(f4066,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_551 ),
    inference(unit_resulting_resolution,[],[f119,f4064,f130])).

fof(f4083,plain,
    ( ~ spl13_555
    | spl13_537 ),
    inference(avatar_split_clause,[],[f3996,f3980,f4081])).

fof(f4081,plain,
    ( spl13_555
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_555])])).

fof(f3980,plain,
    ( spl13_537
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_537])])).

fof(f3996,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl13_537 ),
    inference(unit_resulting_resolution,[],[f119,f3981,f130])).

fof(f3981,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK2))
    | ~ spl13_537 ),
    inference(avatar_component_clause,[],[f3980])).

fof(f4076,plain,
    ( ~ spl13_553
    | spl13_535 ),
    inference(avatar_split_clause,[],[f3991,f3974,f4074])).

fof(f3974,plain,
    ( spl13_535
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_535])])).

fof(f3991,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_535 ),
    inference(unit_resulting_resolution,[],[f119,f3975,f130])).

fof(f3975,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),u1_struct_0(sK1))
    | ~ spl13_535 ),
    inference(avatar_component_clause,[],[f3974])).

fof(f4065,plain,
    ( ~ spl13_551
    | ~ spl13_6
    | spl13_257
    | spl13_543 ),
    inference(avatar_split_clause,[],[f4039,f4012,f1996,f161,f4063])).

fof(f4039,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_543 ),
    inference(unit_resulting_resolution,[],[f1997,f4013,f432])).

fof(f4035,plain,
    ( ~ spl13_549
    | spl13_537 ),
    inference(avatar_split_clause,[],[f3997,f3980,f4033])).

fof(f4033,plain,
    ( spl13_549
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_549])])).

fof(f3997,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK2))
    | ~ spl13_537 ),
    inference(unit_resulting_resolution,[],[f3981,f121])).

fof(f4028,plain,
    ( ~ spl13_547
    | spl13_535 ),
    inference(avatar_split_clause,[],[f3992,f3974,f4026])).

fof(f4026,plain,
    ( spl13_547
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_547])])).

fof(f3992,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),u1_struct_0(sK1))
    | ~ spl13_535 ),
    inference(unit_resulting_resolution,[],[f3975,f121])).

fof(f4021,plain,
    ( spl13_544
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_170 ),
    inference(avatar_split_clause,[],[f1970,f934,f285,f182,f154,f147,f140,f4019])).

fof(f1970,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f935,f116])).

fof(f4014,plain,
    ( ~ spl13_543
    | ~ spl13_72
    | spl13_535 ),
    inference(avatar_split_clause,[],[f3990,f3974,f437,f4012])).

fof(f3990,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_535 ),
    inference(unit_resulting_resolution,[],[f438,f3975,f130])).

fof(f4007,plain,
    ( ~ spl13_541
    | spl13_537 ),
    inference(avatar_split_clause,[],[f3995,f3980,f4005])).

fof(f4005,plain,
    ( spl13_541
  <=> ~ r1_tarski(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_541])])).

fof(f3995,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK2)
    | ~ spl13_537 ),
    inference(unit_resulting_resolution,[],[f3981,f126])).

fof(f3989,plain,
    ( spl13_538
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_170 ),
    inference(avatar_split_clause,[],[f1965,f934,f294,f182,f154,f147,f140,f3987])).

fof(f1965,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f935,f109])).

fof(f3982,plain,
    ( ~ spl13_535
    | ~ spl13_537
    | spl13_201
    | spl13_417 ),
    inference(avatar_split_clause,[],[f3271,f3126,f1183,f3980,f3974])).

fof(f3126,plain,
    ( spl13_417
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_417])])).

fof(f3271,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k1_zfmisc_1(sK3),u1_struct_0(sK1))
    | ~ spl13_201
    | ~ spl13_417 ),
    inference(resolution,[],[f3138,f1598])).

fof(f3138,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_zfmisc_1(sK3),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) )
    | ~ spl13_417 ),
    inference(resolution,[],[f3127,f130])).

fof(f3127,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK2)
    | ~ spl13_417 ),
    inference(avatar_component_clause,[],[f3126])).

fof(f3969,plain,
    ( ~ spl13_493
    | ~ spl13_455
    | spl13_201
    | spl13_361 ),
    inference(avatar_split_clause,[],[f3018,f2670,f1183,f3501,f3735])).

fof(f3735,plain,
    ( spl13_493
  <=> ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_493])])).

fof(f3501,plain,
    ( spl13_455
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_455])])).

fof(f2670,plain,
    ( spl13_361
  <=> ~ m1_subset_1(sK3,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_361])])).

fof(f3018,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_201
    | ~ spl13_361 ),
    inference(resolution,[],[f2675,f1598])).

fof(f2675,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(sK2))) )
    | ~ spl13_361 ),
    inference(resolution,[],[f2671,f130])).

fof(f2671,plain,
    ( ~ m1_subset_1(sK3,sK10(sK2))
    | ~ spl13_361 ),
    inference(avatar_component_clause,[],[f2670])).

fof(f3964,plain,
    ( spl13_532
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_164 ),
    inference(avatar_split_clause,[],[f1934,f890,f285,f182,f154,f147,f140,f3962])).

fof(f3962,plain,
    ( spl13_532
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_532])])).

fof(f890,plain,
    ( spl13_164
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_164])])).

fof(f1934,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_164 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f891,f116])).

fof(f891,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_164 ),
    inference(avatar_component_clause,[],[f890])).

fof(f3944,plain,
    ( spl13_530
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f581,f578,f3942])).

fof(f3942,plain,
    ( spl13_530
  <=> m1_subset_1(sK4(sK5(sK5(sK1))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_530])])).

fof(f578,plain,
    ( spl13_98
  <=> l1_orders_2(sK5(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f581,plain,
    ( m1_subset_1(sK4(sK5(sK5(sK1))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK1)))))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f579,f103])).

fof(f103,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
     => m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(pure_predicate_removal,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] :
          ( v1_waybel_0(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] :
          ( v2_waybel_0(X1,X0)
          & v1_waybel_0(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',rc1_waybel_0)).

fof(f579,plain,
    ( l1_orders_2(sK5(sK5(sK1)))
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f578])).

fof(f3937,plain,
    ( spl13_528
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_164 ),
    inference(avatar_split_clause,[],[f1929,f890,f294,f182,f154,f147,f140,f3935])).

fof(f3935,plain,
    ( spl13_528
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_528])])).

fof(f1929,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_164 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f891,f109])).

fof(f3930,plain,
    ( spl13_526
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f470,f467,f3928])).

fof(f3928,plain,
    ( spl13_526
  <=> m1_subset_1(sK4(sK5(sK5(sK11))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_526])])).

fof(f467,plain,
    ( spl13_78
  <=> l1_orders_2(sK5(sK5(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f470,plain,
    ( m1_subset_1(sK4(sK5(sK5(sK11))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK11)))))
    | ~ spl13_78 ),
    inference(unit_resulting_resolution,[],[f468,f103])).

fof(f468,plain,
    ( l1_orders_2(sK5(sK5(sK11)))
    | ~ spl13_78 ),
    inference(avatar_component_clause,[],[f467])).

fof(f3914,plain,
    ( spl13_524
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_162 ),
    inference(avatar_split_clause,[],[f1881,f883,f285,f182,f154,f147,f140,f3912])).

fof(f3912,plain,
    ( spl13_524
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_524])])).

fof(f1881,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f884,f116])).

fof(f3884,plain,
    ( spl13_522
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_162 ),
    inference(avatar_split_clause,[],[f1876,f883,f294,f182,f154,f147,f140,f3882])).

fof(f1876,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f884,f109])).

fof(f3877,plain,
    ( spl13_520
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f413,f410,f3875])).

fof(f3875,plain,
    ( spl13_520
  <=> m1_subset_1(sK4(sK5(sK5(sK12))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_520])])).

fof(f410,plain,
    ( spl13_66
  <=> l1_orders_2(sK5(sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f413,plain,
    ( m1_subset_1(sK4(sK5(sK5(sK12))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK12)))))
    | ~ spl13_66 ),
    inference(unit_resulting_resolution,[],[f411,f103])).

fof(f411,plain,
    ( l1_orders_2(sK5(sK5(sK12)))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f410])).

fof(f3860,plain,
    ( spl13_518
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1202,f596,f285,f182,f154,f147,f140,f3858])).

fof(f3858,plain,
    ( spl13_518
  <=> r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_518])])).

fof(f596,plain,
    ( spl13_102
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f1202,plain,
    ( r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f597,f117])).

fof(f597,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_102 ),
    inference(avatar_component_clause,[],[f596])).

fof(f3853,plain,
    ( ~ spl13_517
    | spl13_495 ),
    inference(avatar_split_clause,[],[f3793,f3741,f3851])).

fof(f3851,plain,
    ( spl13_517
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_517])])).

fof(f3741,plain,
    ( spl13_495
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_495])])).

fof(f3793,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK3)))))
    | ~ spl13_495 ),
    inference(unit_resulting_resolution,[],[f119,f3742,f130])).

fof(f3742,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK3)))
    | ~ spl13_495 ),
    inference(avatar_component_clause,[],[f3741])).

fof(f3841,plain,
    ( ~ spl13_515
    | spl13_503 ),
    inference(avatar_split_clause,[],[f3788,f3785,f3839])).

fof(f3839,plain,
    ( spl13_515
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_515])])).

fof(f3785,plain,
    ( spl13_503
  <=> ~ m1_subset_1(sK3,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_503])])).

fof(f3788,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_503 ),
    inference(unit_resulting_resolution,[],[f119,f3786,f130])).

fof(f3786,plain,
    ( ~ m1_subset_1(sK3,sK4(sK1))
    | ~ spl13_503 ),
    inference(avatar_component_clause,[],[f3785])).

fof(f3833,plain,
    ( spl13_512
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1196,f596,f294,f182,f154,f147,f140,f3831])).

fof(f1196,plain,
    ( r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f597,f110])).

fof(f3825,plain,
    ( ~ spl13_511
    | spl13_495 ),
    inference(avatar_split_clause,[],[f3794,f3741,f3823])).

fof(f3823,plain,
    ( spl13_511
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_511])])).

fof(f3794,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK3)))
    | ~ spl13_495 ),
    inference(unit_resulting_resolution,[],[f3742,f121])).

fof(f3818,plain,
    ( ~ spl13_509
    | spl13_493 ),
    inference(avatar_split_clause,[],[f3745,f3735,f3816])).

fof(f3816,plain,
    ( spl13_509
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_509])])).

fof(f3745,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_493 ),
    inference(unit_resulting_resolution,[],[f119,f3736,f130])).

fof(f3736,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_493 ),
    inference(avatar_component_clause,[],[f3735])).

fof(f3811,plain,
    ( ~ spl13_507
    | spl13_495 ),
    inference(avatar_split_clause,[],[f3792,f3741,f3809])).

fof(f3809,plain,
    ( spl13_507
  <=> ~ r1_tarski(u1_struct_0(sK1),sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_507])])).

fof(f3792,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK10(sK3))
    | ~ spl13_495 ),
    inference(unit_resulting_resolution,[],[f3742,f126])).

fof(f3804,plain,
    ( spl13_504
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_170 ),
    inference(avatar_split_clause,[],[f1033,f934,f339,f182,f154,f147,f140,f3802])).

fof(f1033,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f935,f116])).

fof(f3787,plain,
    ( ~ spl13_503
    | ~ spl13_6
    | spl13_257
    | spl13_497 ),
    inference(avatar_split_clause,[],[f3773,f3753,f1996,f161,f3785])).

fof(f3753,plain,
    ( spl13_497
  <=> ~ r2_hidden(sK3,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_497])])).

fof(f3773,plain,
    ( ~ m1_subset_1(sK3,sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_497 ),
    inference(unit_resulting_resolution,[],[f1997,f3754,f432])).

fof(f3754,plain,
    ( ~ r2_hidden(sK3,sK4(sK1))
    | ~ spl13_497 ),
    inference(avatar_component_clause,[],[f3753])).

fof(f3769,plain,
    ( spl13_500
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_164 ),
    inference(avatar_split_clause,[],[f1022,f890,f339,f182,f154,f147,f140,f3767])).

fof(f1022,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_164 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f891,f116])).

fof(f3762,plain,
    ( ~ spl13_499
    | spl13_493 ),
    inference(avatar_split_clause,[],[f3746,f3735,f3760])).

fof(f3760,plain,
    ( spl13_499
  <=> ~ r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_499])])).

fof(f3746,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl13_493 ),
    inference(unit_resulting_resolution,[],[f3736,f121])).

fof(f3755,plain,
    ( ~ spl13_497
    | ~ spl13_72
    | spl13_493 ),
    inference(avatar_split_clause,[],[f3744,f3735,f437,f3753])).

fof(f3744,plain,
    ( ~ r2_hidden(sK3,sK4(sK1))
    | ~ spl13_72
    | ~ spl13_493 ),
    inference(unit_resulting_resolution,[],[f438,f3736,f130])).

fof(f3743,plain,
    ( ~ spl13_493
    | ~ spl13_495
    | spl13_201
    | spl13_375 ),
    inference(avatar_split_clause,[],[f2957,f2828,f1183,f3741,f3735])).

fof(f2828,plain,
    ( spl13_375
  <=> ~ m1_subset_1(sK3,sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_375])])).

fof(f2957,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK3)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_201
    | ~ spl13_375 ),
    inference(resolution,[],[f2839,f1598])).

fof(f2839,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(sK3))) )
    | ~ spl13_375 ),
    inference(resolution,[],[f2829,f130])).

fof(f2829,plain,
    ( ~ m1_subset_1(sK3,sK10(sK3))
    | ~ spl13_375 ),
    inference(avatar_component_clause,[],[f2828])).

fof(f3729,plain,
    ( spl13_490
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_162 ),
    inference(avatar_split_clause,[],[f995,f883,f339,f182,f154,f147,f140,f3727])).

fof(f995,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f884,f116])).

fof(f3722,plain,
    ( ~ spl13_489
    | spl13_475 ),
    inference(avatar_split_clause,[],[f3654,f3643,f3720])).

fof(f3654,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK4(sK1)))))
    | ~ spl13_475 ),
    inference(unit_resulting_resolution,[],[f119,f3644,f130])).

fof(f3709,plain,
    ( ~ spl13_487
    | spl13_465 ),
    inference(avatar_split_clause,[],[f3596,f3578,f3707])).

fof(f3596,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl13_465 ),
    inference(unit_resulting_resolution,[],[f119,f3579,f130])).

fof(f3701,plain,
    ( spl13_484
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f953,f596,f339,f182,f154,f147,f140,f3699])).

fof(f3699,plain,
    ( spl13_484
  <=> r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_484])])).

fof(f953,plain,
    ( r1_orders_2(sK1,sK6(sK0,sK1,sK3),sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f597,f340,f117])).

fof(f3694,plain,
    ( ~ spl13_483
    | spl13_455 ),
    inference(avatar_split_clause,[],[f3562,f3501,f3692])).

fof(f3692,plain,
    ( spl13_483
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_483])])).

fof(f3562,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))))
    | ~ spl13_455 ),
    inference(unit_resulting_resolution,[],[f119,f3502,f130])).

fof(f3502,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_455 ),
    inference(avatar_component_clause,[],[f3501])).

fof(f3680,plain,
    ( ~ spl13_481
    | spl13_475 ),
    inference(avatar_split_clause,[],[f3655,f3643,f3678])).

fof(f3655,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_475 ),
    inference(unit_resulting_resolution,[],[f3644,f121])).

fof(f3665,plain,
    ( ~ spl13_479
    | spl13_475 ),
    inference(avatar_split_clause,[],[f3653,f3643,f3663])).

fof(f3653,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),sK4(sK1))
    | ~ spl13_475 ),
    inference(unit_resulting_resolution,[],[f3644,f126])).

fof(f3652,plain,
    ( ~ spl13_477
    | spl13_461 ),
    inference(avatar_split_clause,[],[f3557,f3553,f3650])).

fof(f3650,plain,
    ( spl13_477
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_477])])).

fof(f3553,plain,
    ( spl13_461
  <=> ~ m1_subset_1(sK2,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_461])])).

fof(f3557,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_461 ),
    inference(unit_resulting_resolution,[],[f119,f3554,f130])).

fof(f3554,plain,
    ( ~ m1_subset_1(sK2,sK4(sK1))
    | ~ spl13_461 ),
    inference(avatar_component_clause,[],[f3553])).

fof(f3645,plain,
    ( ~ spl13_475
    | ~ spl13_412
    | spl13_461 ),
    inference(avatar_split_clause,[],[f3556,f3553,f3089,f3643])).

fof(f3556,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK4(sK1)))
    | ~ spl13_412
    | ~ spl13_461 ),
    inference(unit_resulting_resolution,[],[f3090,f3554,f130])).

fof(f3616,plain,
    ( ~ spl13_473
    | spl13_465 ),
    inference(avatar_split_clause,[],[f3597,f3578,f3614])).

fof(f3597,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_465 ),
    inference(unit_resulting_resolution,[],[f3579,f121])).

fof(f3607,plain,
    ( ~ spl13_471
    | spl13_465 ),
    inference(avatar_split_clause,[],[f3595,f3578,f3605])).

fof(f3595,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),u1_struct_0(sK1))
    | ~ spl13_465 ),
    inference(unit_resulting_resolution,[],[f3579,f126])).

fof(f3594,plain,
    ( ~ spl13_469
    | spl13_455 ),
    inference(avatar_split_clause,[],[f3563,f3501,f3592])).

fof(f3592,plain,
    ( spl13_469
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_469])])).

fof(f3563,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_455 ),
    inference(unit_resulting_resolution,[],[f3502,f121])).

fof(f3587,plain,
    ( ~ spl13_467
    | spl13_453 ),
    inference(avatar_split_clause,[],[f3520,f3495,f3585])).

fof(f3585,plain,
    ( spl13_467
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_467])])).

fof(f3495,plain,
    ( spl13_453
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_453])])).

fof(f3520,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_453 ),
    inference(unit_resulting_resolution,[],[f119,f3496,f130])).

fof(f3496,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl13_453 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f3580,plain,
    ( ~ spl13_465
    | ~ spl13_412
    | spl13_453 ),
    inference(avatar_split_clause,[],[f3518,f3495,f3089,f3578])).

fof(f3518,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_412
    | ~ spl13_453 ),
    inference(unit_resulting_resolution,[],[f3090,f3496,f130])).

fof(f3573,plain,
    ( ~ spl13_463
    | spl13_455 ),
    inference(avatar_split_clause,[],[f3561,f3501,f3571])).

fof(f3571,plain,
    ( spl13_463
  <=> ~ r1_tarski(u1_struct_0(sK1),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_463])])).

fof(f3561,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK10(sK2))
    | ~ spl13_455 ),
    inference(unit_resulting_resolution,[],[f3502,f126])).

fof(f3555,plain,
    ( ~ spl13_461
    | ~ spl13_6
    | spl13_257
    | spl13_457 ),
    inference(avatar_split_clause,[],[f3541,f3528,f1996,f161,f3553])).

fof(f3528,plain,
    ( spl13_457
  <=> ~ r2_hidden(sK2,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_457])])).

fof(f3541,plain,
    ( ~ m1_subset_1(sK2,sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257
    | ~ spl13_457 ),
    inference(unit_resulting_resolution,[],[f1997,f3529,f432])).

fof(f3529,plain,
    ( ~ r2_hidden(sK2,sK4(sK1))
    | ~ spl13_457 ),
    inference(avatar_component_clause,[],[f3528])).

fof(f3537,plain,
    ( ~ spl13_459
    | spl13_453 ),
    inference(avatar_split_clause,[],[f3521,f3495,f3535])).

fof(f3535,plain,
    ( spl13_459
  <=> ~ r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_459])])).

fof(f3521,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl13_453 ),
    inference(unit_resulting_resolution,[],[f3496,f121])).

fof(f3530,plain,
    ( ~ spl13_457
    | ~ spl13_72
    | spl13_453 ),
    inference(avatar_split_clause,[],[f3519,f3495,f437,f3528])).

fof(f3519,plain,
    ( ~ r2_hidden(sK2,sK4(sK1))
    | ~ spl13_72
    | ~ spl13_453 ),
    inference(unit_resulting_resolution,[],[f438,f3496,f130])).

fof(f3503,plain,
    ( ~ spl13_453
    | ~ spl13_455
    | spl13_201
    | spl13_355 ),
    inference(avatar_split_clause,[],[f2954,f2624,f1183,f3501,f3495])).

fof(f2624,plain,
    ( spl13_355
  <=> ~ m1_subset_1(sK2,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_355])])).

fof(f2954,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK10(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl13_201
    | ~ spl13_355 ),
    inference(resolution,[],[f2635,f1598])).

fof(f2635,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(sK2))) )
    | ~ spl13_355 ),
    inference(resolution,[],[f2625,f130])).

fof(f2625,plain,
    ( ~ m1_subset_1(sK2,sK10(sK2))
    | ~ spl13_355 ),
    inference(avatar_component_clause,[],[f2624])).

fof(f3490,plain,
    ( spl13_450
    | ~ spl13_60 ),
    inference(avatar_split_clause,[],[f403,f378,f3488])).

fof(f3488,plain,
    ( spl13_450
  <=> m1_subset_1(sK4(sK5(sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_450])])).

fof(f378,plain,
    ( spl13_60
  <=> l1_orders_2(sK5(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f403,plain,
    ( m1_subset_1(sK4(sK5(sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK5(sK5(sK0)))))
    | ~ spl13_60 ),
    inference(unit_resulting_resolution,[],[f379,f103])).

fof(f379,plain,
    ( l1_orders_2(sK5(sK5(sK0)))
    | ~ spl13_60 ),
    inference(avatar_component_clause,[],[f378])).

fof(f3473,plain,
    ( ~ spl13_449
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1204,f596,f285,f182,f154,f147,f140,f3471])).

fof(f3471,plain,
    ( spl13_449
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_449])])).

fof(f1204,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f597,f118])).

fof(f3430,plain,
    ( spl13_446
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1197,f596,f294,f182,f154,f147,f140,f3428])).

fof(f1197,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f597,f111])).

fof(f3381,plain,
    ( spl13_442
    | spl13_444
    | ~ spl13_6
    | ~ spl13_46
    | spl13_323 ),
    inference(avatar_split_clause,[],[f3355,f2369,f325,f161,f3379,f3376])).

fof(f3376,plain,
    ( spl13_442
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_442])])).

fof(f3355,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,sK2)
        | o_0_0_xboole_0 = sK2 )
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_323 ),
    inference(resolution,[],[f3350,f432])).

fof(f3367,plain,
    ( spl13_440
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_170 ),
    inference(avatar_split_clause,[],[f1038,f934,f182,f154,f147,f140,f3365])).

fof(f1038,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_170 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f935,f129])).

fof(f3337,plain,
    ( spl13_438
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_164 ),
    inference(avatar_split_clause,[],[f1027,f890,f182,f154,f147,f140,f3335])).

fof(f3335,plain,
    ( spl13_438
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_438])])).

fof(f1027,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_164 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f891,f129])).

fof(f3286,plain,
    ( spl13_436
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_162 ),
    inference(avatar_split_clause,[],[f1000,f883,f182,f154,f147,f140,f3284])).

fof(f1000,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_162 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f884,f129])).

fof(f3278,plain,
    ( ~ spl13_435
    | spl13_425 ),
    inference(avatar_split_clause,[],[f3213,f3209,f3276])).

fof(f3213,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(k1_zfmisc_1(sK10(sK2)))))
    | ~ spl13_425 ),
    inference(unit_resulting_resolution,[],[f119,f3210,f130])).

fof(f3257,plain,
    ( ~ spl13_433
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f950,f596,f339,f182,f154,f147,f140,f3255])).

fof(f3255,plain,
    ( spl13_433
  <=> ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_433])])).

fof(f950,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f597,f340,f118])).

fof(f3238,plain,
    ( ~ spl13_431
    | spl13_425 ),
    inference(avatar_split_clause,[],[f3214,f3209,f3236])).

fof(f3214,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_425 ),
    inference(unit_resulting_resolution,[],[f3210,f121])).

fof(f3231,plain,
    ( ~ spl13_429
    | spl13_417 ),
    inference(avatar_split_clause,[],[f3136,f3126,f3229])).

fof(f3136,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK2)))
    | ~ spl13_417 ),
    inference(unit_resulting_resolution,[],[f119,f3127,f130])).

fof(f3224,plain,
    ( ~ spl13_427
    | spl13_425 ),
    inference(avatar_split_clause,[],[f3212,f3209,f3222])).

fof(f3212,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),sK10(sK2))
    | ~ spl13_425 ),
    inference(unit_resulting_resolution,[],[f3210,f126])).

fof(f3211,plain,
    ( ~ spl13_425
    | spl13_355
    | ~ spl13_412 ),
    inference(avatar_split_clause,[],[f3112,f3089,f2624,f3209])).

fof(f3112,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(sK10(sK2)))
    | ~ spl13_355
    | ~ spl13_412 ),
    inference(unit_resulting_resolution,[],[f2625,f3090,f130])).

fof(f3153,plain,
    ( spl13_422
    | ~ spl13_6
    | spl13_405 ),
    inference(avatar_split_clause,[],[f3052,f3033,f161,f3151])).

fof(f3052,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
    | ~ spl13_6
    | ~ spl13_405 ),
    inference(unit_resulting_resolution,[],[f119,f3034,f432])).

fof(f3146,plain,
    ( ~ spl13_421
    | ~ spl13_6
    | spl13_405 ),
    inference(avatar_split_clause,[],[f3050,f3033,f161,f3144])).

fof(f3050,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK10(k1_zfmisc_1(sK3)))
    | ~ spl13_6
    | ~ spl13_405 ),
    inference(unit_resulting_resolution,[],[f119,f3034,f838])).

fof(f3135,plain,
    ( spl13_418
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f562,f227,f175,f3133])).

fof(f3133,plain,
    ( spl13_418
  <=> m1_subset_1(u1_waybel_0(sK12,sK5(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5(sK12)),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_418])])).

fof(f175,plain,
    ( spl13_10
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f227,plain,
    ( spl13_22
  <=> l1_waybel_0(sK5(sK12),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f562,plain,
    ( m1_subset_1(u1_waybel_0(sK12,sK5(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5(sK12)),u1_struct_0(sK12))))
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f176,f228,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f228,plain,
    ( l1_waybel_0(sK5(sK12),sK12)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f176,plain,
    ( l1_struct_0(sK12)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f175])).

fof(f3128,plain,
    ( ~ spl13_417
    | spl13_321
    | spl13_411 ),
    inference(avatar_split_clause,[],[f3103,f3082,f2362,f3126])).

fof(f3082,plain,
    ( spl13_411
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_411])])).

fof(f3103,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK2)
    | ~ spl13_321
    | ~ spl13_411 ),
    inference(unit_resulting_resolution,[],[f2363,f3083,f122])).

fof(f3083,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK2)
    | ~ spl13_411 ),
    inference(avatar_component_clause,[],[f3082])).

fof(f3101,plain,
    ( ~ spl13_415
    | ~ spl13_240
    | spl13_407 ),
    inference(avatar_split_clause,[],[f3070,f3042,f1735,f3099])).

fof(f3099,plain,
    ( spl13_415
  <=> ~ r1_tarski(k1_zfmisc_1(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_415])])).

fof(f3042,plain,
    ( spl13_407
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_407])])).

fof(f3070,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK3),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_407 ),
    inference(unit_resulting_resolution,[],[f3043,f1738])).

fof(f3043,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),o_0_0_xboole_0)
    | ~ spl13_407 ),
    inference(avatar_component_clause,[],[f3042])).

fof(f3091,plain,
    ( spl13_412
    | ~ spl13_6
    | ~ spl13_46
    | spl13_405 ),
    inference(avatar_split_clause,[],[f3051,f3033,f325,f161,f3089])).

fof(f3051,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK3))
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_405 ),
    inference(unit_resulting_resolution,[],[f326,f3034,f432])).

fof(f3084,plain,
    ( ~ spl13_411
    | ~ spl13_6
    | ~ spl13_46
    | spl13_405 ),
    inference(avatar_split_clause,[],[f3049,f3033,f325,f161,f3082])).

fof(f3049,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK2)
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_405 ),
    inference(unit_resulting_resolution,[],[f326,f3034,f838])).

fof(f3066,plain,
    ( ~ spl13_409
    | ~ spl13_6
    | spl13_405 ),
    inference(avatar_split_clause,[],[f3056,f3033,f161,f3064])).

fof(f3056,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl13_6
    | ~ spl13_405 ),
    inference(unit_resulting_resolution,[],[f162,f3034,f127])).

fof(f3044,plain,
    ( spl13_404
    | ~ spl13_407
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_240
    | spl13_325 ),
    inference(avatar_split_clause,[],[f3028,f2382,f1735,f325,f161,f3042,f3036])).

fof(f2382,plain,
    ( spl13_325
  <=> ~ m1_subset_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_325])])).

fof(f3028,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),o_0_0_xboole_0)
    | k1_zfmisc_1(sK3) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_46
    | ~ spl13_240
    | ~ spl13_325 ),
    inference(resolution,[],[f2562,f326])).

fof(f2562,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,X0)
        | ~ m1_subset_1(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_325 ),
    inference(resolution,[],[f2404,f432])).

fof(f2404,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ m1_subset_1(X0,o_0_0_xboole_0) )
    | ~ spl13_240
    | ~ spl13_325 ),
    inference(forward_demodulation,[],[f2400,f1736])).

fof(f2400,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(sK2,X0) )
    | ~ spl13_325 ),
    inference(resolution,[],[f2383,f130])).

fof(f2383,plain,
    ( ~ m1_subset_1(sK2,o_0_0_xboole_0)
    | ~ spl13_325 ),
    inference(avatar_component_clause,[],[f2382])).

fof(f3026,plain,
    ( ~ spl13_403
    | spl13_351 ),
    inference(avatar_split_clause,[],[f2609,f2606,f3024])).

fof(f3024,plain,
    ( spl13_403
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_403])])).

fof(f2606,plain,
    ( spl13_351
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_351])])).

fof(f2609,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_351 ),
    inference(unit_resulting_resolution,[],[f119,f2607,f130])).

fof(f2607,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1))
    | ~ spl13_351 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f2984,plain,
    ( ~ spl13_361
    | spl13_356
    | ~ spl13_6
    | ~ spl13_344 ),
    inference(avatar_split_clause,[],[f2527,f2519,f161,f2630,f2670])).

fof(f2630,plain,
    ( spl13_356
  <=> o_0_0_xboole_0 = sK10(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_356])])).

fof(f2527,plain,
    ( o_0_0_xboole_0 = sK10(sK2)
    | ~ m1_subset_1(sK3,sK10(sK2))
    | ~ spl13_6
    | ~ spl13_344 ),
    inference(resolution,[],[f2520,f838])).

fof(f2978,plain,
    ( spl13_400
    | ~ spl13_6
    | spl13_309 ),
    inference(avatar_split_clause,[],[f2301,f2282,f161,f2976])).

fof(f2976,plain,
    ( spl13_400
  <=> r2_hidden(sK10(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_400])])).

fof(f2301,plain,
    ( r2_hidden(sK10(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f119,f2283,f432])).

fof(f2971,plain,
    ( ~ spl13_399
    | ~ spl13_6
    | spl13_309 ),
    inference(avatar_split_clause,[],[f2299,f2282,f161,f2969])).

fof(f2969,plain,
    ( spl13_399
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_399])])).

fof(f2299,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f119,f2283,f838])).

fof(f2964,plain,
    ( spl13_396
    | ~ spl13_46
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2349,f2211,f325,f2962])).

fof(f2349,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_46
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f326,f2212,f130])).

fof(f2939,plain,
    ( spl13_394
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2347,f2211,f2937])).

fof(f2347,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f2212,f121])).

fof(f2932,plain,
    ( ~ spl13_393
    | ~ spl13_240
    | spl13_391 ),
    inference(avatar_split_clause,[],[f2916,f2913,f1735,f2930])).

fof(f2930,plain,
    ( spl13_393
  <=> ~ r1_tarski(sK10(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_393])])).

fof(f2916,plain,
    ( ~ r1_tarski(sK10(sK3),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_391 ),
    inference(unit_resulting_resolution,[],[f2914,f1738])).

fof(f2915,plain,
    ( ~ spl13_391
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_386 ),
    inference(avatar_split_clause,[],[f2908,f2887,f1735,f161,f2913])).

fof(f2908,plain,
    ( ~ m1_subset_1(sK10(sK3),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_386 ),
    inference(forward_demodulation,[],[f2903,f1736])).

fof(f2903,plain,
    ( ~ m1_subset_1(sK10(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_386 ),
    inference(unit_resulting_resolution,[],[f162,f2888,f131])).

fof(f2897,plain,
    ( ~ spl13_389
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2346,f2211,f2895])).

fof(f2346,plain,
    ( ~ r2_hidden(sK2,k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))))
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f2212,f120])).

fof(f2889,plain,
    ( spl13_386
    | ~ spl13_6
    | spl13_377 ),
    inference(avatar_split_clause,[],[f2850,f2831,f161,f2887])).

fof(f2831,plain,
    ( spl13_377
  <=> o_0_0_xboole_0 != sK10(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_377])])).

fof(f2850,plain,
    ( r2_hidden(sK10(sK10(sK3)),sK10(sK3))
    | ~ spl13_6
    | ~ spl13_377 ),
    inference(unit_resulting_resolution,[],[f162,f119,f2832,f431])).

fof(f2832,plain,
    ( o_0_0_xboole_0 != sK10(sK3)
    | ~ spl13_377 ),
    inference(avatar_component_clause,[],[f2831])).

fof(f2882,plain,
    ( ~ spl13_385
    | ~ spl13_6
    | spl13_377 ),
    inference(avatar_split_clause,[],[f2841,f2831,f161,f2880])).

fof(f2841,plain,
    ( ~ r2_hidden(sK10(sK3),sK10(sK10(sK3)))
    | ~ spl13_6
    | ~ spl13_377 ),
    inference(unit_resulting_resolution,[],[f119,f2832,f838])).

fof(f2875,plain,
    ( ~ spl13_383
    | spl13_375 ),
    inference(avatar_split_clause,[],[f2837,f2828,f2873])).

fof(f2873,plain,
    ( spl13_383
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK10(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_383])])).

fof(f2837,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK10(sK3))))
    | ~ spl13_375 ),
    inference(unit_resulting_resolution,[],[f119,f2829,f130])).

fof(f2865,plain,
    ( spl13_380
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f556,f220,f147,f2863])).

fof(f2863,plain,
    ( spl13_380
  <=> m1_subset_1(u1_waybel_0(sK0,sK5(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_380])])).

fof(f220,plain,
    ( spl13_20
  <=> l1_waybel_0(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f556,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK5(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5(sK0)),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f148,f221,f125])).

fof(f221,plain,
    ( l1_waybel_0(sK5(sK0),sK0)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f2858,plain,
    ( ~ spl13_379
    | ~ spl13_6
    | spl13_377 ),
    inference(avatar_split_clause,[],[f2851,f2831,f161,f2856])).

fof(f2856,plain,
    ( spl13_379
  <=> ~ v1_xboole_0(sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_379])])).

fof(f2851,plain,
    ( ~ v1_xboole_0(sK10(sK3))
    | ~ spl13_6
    | ~ spl13_377 ),
    inference(unit_resulting_resolution,[],[f162,f2832,f127])).

fof(f2836,plain,
    ( ~ spl13_375
    | spl13_376
    | ~ spl13_6
    | ~ spl13_330 ),
    inference(avatar_split_clause,[],[f2451,f2423,f161,f2834,f2828])).

fof(f2834,plain,
    ( spl13_376
  <=> o_0_0_xboole_0 = sK10(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_376])])).

fof(f2451,plain,
    ( o_0_0_xboole_0 = sK10(sK3)
    | ~ m1_subset_1(sK3,sK10(sK3))
    | ~ spl13_6
    | ~ spl13_330 ),
    inference(resolution,[],[f2424,f838])).

fof(f2786,plain,
    ( ~ spl13_373
    | spl13_361 ),
    inference(avatar_split_clause,[],[f2673,f2670,f2784])).

fof(f2784,plain,
    ( spl13_373
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_373])])).

fof(f2673,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_361 ),
    inference(unit_resulting_resolution,[],[f119,f2671,f130])).

fof(f2779,plain,
    ( ~ spl13_371
    | ~ spl13_240
    | spl13_369 ),
    inference(avatar_split_clause,[],[f2739,f2736,f1735,f2777])).

fof(f2777,plain,
    ( spl13_371
  <=> ~ r1_tarski(sK10(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_371])])).

fof(f2736,plain,
    ( spl13_369
  <=> ~ m1_subset_1(sK10(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_369])])).

fof(f2739,plain,
    ( ~ r1_tarski(sK10(sK2),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_369 ),
    inference(unit_resulting_resolution,[],[f2737,f1738])).

fof(f2737,plain,
    ( ~ m1_subset_1(sK10(sK2),o_0_0_xboole_0)
    | ~ spl13_369 ),
    inference(avatar_component_clause,[],[f2736])).

fof(f2738,plain,
    ( ~ spl13_369
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_366 ),
    inference(avatar_split_clause,[],[f2731,f2695,f1735,f161,f2736])).

fof(f2731,plain,
    ( ~ m1_subset_1(sK10(sK2),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_366 ),
    inference(forward_demodulation,[],[f2726,f1736])).

fof(f2726,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_366 ),
    inference(unit_resulting_resolution,[],[f162,f2696,f131])).

fof(f2697,plain,
    ( spl13_366
    | ~ spl13_6
    | spl13_357 ),
    inference(avatar_split_clause,[],[f2649,f2627,f161,f2695])).

fof(f2649,plain,
    ( r2_hidden(sK10(sK10(sK2)),sK10(sK2))
    | ~ spl13_6
    | ~ spl13_357 ),
    inference(unit_resulting_resolution,[],[f162,f119,f2628,f431])).

fof(f2690,plain,
    ( ~ spl13_365
    | ~ spl13_6
    | spl13_357 ),
    inference(avatar_split_clause,[],[f2637,f2627,f161,f2688])).

fof(f2637,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(sK10(sK2)))
    | ~ spl13_6
    | ~ spl13_357 ),
    inference(unit_resulting_resolution,[],[f119,f2628,f838])).

fof(f2683,plain,
    ( ~ spl13_363
    | spl13_355 ),
    inference(avatar_split_clause,[],[f2633,f2624,f2681])).

fof(f2681,plain,
    ( spl13_363
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_363])])).

fof(f2633,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK10(sK2))))
    | ~ spl13_355 ),
    inference(unit_resulting_resolution,[],[f119,f2625,f130])).

fof(f2672,plain,
    ( ~ spl13_361
    | ~ spl13_6
    | spl13_347
    | spl13_357 ),
    inference(avatar_split_clause,[],[f2648,f2627,f2536,f161,f2670])).

fof(f2536,plain,
    ( spl13_347
  <=> ~ r2_hidden(sK3,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_347])])).

fof(f2648,plain,
    ( ~ m1_subset_1(sK3,sK10(sK2))
    | ~ spl13_6
    | ~ spl13_347
    | ~ spl13_357 ),
    inference(unit_resulting_resolution,[],[f162,f2537,f2628,f431])).

fof(f2537,plain,
    ( ~ r2_hidden(sK3,sK10(sK2))
    | ~ spl13_347 ),
    inference(avatar_component_clause,[],[f2536])).

fof(f2657,plain,
    ( ~ spl13_359
    | ~ spl13_6
    | spl13_357 ),
    inference(avatar_split_clause,[],[f2650,f2627,f161,f2655])).

fof(f2655,plain,
    ( spl13_359
  <=> ~ v1_xboole_0(sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_359])])).

fof(f2650,plain,
    ( ~ v1_xboole_0(sK10(sK2))
    | ~ spl13_6
    | ~ spl13_357 ),
    inference(unit_resulting_resolution,[],[f162,f2628,f127])).

fof(f2632,plain,
    ( ~ spl13_355
    | spl13_356
    | ~ spl13_6
    | ~ spl13_328 ),
    inference(avatar_split_clause,[],[f2441,f2416,f161,f2630,f2624])).

fof(f2441,plain,
    ( o_0_0_xboole_0 = sK10(sK2)
    | ~ m1_subset_1(sK2,sK10(sK2))
    | ~ spl13_6
    | ~ spl13_328 ),
    inference(resolution,[],[f2417,f838])).

fof(f2619,plain,
    ( spl13_352
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1200,f596,f285,f182,f154,f147,f140,f2617])).

fof(f1200,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f597,f116])).

fof(f2608,plain,
    ( ~ spl13_351
    | spl13_263
    | spl13_317 ),
    inference(avatar_split_clause,[],[f2585,f2335,f2033,f2606])).

fof(f2033,plain,
    ( spl13_263
  <=> ~ v1_xboole_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_263])])).

fof(f2335,plain,
    ( spl13_317
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_317])])).

fof(f2585,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1))
    | ~ spl13_263
    | ~ spl13_317 ),
    inference(unit_resulting_resolution,[],[f2034,f2336,f122])).

fof(f2336,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1))
    | ~ spl13_317 ),
    inference(avatar_component_clause,[],[f2335])).

fof(f2034,plain,
    ( ~ v1_xboole_0(sK4(sK1))
    | ~ spl13_263 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f2576,plain,
    ( spl13_348
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f1195,f596,f294,f182,f154,f147,f140,f2574])).

fof(f1195,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f597,f109])).

fof(f2538,plain,
    ( ~ spl13_347
    | ~ spl13_344 ),
    inference(avatar_split_clause,[],[f2523,f2519,f2536])).

fof(f2523,plain,
    ( ~ r2_hidden(sK3,sK10(sK2))
    | ~ spl13_344 ),
    inference(unit_resulting_resolution,[],[f2520,f120])).

fof(f2521,plain,
    ( spl13_344
    | spl13_323
    | ~ spl13_338 ),
    inference(avatar_split_clause,[],[f2513,f2495,f2369,f2519])).

fof(f2495,plain,
    ( spl13_338
  <=> m1_subset_1(sK10(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_338])])).

fof(f2513,plain,
    ( r2_hidden(sK10(sK2),sK3)
    | ~ spl13_323
    | ~ spl13_338 ),
    inference(unit_resulting_resolution,[],[f2370,f2496,f122])).

fof(f2496,plain,
    ( m1_subset_1(sK10(sK2),sK3)
    | ~ spl13_338 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2512,plain,
    ( spl13_342
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f956,f596,f339,f182,f154,f147,f140,f2510])).

fof(f956,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK6(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f597,f340,f116])).

fof(f2504,plain,
    ( ~ spl13_341
    | ~ spl13_330 ),
    inference(avatar_split_clause,[],[f2447,f2423,f2502])).

fof(f2502,plain,
    ( spl13_341
  <=> ~ r2_hidden(sK3,sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_341])])).

fof(f2447,plain,
    ( ~ r2_hidden(sK3,sK10(sK3))
    | ~ spl13_330 ),
    inference(unit_resulting_resolution,[],[f2424,f120])).

fof(f2497,plain,
    ( spl13_338
    | ~ spl13_46
    | ~ spl13_328 ),
    inference(avatar_split_clause,[],[f2438,f2416,f325,f2495])).

fof(f2438,plain,
    ( m1_subset_1(sK10(sK2),sK3)
    | ~ spl13_46
    | ~ spl13_328 ),
    inference(unit_resulting_resolution,[],[f326,f2417,f130])).

fof(f2490,plain,
    ( ~ spl13_337
    | ~ spl13_328 ),
    inference(avatar_split_clause,[],[f2435,f2416,f2488])).

fof(f2488,plain,
    ( spl13_337
  <=> ~ r2_hidden(sK2,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_337])])).

fof(f2435,plain,
    ( ~ r2_hidden(sK2,sK10(sK2))
    | ~ spl13_328 ),
    inference(unit_resulting_resolution,[],[f2417,f120])).

fof(f2477,plain,
    ( ~ spl13_335
    | ~ spl13_240
    | spl13_333 ),
    inference(avatar_split_clause,[],[f2463,f2460,f1735,f2475])).

fof(f2475,plain,
    ( spl13_335
  <=> ~ r1_tarski(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_335])])).

fof(f2460,plain,
    ( spl13_333
  <=> ~ m1_subset_1(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_333])])).

fof(f2463,plain,
    ( ~ r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_333 ),
    inference(unit_resulting_resolution,[],[f2461,f1738])).

fof(f2461,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl13_333 ),
    inference(avatar_component_clause,[],[f2460])).

fof(f2462,plain,
    ( ~ spl13_333
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_330 ),
    inference(avatar_split_clause,[],[f2455,f2423,f1735,f161,f2460])).

fof(f2455,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_330 ),
    inference(forward_demodulation,[],[f2450,f1736])).

fof(f2450,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_330 ),
    inference(unit_resulting_resolution,[],[f162,f2424,f131])).

fof(f2425,plain,
    ( spl13_330
    | spl13_323 ),
    inference(avatar_split_clause,[],[f2375,f2369,f2423])).

fof(f2375,plain,
    ( r2_hidden(sK10(sK3),sK3)
    | ~ spl13_323 ),
    inference(unit_resulting_resolution,[],[f119,f2370,f122])).

fof(f2418,plain,
    ( spl13_328
    | spl13_321 ),
    inference(avatar_split_clause,[],[f2372,f2362,f2416])).

fof(f2372,plain,
    ( r2_hidden(sK10(sK2),sK2)
    | ~ spl13_321 ),
    inference(unit_resulting_resolution,[],[f119,f2363,f122])).

fof(f2411,plain,
    ( ~ spl13_327
    | ~ spl13_240
    | spl13_325 ),
    inference(avatar_split_clause,[],[f2397,f2382,f1735,f2409])).

fof(f2409,plain,
    ( spl13_327
  <=> ~ r1_tarski(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_327])])).

fof(f2397,plain,
    ( ~ r1_tarski(sK2,o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_325 ),
    inference(unit_resulting_resolution,[],[f2383,f1738])).

fof(f2384,plain,
    ( ~ spl13_325
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2357,f2211,f1735,f161,f2382])).

fof(f2357,plain,
    ( ~ m1_subset_1(sK2,o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_240
    | ~ spl13_290 ),
    inference(forward_demodulation,[],[f2350,f1736])).

fof(f2350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f162,f2212,f131])).

fof(f2371,plain,
    ( ~ spl13_323
    | ~ spl13_46
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2351,f2211,f325,f2369])).

fof(f2351,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl13_46
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f326,f2212,f131])).

fof(f2364,plain,
    ( ~ spl13_321
    | ~ spl13_290 ),
    inference(avatar_split_clause,[],[f2348,f2211,f2362])).

fof(f2348,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl13_290 ),
    inference(unit_resulting_resolution,[],[f2212,f128])).

fof(f2344,plain,
    ( spl13_318
    | ~ spl13_6
    | ~ spl13_72
    | spl13_309 ),
    inference(avatar_split_clause,[],[f2300,f2282,f437,f161,f2342])).

fof(f2300,plain,
    ( r2_hidden(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_72
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f438,f2283,f432])).

fof(f2337,plain,
    ( ~ spl13_317
    | ~ spl13_6
    | ~ spl13_72
    | spl13_309 ),
    inference(avatar_split_clause,[],[f2298,f2282,f437,f161,f2335])).

fof(f2298,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_72
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f438,f2283,f838])).

fof(f2330,plain,
    ( ~ spl13_315
    | ~ spl13_240
    | spl13_311 ),
    inference(avatar_split_clause,[],[f2316,f2291,f1735,f2328])).

fof(f2328,plain,
    ( spl13_315
  <=> ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_315])])).

fof(f2316,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl13_240
    | ~ spl13_311 ),
    inference(unit_resulting_resolution,[],[f2292,f1738])).

fof(f2312,plain,
    ( ~ spl13_313
    | ~ spl13_6
    | spl13_309 ),
    inference(avatar_split_clause,[],[f2305,f2282,f161,f2310])).

fof(f2310,plain,
    ( spl13_313
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_313])])).

fof(f2305,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_309 ),
    inference(unit_resulting_resolution,[],[f162,f2283,f127])).

fof(f2293,plain,
    ( spl13_308
    | ~ spl13_311
    | ~ spl13_6
    | ~ spl13_72
    | ~ spl13_92
    | spl13_235
    | spl13_237 ),
    inference(avatar_split_clause,[],[f2223,f1707,f1657,f544,f437,f161,f2291,f2285])).

fof(f2285,plain,
    ( spl13_308
  <=> k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_308])])).

fof(f1657,plain,
    ( spl13_235
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_235])])).

fof(f2223,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),o_0_0_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_72
    | ~ spl13_92
    | ~ spl13_235
    | ~ spl13_237 ),
    inference(resolution,[],[f1809,f438])).

fof(f1809,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1),X0)
        | ~ m1_subset_1(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_235
    | ~ spl13_237 ),
    inference(resolution,[],[f1716,f432])).

fof(f1716,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ m1_subset_1(X0,o_0_0_xboole_0) )
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_235
    | ~ spl13_237 ),
    inference(forward_demodulation,[],[f1712,f1664])).

fof(f1664,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_235 ),
    inference(subsumption_resolution,[],[f1663,f545])).

fof(f1663,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_235 ),
    inference(resolution,[],[f1658,f432])).

fof(f1658,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_235 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f1712,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0)) )
    | ~ spl13_237 ),
    inference(resolution,[],[f1708,f130])).

fof(f2280,plain,
    ( spl13_306
    | ~ spl13_170
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1981,f1183,f934,f2278])).

fof(f1981,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_170
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f935,f122])).

fof(f2272,plain,
    ( spl13_304
    | ~ spl13_164
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1945,f1183,f890,f2270])).

fof(f2270,plain,
    ( spl13_304
  <=> r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_304])])).

fof(f1945,plain,
    ( r2_hidden(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_164
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f891,f122])).

fof(f2265,plain,
    ( spl13_302
    | ~ spl13_162
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1892,f1183,f883,f2263])).

fof(f1892,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_162
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f884,f122])).

fof(f2258,plain,
    ( spl13_300
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1831,f1183,f876,f633,f460,f2256])).

fof(f1831,plain,
    ( m1_subset_1(k1_funct_1(u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(backward_demodulation,[],[f1827,f1830])).

fof(f1830,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f119,f461,f634,f877,f132])).

fof(f1827,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1))) = k1_funct_1(u1_waybel_0(sK0,sK1),sK10(u1_struct_0(sK1)))
    | ~ spl13_76
    | ~ spl13_112
    | ~ spl13_160
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f119,f461,f634,f877,f133])).

fof(f2248,plain,
    ( ~ spl13_299
    | ~ spl13_6
    | ~ spl13_170
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1977,f1155,f934,f161,f2246])).

fof(f1977,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_170
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f1156,f935,f838])).

fof(f2241,plain,
    ( ~ spl13_297
    | ~ spl13_6
    | ~ spl13_164
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1941,f1155,f890,f161,f2239])).

fof(f1941,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_164
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f1156,f891,f838])).

fof(f2234,plain,
    ( ~ spl13_295
    | ~ spl13_6
    | ~ spl13_162
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1888,f1155,f883,f161,f2232])).

fof(f1888,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_6
    | ~ spl13_162
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f1156,f884,f838])).

fof(f2221,plain,
    ( spl13_292
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2098,f2083,f182,f154,f147,f140,f2219])).

fof(f2219,plain,
    ( spl13_292
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK10(sK4(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_292])])).

fof(f2098,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK10(sK4(sK1))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f2084,f129])).

fof(f2213,plain,
    ( spl13_290
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f1164,f294,f182,f154,f147,f140,f2211])).

fof(f1164,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f295,f111])).

fof(f2205,plain,
    ( ~ spl13_289
    | spl13_279 ),
    inference(avatar_split_clause,[],[f2163,f2142,f2203])).

fof(f2203,plain,
    ( spl13_289
  <=> ~ r2_hidden(sK9(sK0,sK1,sK3),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_289])])).

fof(f2163,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK3),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_279 ),
    inference(unit_resulting_resolution,[],[f119,f2143,f130])).

fof(f2143,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_279 ),
    inference(avatar_component_clause,[],[f2142])).

fof(f2198,plain,
    ( ~ spl13_287
    | spl13_277 ),
    inference(avatar_split_clause,[],[f2159,f2135,f2196])).

fof(f2196,plain,
    ( spl13_287
  <=> ~ r2_hidden(sK9(sK0,sK1,sK2),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_287])])).

fof(f2159,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_277 ),
    inference(unit_resulting_resolution,[],[f119,f2136,f130])).

fof(f2180,plain,
    ( spl13_284
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37 ),
    inference(avatar_split_clause,[],[f1162,f285,f182,f154,f147,f140,f2178])).

fof(f2178,plain,
    ( spl13_284
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_284])])).

fof(f1162,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f286,f117])).

fof(f2158,plain,
    ( ~ spl13_283
    | spl13_259 ),
    inference(avatar_split_clause,[],[f2041,f2005,f2156])).

fof(f2156,plain,
    ( spl13_283
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_283])])).

fof(f2005,plain,
    ( spl13_259
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_259])])).

fof(f2041,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(sK4(sK1))))
    | ~ spl13_259 ),
    inference(unit_resulting_resolution,[],[f119,f2006,f130])).

fof(f2006,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK1))
    | ~ spl13_259 ),
    inference(avatar_component_clause,[],[f2005])).

fof(f2151,plain,
    ( ~ spl13_281
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37 ),
    inference(avatar_split_clause,[],[f1161,f285,f182,f154,f147,f140,f2149])).

fof(f1161,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f286,f118])).

fof(f2144,plain,
    ( ~ spl13_279
    | ~ spl13_6
    | spl13_179
    | spl13_257 ),
    inference(avatar_split_clause,[],[f2019,f1996,f985,f161,f2142])).

fof(f2019,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_179
    | ~ spl13_257 ),
    inference(unit_resulting_resolution,[],[f162,f986,f1997,f431])).

fof(f2137,plain,
    ( ~ spl13_277
    | ~ spl13_6
    | spl13_177
    | spl13_257 ),
    inference(avatar_split_clause,[],[f2018,f1996,f978,f161,f2135])).

fof(f2018,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_177
    | ~ spl13_257 ),
    inference(unit_resulting_resolution,[],[f162,f979,f1997,f431])).

fof(f2119,plain,
    ( spl13_274
    | spl13_201
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2104,f2083,f1183,f2117])).

fof(f2117,plain,
    ( spl13_274
  <=> r2_hidden(sK10(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_274])])).

fof(f2104,plain,
    ( r2_hidden(sK10(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_201
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f1184,f2084,f122])).

fof(f2112,plain,
    ( ~ spl13_273
    | ~ spl13_6
    | spl13_199
    | ~ spl13_270 ),
    inference(avatar_split_clause,[],[f2100,f2083,f1155,f161,f2110])).

fof(f2100,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(sK4(sK1)))
    | ~ spl13_6
    | ~ spl13_199
    | ~ spl13_270 ),
    inference(unit_resulting_resolution,[],[f1156,f2084,f838])).

fof(f2085,plain,
    ( spl13_270
    | ~ spl13_72
    | ~ spl13_266 ),
    inference(avatar_split_clause,[],[f2071,f2056,f437,f2083])).

fof(f2071,plain,
    ( m1_subset_1(sK10(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl13_72
    | ~ spl13_266 ),
    inference(unit_resulting_resolution,[],[f438,f2057,f130])).

fof(f2065,plain,
    ( spl13_268
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51 ),
    inference(avatar_split_clause,[],[f955,f339,f182,f154,f147,f140,f2063])).

fof(f955,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f340,f117])).

fof(f2058,plain,
    ( spl13_266
    | ~ spl13_6
    | spl13_257 ),
    inference(avatar_split_clause,[],[f2020,f1996,f161,f2056])).

fof(f2020,plain,
    ( r2_hidden(sK10(sK4(sK1)),sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257 ),
    inference(unit_resulting_resolution,[],[f162,f119,f1997,f431])).

fof(f2051,plain,
    ( ~ spl13_265
    | ~ spl13_6
    | spl13_257 ),
    inference(avatar_split_clause,[],[f2008,f1996,f161,f2049])).

fof(f2008,plain,
    ( ~ r2_hidden(sK4(sK1),sK10(sK4(sK1)))
    | ~ spl13_6
    | ~ spl13_257 ),
    inference(unit_resulting_resolution,[],[f119,f1997,f838])).

fof(f2035,plain,
    ( ~ spl13_263
    | ~ spl13_6
    | spl13_257 ),
    inference(avatar_split_clause,[],[f2021,f1996,f161,f2033])).

fof(f2021,plain,
    ( ~ v1_xboole_0(sK4(sK1))
    | ~ spl13_6
    | ~ spl13_257 ),
    inference(unit_resulting_resolution,[],[f162,f1997,f127])).

fof(f2028,plain,
    ( ~ spl13_261
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51 ),
    inference(avatar_split_clause,[],[f952,f339,f182,f154,f147,f140,f2026])).

fof(f952,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f340,f118])).

fof(f2007,plain,
    ( spl13_256
    | ~ spl13_259
    | ~ spl13_6
    | spl13_251 ),
    inference(avatar_split_clause,[],[f1947,f1917,f161,f2005,f1999])).

fof(f1917,plain,
    ( spl13_251
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_251])])).

fof(f1947,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK1))
    | o_0_0_xboole_0 = sK4(sK1)
    | ~ spl13_6
    | ~ spl13_251 ),
    inference(resolution,[],[f1918,f432])).

fof(f1918,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(sK1))
    | ~ spl13_251 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1960,plain,
    ( ~ spl13_255
    | spl13_249 ),
    inference(avatar_split_clause,[],[f1909,f1905,f1958])).

fof(f1958,plain,
    ( spl13_255
  <=> ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_255])])).

fof(f1905,plain,
    ( spl13_249
  <=> ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_249])])).

fof(f1909,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_249 ),
    inference(unit_resulting_resolution,[],[f119,f1906,f130])).

fof(f1906,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_249 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1926,plain,
    ( ~ spl13_253
    | spl13_249 ),
    inference(avatar_split_clause,[],[f1910,f1905,f1924])).

fof(f1924,plain,
    ( spl13_253
  <=> ~ r2_hidden(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_253])])).

fof(f1910,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_249 ),
    inference(unit_resulting_resolution,[],[f1906,f121])).

fof(f1919,plain,
    ( ~ spl13_251
    | ~ spl13_72
    | spl13_249 ),
    inference(avatar_split_clause,[],[f1908,f1905,f437,f1917])).

fof(f1908,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_249 ),
    inference(unit_resulting_resolution,[],[f438,f1906,f130])).

fof(f1907,plain,
    ( ~ spl13_249
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1900,f1183,f1905])).

fof(f1900,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_201 ),
    inference(duplicate_literal_removal,[],[f1899])).

fof(f1899,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl13_201 ),
    inference(resolution,[],[f1867,f1598])).

fof(f1867,plain,
    ( ! [X3] :
        ( ~ r2_hidden(u1_struct_0(sK1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl13_201 ),
    inference(resolution,[],[f1598,f120])).

fof(f1845,plain,
    ( spl13_246
    | ~ spl13_148
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1804,f1183,f811,f1843])).

fof(f1843,plain,
    ( spl13_246
  <=> r2_hidden(sK6(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_246])])).

fof(f1804,plain,
    ( r2_hidden(sK6(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_148
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f1184,f812,f122])).

fof(f1781,plain,
    ( ~ spl13_245
    | spl13_233
    | ~ spl13_240 ),
    inference(avatar_split_clause,[],[f1772,f1735,f1591,f1779])).

fof(f1779,plain,
    ( spl13_245
  <=> ~ r1_tarski(sK6(sK0,sK1,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_245])])).

fof(f1772,plain,
    ( ~ r1_tarski(sK6(sK0,sK1,sK3),o_0_0_xboole_0)
    | ~ spl13_233
    | ~ spl13_240 ),
    inference(unit_resulting_resolution,[],[f1592,f1738])).

fof(f1745,plain,
    ( ~ spl13_243
    | ~ spl13_6
    | ~ spl13_92
    | spl13_215
    | spl13_235 ),
    inference(avatar_split_clause,[],[f1669,f1657,f1376,f544,f161,f1743])).

fof(f1376,plain,
    ( spl13_215
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_215])])).

fof(f1669,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_215
    | ~ spl13_235 ),
    inference(backward_demodulation,[],[f1664,f1377])).

fof(f1377,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_215 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1737,plain,
    ( spl13_240
    | ~ spl13_6
    | ~ spl13_92
    | spl13_235 ),
    inference(avatar_split_clause,[],[f1664,f1657,f544,f161,f1735])).

fof(f1723,plain,
    ( spl13_238
    | ~ spl13_6
    | ~ spl13_90
    | ~ spl13_92
    | spl13_235 ),
    inference(avatar_split_clause,[],[f1665,f1657,f544,f528,f161,f1721])).

fof(f1665,plain,
    ( o_0_0_xboole_0 = sK10(o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_90
    | ~ spl13_92
    | ~ spl13_235 ),
    inference(backward_demodulation,[],[f1664,f529])).

fof(f1709,plain,
    ( ~ spl13_237
    | ~ spl13_6
    | ~ spl13_92
    | spl13_209
    | spl13_235 ),
    inference(avatar_split_clause,[],[f1667,f1657,f1297,f544,f161,f1707])).

fof(f1667,plain,
    ( ~ m1_subset_1(sK4(sK1),o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_209
    | ~ spl13_235 ),
    inference(backward_demodulation,[],[f1664,f1298])).

fof(f1698,plain,
    ( spl13_228
    | ~ spl13_6
    | ~ spl13_92
    | spl13_235 ),
    inference(avatar_split_clause,[],[f1666,f1657,f544,f161,f1574])).

fof(f1666,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_235 ),
    inference(backward_demodulation,[],[f1664,f545])).

fof(f1678,plain,
    ( ~ spl13_6
    | ~ spl13_92
    | spl13_229
    | spl13_235 ),
    inference(avatar_contradiction_clause,[],[f1677])).

fof(f1677,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_229
    | ~ spl13_235 ),
    inference(subsumption_resolution,[],[f1666,f1572])).

fof(f1572,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_229 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1571,plain,
    ( spl13_229
  <=> ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_229])])).

fof(f1662,plain,
    ( spl13_234
    | ~ spl13_6
    | ~ spl13_208
    | ~ spl13_212 ),
    inference(avatar_split_clause,[],[f1655,f1347,f1300,f161,f1660])).

fof(f1300,plain,
    ( spl13_208
  <=> m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_208])])).

fof(f1347,plain,
    ( spl13_212
  <=> r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_212])])).

fof(f1655,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_208
    | ~ spl13_212 ),
    inference(forward_demodulation,[],[f1348,f1619])).

fof(f1619,plain,
    ( o_0_0_xboole_0 = sK4(sK1)
    | ~ spl13_6
    | ~ spl13_208 ),
    inference(unit_resulting_resolution,[],[f119,f1617,f432])).

fof(f1617,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(sK1))
    | ~ spl13_6
    | ~ spl13_208 ),
    inference(unit_resulting_resolution,[],[f162,f1301,f131])).

fof(f1301,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_208 ),
    inference(avatar_component_clause,[],[f1300])).

fof(f1348,plain,
    ( r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_212 ),
    inference(avatar_component_clause,[],[f1347])).

fof(f1648,plain,
    ( ~ spl13_6
    | ~ spl13_92
    | ~ spl13_208
    | spl13_213
    | spl13_229 ),
    inference(avatar_contradiction_clause,[],[f1647])).

fof(f1647,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_208
    | ~ spl13_213
    | ~ spl13_229 ),
    inference(subsumption_resolution,[],[f1639,f1572])).

fof(f1639,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_208
    | ~ spl13_213 ),
    inference(backward_demodulation,[],[f1637,f545])).

fof(f1637,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_208
    | ~ spl13_213 ),
    inference(subsumption_resolution,[],[f1631,f545])).

fof(f1631,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_208
    | ~ spl13_213 ),
    inference(backward_demodulation,[],[f1619,f1353])).

fof(f1353,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_213 ),
    inference(resolution,[],[f1351,f432])).

fof(f1351,plain,
    ( ~ r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_213 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1350,plain,
    ( spl13_213
  <=> ~ r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_213])])).

fof(f1596,plain,
    ( spl13_232
    | ~ spl13_102
    | ~ spl13_198 ),
    inference(avatar_split_clause,[],[f1465,f1158,f596,f1594])).

fof(f1594,plain,
    ( spl13_232
  <=> m1_subset_1(sK6(sK0,sK1,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_232])])).

fof(f1158,plain,
    ( spl13_198
  <=> u1_struct_0(sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_198])])).

fof(f1465,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),o_0_0_xboole_0)
    | ~ spl13_102
    | ~ spl13_198 ),
    inference(backward_demodulation,[],[f1159,f597])).

fof(f1159,plain,
    ( u1_struct_0(sK1) = o_0_0_xboole_0
    | ~ spl13_198 ),
    inference(avatar_component_clause,[],[f1158])).

fof(f1589,plain,
    ( ~ spl13_231
    | ~ spl13_198
    | spl13_217 ),
    inference(avatar_split_clause,[],[f1513,f1389,f1158,f1587])).

fof(f1587,plain,
    ( spl13_231
  <=> ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_231])])).

fof(f1389,plain,
    ( spl13_217
  <=> ~ r1_tarski(u1_struct_0(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_217])])).

fof(f1513,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_198
    | ~ spl13_217 ),
    inference(backward_demodulation,[],[f1159,f1390])).

fof(f1390,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),o_0_0_xboole_0)
    | ~ spl13_217 ),
    inference(avatar_component_clause,[],[f1389])).

fof(f1576,plain,
    ( spl13_228
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_198
    | spl13_219 ),
    inference(avatar_split_clause,[],[f1530,f1396,f1158,f544,f161,f1574])).

fof(f1396,plain,
    ( spl13_219
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_219])])).

fof(f1530,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_198
    | ~ spl13_219 ),
    inference(backward_demodulation,[],[f1528,f545])).

fof(f1528,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_92
    | ~ spl13_198
    | ~ spl13_219 ),
    inference(subsumption_resolution,[],[f1515,f545])).

fof(f1515,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_198
    | ~ spl13_219 ),
    inference(backward_demodulation,[],[f1159,f1399])).

fof(f1399,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_219 ),
    inference(resolution,[],[f1397,f432])).

fof(f1397,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_219 ),
    inference(avatar_component_clause,[],[f1396])).

fof(f1462,plain,
    ( spl13_226
    | ~ spl13_102
    | spl13_201 ),
    inference(avatar_split_clause,[],[f1314,f1183,f596,f1460])).

fof(f1460,plain,
    ( spl13_226
  <=> r2_hidden(sK6(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_226])])).

fof(f1314,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_102
    | ~ spl13_201 ),
    inference(unit_resulting_resolution,[],[f597,f1184,f122])).

fof(f1444,plain,
    ( ~ spl13_225
    | ~ spl13_6
    | ~ spl13_148
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1420,f1155,f811,f161,f1442])).

fof(f1442,plain,
    ( spl13_225
  <=> ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_225])])).

fof(f1420,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK1,o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_148
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f1156,f812,f838])).

fof(f1437,plain,
    ( ~ spl13_223
    | ~ spl13_6
    | ~ spl13_102
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1320,f1155,f596,f161,f1435])).

fof(f1435,plain,
    ( spl13_223
  <=> ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_223])])).

fof(f1320,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK1,sK3))
    | ~ spl13_6
    | ~ spl13_102
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f597,f1156,f838])).

fof(f1429,plain,
    ( ~ spl13_221
    | spl13_209 ),
    inference(avatar_split_clause,[],[f1328,f1297,f1427])).

fof(f1427,plain,
    ( spl13_221
  <=> ~ r2_hidden(sK4(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_221])])).

fof(f1328,plain,
    ( ~ r2_hidden(sK4(sK1),sK10(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl13_209 ),
    inference(unit_resulting_resolution,[],[f119,f1298,f130])).

fof(f1398,plain,
    ( ~ spl13_219
    | spl13_215 ),
    inference(avatar_split_clause,[],[f1381,f1376,f1396])).

fof(f1381,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_215 ),
    inference(unit_resulting_resolution,[],[f1377,f121])).

fof(f1391,plain,
    ( ~ spl13_217
    | spl13_215 ),
    inference(avatar_split_clause,[],[f1379,f1376,f1389])).

fof(f1379,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),o_0_0_xboole_0)
    | ~ spl13_215 ),
    inference(unit_resulting_resolution,[],[f1377,f126])).

fof(f1378,plain,
    ( ~ spl13_215
    | ~ spl13_6
    | ~ spl13_204 ),
    inference(avatar_split_clause,[],[f1360,f1214,f161,f1376])).

fof(f1360,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_204 ),
    inference(unit_resulting_resolution,[],[f162,f1215,f131])).

fof(f1352,plain,
    ( ~ spl13_213
    | spl13_209 ),
    inference(avatar_split_clause,[],[f1329,f1297,f1350])).

fof(f1329,plain,
    ( ~ r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_209 ),
    inference(unit_resulting_resolution,[],[f1298,f121])).

fof(f1339,plain,
    ( ~ spl13_211
    | spl13_209 ),
    inference(avatar_split_clause,[],[f1327,f1297,f1337])).

fof(f1337,plain,
    ( spl13_211
  <=> ~ r1_tarski(sK4(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_211])])).

fof(f1327,plain,
    ( ~ r1_tarski(sK4(sK1),o_0_0_xboole_0)
    | ~ spl13_209 ),
    inference(unit_resulting_resolution,[],[f1298,f126])).

fof(f1302,plain,
    ( spl13_208
    | ~ spl13_72
    | ~ spl13_198 ),
    inference(avatar_split_clause,[],[f1217,f1158,f437,f1300])).

fof(f1217,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_72
    | ~ spl13_198 ),
    inference(backward_demodulation,[],[f1159,f438])).

fof(f1294,plain,
    ( ~ spl13_207
    | ~ spl13_198
    | spl13_203 ),
    inference(avatar_split_clause,[],[f1260,f1192,f1158,f1292])).

fof(f1260,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK10(o_0_0_xboole_0))
    | ~ spl13_198
    | ~ spl13_203 ),
    inference(backward_demodulation,[],[f1159,f1193])).

fof(f1216,plain,
    ( spl13_204
    | ~ spl13_6
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1175,f1155,f161,f1214])).

fof(f1175,plain,
    ( r2_hidden(sK10(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f119,f1156,f432])).

fof(f1194,plain,
    ( ~ spl13_203
    | ~ spl13_6
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1174,f1155,f161,f1192])).

fof(f1174,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK10(u1_struct_0(sK1)))
    | ~ spl13_6
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f119,f1156,f838])).

fof(f1185,plain,
    ( ~ spl13_201
    | ~ spl13_6
    | spl13_199 ),
    inference(avatar_split_clause,[],[f1178,f1155,f161,f1183])).

fof(f1178,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_6
    | ~ spl13_199 ),
    inference(unit_resulting_resolution,[],[f162,f1156,f127])).

fof(f1160,plain,
    ( spl13_198
    | ~ spl13_6
    | ~ spl13_166
    | spl13_169 ),
    inference(avatar_split_clause,[],[f1104,f926,f903,f161,f1158])).

fof(f926,plain,
    ( spl13_169
  <=> ~ r2_hidden(sK9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_169])])).

fof(f1104,plain,
    ( u1_struct_0(sK1) = o_0_0_xboole_0
    | ~ spl13_6
    | ~ spl13_166
    | ~ spl13_169 ),
    inference(unit_resulting_resolution,[],[f927,f904,f432])).

fof(f927,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_169 ),
    inference(avatar_component_clause,[],[f926])).

fof(f1090,plain,
    ( spl13_196
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f685,f294,f182,f154,f147,f140,f1088])).

fof(f685,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f119,f110])).

fof(f1083,plain,
    ( spl13_194
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f822,f811,f182,f154,f147,f140,f1081])).

fof(f822,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_148 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f812,f129])).

fof(f1076,plain,
    ( spl13_192
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f533,f332,f254,f1074])).

fof(f1074,plain,
    ( spl13_192
  <=> v1_funct_2(u1_waybel_0(sK1,sK5(sK1)),u1_struct_0(sK5(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_192])])).

fof(f254,plain,
    ( spl13_28
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f332,plain,
    ( spl13_48
  <=> l1_waybel_0(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f533,plain,
    ( v1_funct_2(u1_waybel_0(sK1,sK5(sK1)),u1_struct_0(sK5(sK1)),u1_struct_0(sK1))
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(unit_resulting_resolution,[],[f255,f333,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f333,plain,
    ( l1_waybel_0(sK5(sK1),sK1)
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f332])).

fof(f255,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f1069,plain,
    ( spl13_190
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f537,f234,f197,f1067])).

fof(f1067,plain,
    ( spl13_190
  <=> v1_funct_2(u1_waybel_0(sK11,sK5(sK11)),u1_struct_0(sK5(sK11)),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_190])])).

fof(f197,plain,
    ( spl13_16
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f234,plain,
    ( spl13_24
  <=> l1_waybel_0(sK5(sK11),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f537,plain,
    ( v1_funct_2(u1_waybel_0(sK11,sK5(sK11)),u1_struct_0(sK5(sK11)),u1_struct_0(sK11))
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f198,f235,f124])).

fof(f235,plain,
    ( l1_waybel_0(sK5(sK11),sK11)
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f234])).

fof(f198,plain,
    ( l1_struct_0(sK11)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1059,plain,
    ( spl13_188
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f538,f227,f175,f1057])).

fof(f1057,plain,
    ( spl13_188
  <=> v1_funct_2(u1_waybel_0(sK12,sK5(sK12)),u1_struct_0(sK5(sK12)),u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_188])])).

fof(f538,plain,
    ( v1_funct_2(u1_waybel_0(sK12,sK5(sK12)),u1_struct_0(sK5(sK12)),u1_struct_0(sK12))
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f176,f228,f124])).

fof(f1052,plain,
    ( spl13_186
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f620,f596,f182,f154,f147,f140,f1050])).

fof(f1050,plain,
    ( spl13_186
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_186])])).

fof(f620,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f597,f129])).

fof(f1045,plain,
    ( spl13_184
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f532,f220,f147,f1043])).

fof(f1043,plain,
    ( spl13_184
  <=> v1_funct_2(u1_waybel_0(sK0,sK5(sK0)),u1_struct_0(sK5(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_184])])).

fof(f532,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK5(sK0)),u1_struct_0(sK5(sK0)),u1_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f148,f221,f124])).

fof(f1014,plain,
    ( ~ spl13_183
    | spl13_173 ),
    inference(avatar_split_clause,[],[f961,f944,f1012])).

fof(f1012,plain,
    ( spl13_183
  <=> ~ r2_hidden(sK9(sK0,sK1,sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_183])])).

fof(f944,plain,
    ( spl13_173
  <=> ~ m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_173])])).

fof(f961,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK3),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_173 ),
    inference(unit_resulting_resolution,[],[f119,f945,f130])).

fof(f945,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_173 ),
    inference(avatar_component_clause,[],[f944])).

fof(f1007,plain,
    ( ~ spl13_181
    | spl13_167 ),
    inference(avatar_split_clause,[],[f917,f900,f1005])).

fof(f1005,plain,
    ( spl13_181
  <=> ~ r2_hidden(sK9(sK0,sK1,sK2),sK10(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_181])])).

fof(f900,plain,
    ( spl13_167
  <=> ~ m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_167])])).

fof(f917,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),sK10(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl13_167 ),
    inference(unit_resulting_resolution,[],[f119,f901,f130])).

fof(f901,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_167 ),
    inference(avatar_component_clause,[],[f900])).

fof(f987,plain,
    ( ~ spl13_179
    | ~ spl13_72
    | spl13_173 ),
    inference(avatar_split_clause,[],[f960,f944,f437,f985])).

fof(f960,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK3),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_173 ),
    inference(unit_resulting_resolution,[],[f438,f945,f130])).

fof(f980,plain,
    ( ~ spl13_177
    | ~ spl13_72
    | spl13_167 ),
    inference(avatar_split_clause,[],[f916,f900,f437,f978])).

fof(f916,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),sK4(sK1))
    | ~ spl13_72
    | ~ spl13_167 ),
    inference(unit_resulting_resolution,[],[f438,f901,f130])).

fof(f972,plain,
    ( ~ spl13_175
    | spl13_173 ),
    inference(avatar_split_clause,[],[f962,f944,f970])).

fof(f970,plain,
    ( spl13_175
  <=> ~ r2_hidden(sK9(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_175])])).

fof(f962,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_173 ),
    inference(unit_resulting_resolution,[],[f945,f121])).

fof(f949,plain,
    ( spl13_172
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f937,f336,f182,f154,f147,f140,f947])).

fof(f947,plain,
    ( spl13_172
  <=> m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_172])])).

fof(f336,plain,
    ( spl13_50
  <=> r1_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f937,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f337,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f337,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f336])).

fof(f936,plain,
    ( spl13_170
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_51 ),
    inference(avatar_split_clause,[],[f710,f339,f182,f154,f147,f140,f934])).

fof(f710,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f340,f119,f116])).

fof(f928,plain,
    ( ~ spl13_169
    | spl13_167 ),
    inference(avatar_split_clause,[],[f918,f900,f926])).

fof(f918,plain,
    ( ~ r2_hidden(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_167 ),
    inference(unit_resulting_resolution,[],[f901,f121])).

fof(f905,plain,
    ( spl13_166
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f893,f288,f182,f154,f147,f140,f903])).

fof(f893,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_36 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f289,f114])).

fof(f892,plain,
    ( spl13_164
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_37 ),
    inference(avatar_split_clause,[],[f709,f285,f182,f154,f147,f140,f890])).

fof(f709,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_37 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f286,f119,f116])).

fof(f885,plain,
    ( spl13_162
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f658,f294,f182,f154,f147,f140,f883])).

fof(f658,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2,sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_38 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f295,f119,f109])).

fof(f878,plain,
    ( spl13_160
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f555,f182,f147,f876])).

fof(f555,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f148,f183,f125])).

fof(f871,plain,
    ( spl13_158
    | ~ spl13_100
    | ~ spl13_140 ),
    inference(avatar_split_clause,[],[f770,f766,f588,f869])).

fof(f869,plain,
    ( spl13_158
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK1)),sK5(sK5(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_158])])).

fof(f588,plain,
    ( spl13_100
  <=> l1_struct_0(sK5(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f766,plain,
    ( spl13_140
  <=> l1_waybel_0(sK5(sK5(sK5(sK1))),sK5(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f770,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK1)),sK5(sK5(sK5(sK1)))))
    | ~ spl13_100
    | ~ spl13_140 ),
    inference(unit_resulting_resolution,[],[f589,f767,f123])).

fof(f767,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK1))),sK5(sK5(sK1)))
    | ~ spl13_140 ),
    inference(avatar_component_clause,[],[f766])).

fof(f589,plain,
    ( l1_struct_0(sK5(sK5(sK1)))
    | ~ spl13_100 ),
    inference(avatar_component_clause,[],[f588])).

fof(f864,plain,
    ( spl13_156
    | ~ spl13_80
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f740,f732,f476,f862])).

fof(f862,plain,
    ( spl13_156
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK11)),sK5(sK5(sK5(sK11))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_156])])).

fof(f476,plain,
    ( spl13_80
  <=> l1_struct_0(sK5(sK5(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f732,plain,
    ( spl13_134
  <=> l1_waybel_0(sK5(sK5(sK5(sK11))),sK5(sK5(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f740,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK11)),sK5(sK5(sK5(sK11)))))
    | ~ spl13_80
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f477,f733,f123])).

fof(f733,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK11))),sK5(sK5(sK11)))
    | ~ spl13_134 ),
    inference(avatar_component_clause,[],[f732])).

fof(f477,plain,
    ( l1_struct_0(sK5(sK5(sK11)))
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f476])).

fof(f857,plain,
    ( spl13_154
    | ~ spl13_68
    | ~ spl13_128 ),
    inference(avatar_split_clause,[],[f704,f700,f419,f855])).

fof(f855,plain,
    ( spl13_154
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK12)),sK5(sK5(sK5(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f419,plain,
    ( spl13_68
  <=> l1_struct_0(sK5(sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f700,plain,
    ( spl13_128
  <=> l1_waybel_0(sK5(sK5(sK5(sK12))),sK5(sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f704,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK12)),sK5(sK5(sK5(sK12)))))
    | ~ spl13_68
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f420,f701,f123])).

fof(f701,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK12))),sK5(sK5(sK12)))
    | ~ spl13_128 ),
    inference(avatar_component_clause,[],[f700])).

fof(f420,plain,
    ( l1_struct_0(sK5(sK5(sK12)))
    | ~ spl13_68 ),
    inference(avatar_component_clause,[],[f419])).

fof(f849,plain,
    ( spl13_152
    | ~ spl13_62
    | ~ spl13_122 ),
    inference(avatar_split_clause,[],[f674,f670,f387,f847])).

fof(f847,plain,
    ( spl13_152
  <=> v1_funct_1(u1_waybel_0(sK5(sK5(sK0)),sK5(sK5(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f387,plain,
    ( spl13_62
  <=> l1_struct_0(sK5(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_62])])).

fof(f670,plain,
    ( spl13_122
  <=> l1_waybel_0(sK5(sK5(sK5(sK0))),sK5(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f674,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK5(sK0)),sK5(sK5(sK5(sK0)))))
    | ~ spl13_62
    | ~ spl13_122 ),
    inference(unit_resulting_resolution,[],[f388,f671,f123])).

fof(f671,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK0))),sK5(sK5(sK0)))
    | ~ spl13_122 ),
    inference(avatar_component_clause,[],[f670])).

fof(f388,plain,
    ( l1_struct_0(sK5(sK5(sK0)))
    | ~ spl13_62 ),
    inference(avatar_component_clause,[],[f387])).

fof(f835,plain,
    ( spl13_150
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f621,f182,f154,f147,f140,f833])).

fof(f621,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f129])).

fof(f813,plain,
    ( spl13_148
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_147 ),
    inference(avatar_split_clause,[],[f805,f802,f182,f154,f147,f140,f811])).

fof(f802,plain,
    ( spl13_147
  <=> ~ r2_waybel_0(sK0,sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_147])])).

fof(f805,plain,
    ( m1_subset_1(sK6(sK0,sK1,o_0_0_xboole_0),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_147 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f803,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f803,plain,
    ( ~ r2_waybel_0(sK0,sK1,o_0_0_xboole_0)
    | ~ spl13_147 ),
    inference(avatar_component_clause,[],[f802])).

fof(f804,plain,
    ( ~ spl13_147
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f792,f182,f161,f154,f147,f140,f802])).

fof(f792,plain,
    ( ~ r2_waybel_0(sK0,sK1,o_0_0_xboole_0)
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_6
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f119,f210,f111])).

fof(f788,plain,
    ( spl13_144
    | ~ spl13_142 ),
    inference(avatar_split_clause,[],[f781,f777,f786])).

fof(f777,plain,
    ( spl13_142
  <=> l1_orders_2(sK5(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_142])])).

fof(f781,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK1))))
    | ~ spl13_142 ),
    inference(unit_resulting_resolution,[],[f778,f102])).

fof(f778,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK1))))
    | ~ spl13_142 ),
    inference(avatar_component_clause,[],[f777])).

fof(f779,plain,
    ( spl13_142
    | ~ spl13_100
    | ~ spl13_140 ),
    inference(avatar_split_clause,[],[f769,f766,f588,f777])).

fof(f769,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK1))))
    | ~ spl13_100
    | ~ spl13_140 ),
    inference(unit_resulting_resolution,[],[f589,f767,f106])).

fof(f768,plain,
    ( spl13_140
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f591,f588,f766])).

fof(f591,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK1))),sK5(sK5(sK1)))
    | ~ spl13_100 ),
    inference(unit_resulting_resolution,[],[f589,f107])).

fof(f758,plain,
    ( spl13_138
    | ~ spl13_136 ),
    inference(avatar_split_clause,[],[f751,f747,f756])).

fof(f747,plain,
    ( spl13_136
  <=> l1_orders_2(sK5(sK5(sK5(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_136])])).

fof(f751,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK11))))
    | ~ spl13_136 ),
    inference(unit_resulting_resolution,[],[f748,f102])).

fof(f748,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK11))))
    | ~ spl13_136 ),
    inference(avatar_component_clause,[],[f747])).

fof(f749,plain,
    ( spl13_136
    | ~ spl13_80
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f739,f732,f476,f747])).

fof(f739,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK11))))
    | ~ spl13_80
    | ~ spl13_134 ),
    inference(unit_resulting_resolution,[],[f477,f733,f106])).

fof(f734,plain,
    ( spl13_134
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f480,f476,f732])).

fof(f480,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK11))),sK5(sK5(sK11)))
    | ~ spl13_80 ),
    inference(unit_resulting_resolution,[],[f477,f107])).

fof(f726,plain,
    ( spl13_132
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f719,f715,f724])).

fof(f715,plain,
    ( spl13_130
  <=> l1_orders_2(sK5(sK5(sK5(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f719,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK12))))
    | ~ spl13_130 ),
    inference(unit_resulting_resolution,[],[f716,f102])).

fof(f716,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK12))))
    | ~ spl13_130 ),
    inference(avatar_component_clause,[],[f715])).

fof(f717,plain,
    ( spl13_130
    | ~ spl13_68
    | ~ spl13_128 ),
    inference(avatar_split_clause,[],[f703,f700,f419,f715])).

fof(f703,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK12))))
    | ~ spl13_68
    | ~ spl13_128 ),
    inference(unit_resulting_resolution,[],[f420,f701,f106])).

fof(f702,plain,
    ( spl13_128
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f422,f419,f700])).

fof(f422,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK12))),sK5(sK5(sK12)))
    | ~ spl13_68 ),
    inference(unit_resulting_resolution,[],[f420,f107])).

fof(f694,plain,
    ( spl13_126
    | ~ spl13_124 ),
    inference(avatar_split_clause,[],[f687,f681,f692])).

fof(f681,plain,
    ( spl13_124
  <=> l1_orders_2(sK5(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f687,plain,
    ( l1_struct_0(sK5(sK5(sK5(sK0))))
    | ~ spl13_124 ),
    inference(unit_resulting_resolution,[],[f682,f102])).

fof(f682,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK0))))
    | ~ spl13_124 ),
    inference(avatar_component_clause,[],[f681])).

fof(f683,plain,
    ( spl13_124
    | ~ spl13_62
    | ~ spl13_122 ),
    inference(avatar_split_clause,[],[f673,f670,f387,f681])).

fof(f673,plain,
    ( l1_orders_2(sK5(sK5(sK5(sK0))))
    | ~ spl13_62
    | ~ spl13_122 ),
    inference(unit_resulting_resolution,[],[f388,f671,f106])).

fof(f672,plain,
    ( spl13_122
    | ~ spl13_62 ),
    inference(avatar_split_clause,[],[f390,f387,f670])).

fof(f390,plain,
    ( l1_waybel_0(sK5(sK5(sK5(sK0))),sK5(sK5(sK0)))
    | ~ spl13_62 ),
    inference(unit_resulting_resolution,[],[f388,f107])).

fof(f665,plain,
    ( spl13_120
    | ~ spl13_52 ),
    inference(avatar_split_clause,[],[f402,f347,f663])).

fof(f663,plain,
    ( spl13_120
  <=> m1_subset_1(sK4(sK5(sK1)),k1_zfmisc_1(u1_struct_0(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f347,plain,
    ( spl13_52
  <=> l1_orders_2(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f402,plain,
    ( m1_subset_1(sK4(sK5(sK1)),k1_zfmisc_1(u1_struct_0(sK5(sK1))))
    | ~ spl13_52 ),
    inference(unit_resulting_resolution,[],[f348,f103])).

fof(f348,plain,
    ( l1_orders_2(sK5(sK1))
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f347])).

fof(f656,plain,
    ( spl13_118
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f404,f301,f654])).

fof(f654,plain,
    ( spl13_118
  <=> m1_subset_1(sK4(sK5(sK11)),k1_zfmisc_1(u1_struct_0(sK5(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f301,plain,
    ( spl13_40
  <=> l1_orders_2(sK5(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f404,plain,
    ( m1_subset_1(sK4(sK5(sK11)),k1_zfmisc_1(u1_struct_0(sK5(sK11))))
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f302,f103])).

fof(f302,plain,
    ( l1_orders_2(sK5(sK11))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f301])).

fof(f649,plain,
    ( spl13_116
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f405,f272,f647])).

fof(f647,plain,
    ( spl13_116
  <=> m1_subset_1(sK4(sK5(sK12)),k1_zfmisc_1(u1_struct_0(sK5(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f272,plain,
    ( spl13_32
  <=> l1_orders_2(sK5(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f405,plain,
    ( m1_subset_1(sK4(sK5(sK12)),k1_zfmisc_1(u1_struct_0(sK5(sK12))))
    | ~ spl13_32 ),
    inference(unit_resulting_resolution,[],[f273,f103])).

fof(f273,plain,
    ( l1_orders_2(sK5(sK12))
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f642,plain,
    ( spl13_114
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f401,f262,f640])).

fof(f640,plain,
    ( spl13_114
  <=> m1_subset_1(sK4(sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f262,plain,
    ( spl13_30
  <=> l1_orders_2(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f401,plain,
    ( m1_subset_1(sK4(sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK5(sK0))))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f263,f103])).

fof(f263,plain,
    ( l1_orders_2(sK5(sK0))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f262])).

fof(f635,plain,
    ( spl13_112
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f531,f182,f147,f633])).

fof(f531,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f148,f183,f124])).

fof(f628,plain,
    ( spl13_110
    | ~ spl13_54
    | ~ spl13_96 ),
    inference(avatar_split_clause,[],[f572,f567,f355,f626])).

fof(f626,plain,
    ( spl13_110
  <=> v1_funct_1(u1_waybel_0(sK5(sK1),sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f355,plain,
    ( spl13_54
  <=> l1_struct_0(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f567,plain,
    ( spl13_96
  <=> l1_waybel_0(sK5(sK5(sK1)),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f572,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK1),sK5(sK5(sK1))))
    | ~ spl13_54
    | ~ spl13_96 ),
    inference(unit_resulting_resolution,[],[f356,f568,f123])).

fof(f568,plain,
    ( l1_waybel_0(sK5(sK5(sK1)),sK5(sK1))
    | ~ spl13_96 ),
    inference(avatar_component_clause,[],[f567])).

fof(f356,plain,
    ( l1_struct_0(sK5(sK1))
    | ~ spl13_54 ),
    inference(avatar_component_clause,[],[f355])).

fof(f619,plain,
    ( spl13_108
    | ~ spl13_44
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f453,f444,f317,f617])).

fof(f617,plain,
    ( spl13_108
  <=> v1_funct_1(u1_waybel_0(sK5(sK11),sK5(sK5(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f317,plain,
    ( spl13_44
  <=> l1_struct_0(sK5(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f444,plain,
    ( spl13_74
  <=> l1_waybel_0(sK5(sK5(sK11)),sK5(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f453,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK11),sK5(sK5(sK11))))
    | ~ spl13_44
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f318,f445,f123])).

fof(f445,plain,
    ( l1_waybel_0(sK5(sK5(sK11)),sK5(sK11))
    | ~ spl13_74 ),
    inference(avatar_component_clause,[],[f444])).

fof(f318,plain,
    ( l1_struct_0(sK5(sK11))
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f317])).

fof(f612,plain,
    ( spl13_106
    | ~ spl13_42
    | ~ spl13_64 ),
    inference(avatar_split_clause,[],[f452,f395,f308,f610])).

fof(f610,plain,
    ( spl13_106
  <=> v1_funct_1(u1_waybel_0(sK5(sK12),sK5(sK5(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f308,plain,
    ( spl13_42
  <=> l1_struct_0(sK5(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f395,plain,
    ( spl13_64
  <=> l1_waybel_0(sK5(sK5(sK12)),sK5(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f452,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK12),sK5(sK5(sK12))))
    | ~ spl13_42
    | ~ spl13_64 ),
    inference(unit_resulting_resolution,[],[f309,f396,f123])).

fof(f396,plain,
    ( l1_waybel_0(sK5(sK5(sK12)),sK5(sK12))
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f395])).

fof(f309,plain,
    ( l1_struct_0(sK5(sK12))
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f308])).

fof(f605,plain,
    ( spl13_104
    | ~ spl13_34
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f451,f370,f280,f603])).

fof(f603,plain,
    ( spl13_104
  <=> v1_funct_1(u1_waybel_0(sK5(sK0),sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f280,plain,
    ( spl13_34
  <=> l1_struct_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f370,plain,
    ( spl13_58
  <=> l1_waybel_0(sK5(sK5(sK0)),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f451,plain,
    ( v1_funct_1(u1_waybel_0(sK5(sK0),sK5(sK5(sK0))))
    | ~ spl13_34
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f281,f371,f123])).

fof(f371,plain,
    ( l1_waybel_0(sK5(sK5(sK0)),sK5(sK0))
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f370])).

fof(f281,plain,
    ( l1_struct_0(sK5(sK0))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f280])).

fof(f598,plain,
    ( spl13_102
    | spl13_1
    | ~ spl13_2
    | spl13_5
    | ~ spl13_12
    | spl13_57 ),
    inference(avatar_split_clause,[],[f583,f362,f182,f154,f147,f140,f596])).

fof(f583,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_5
    | ~ spl13_12
    | ~ spl13_57 ),
    inference(unit_resulting_resolution,[],[f141,f148,f155,f183,f363,f112])).

fof(f590,plain,
    ( spl13_100
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f582,f578,f588])).

fof(f582,plain,
    ( l1_struct_0(sK5(sK5(sK1)))
    | ~ spl13_98 ),
    inference(unit_resulting_resolution,[],[f579,f102])).

fof(f580,plain,
    ( spl13_98
    | ~ spl13_54
    | ~ spl13_96 ),
    inference(avatar_split_clause,[],[f573,f567,f355,f578])).

fof(f573,plain,
    ( l1_orders_2(sK5(sK5(sK1)))
    | ~ spl13_54
    | ~ spl13_96 ),
    inference(unit_resulting_resolution,[],[f356,f568,f106])).

fof(f569,plain,
    ( spl13_96
    | ~ spl13_54 ),
    inference(avatar_split_clause,[],[f365,f355,f567])).

fof(f365,plain,
    ( l1_waybel_0(sK5(sK5(sK1)),sK5(sK1))
    | ~ spl13_54 ),
    inference(unit_resulting_resolution,[],[f356,f107])).

fof(f554,plain,
    ( spl13_94
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f450,f332,f254,f552])).

fof(f552,plain,
    ( spl13_94
  <=> v1_funct_1(u1_waybel_0(sK1,sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f450,plain,
    ( v1_funct_1(u1_waybel_0(sK1,sK5(sK1)))
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(unit_resulting_resolution,[],[f255,f333,f123])).

fof(f546,plain,
    ( spl13_92
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f539,f528,f544])).

fof(f539,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_90 ),
    inference(superposition,[],[f119,f529])).

fof(f530,plain,
    ( spl13_90
    | ~ spl13_6
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f494,f486,f161,f528])).

fof(f486,plain,
    ( spl13_82
  <=> v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f494,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl13_6
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f487,f202])).

fof(f487,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f486])).

fof(f523,plain,
    ( spl13_88
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f454,f234,f197,f521])).

fof(f521,plain,
    ( spl13_88
  <=> v1_funct_1(u1_waybel_0(sK11,sK5(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f454,plain,
    ( v1_funct_1(u1_waybel_0(sK11,sK5(sK11)))
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f198,f235,f123])).

fof(f516,plain,
    ( spl13_86
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f455,f227,f175,f514])).

fof(f514,plain,
    ( spl13_86
  <=> v1_funct_1(u1_waybel_0(sK12,sK5(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f455,plain,
    ( v1_funct_1(u1_waybel_0(sK12,sK5(sK12)))
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f176,f228,f123])).

fof(f509,plain,
    ( spl13_84
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f449,f220,f147,f507])).

fof(f507,plain,
    ( spl13_84
  <=> v1_funct_1(u1_waybel_0(sK0,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f449,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK5(sK0)))
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f148,f221,f123])).

fof(f488,plain,
    ( spl13_82
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f481,f161,f486])).

fof(f481,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f119,f479,f122])).

fof(f479,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f162,f119,f131])).

fof(f478,plain,
    ( spl13_80
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f471,f467,f476])).

fof(f471,plain,
    ( l1_struct_0(sK5(sK5(sK11)))
    | ~ spl13_78 ),
    inference(unit_resulting_resolution,[],[f468,f102])).

fof(f469,plain,
    ( spl13_78
    | ~ spl13_44
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f447,f444,f317,f467])).

fof(f447,plain,
    ( l1_orders_2(sK5(sK5(sK11)))
    | ~ spl13_44
    | ~ spl13_74 ),
    inference(unit_resulting_resolution,[],[f318,f445,f106])).

fof(f462,plain,
    ( spl13_76
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f448,f182,f147,f460])).

fof(f448,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f148,f183,f123])).

fof(f446,plain,
    ( spl13_74
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f320,f317,f444])).

fof(f320,plain,
    ( l1_waybel_0(sK5(sK5(sK11)),sK5(sK11))
    | ~ spl13_44 ),
    inference(unit_resulting_resolution,[],[f318,f107])).

fof(f439,plain,
    ( spl13_72
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f400,f246,f437])).

fof(f246,plain,
    ( spl13_26
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f400,plain,
    ( m1_subset_1(sK4(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f247,f103])).

fof(f247,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f429,plain,
    ( spl13_70
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f399,f168,f427])).

fof(f427,plain,
    ( spl13_70
  <=> m1_subset_1(sK4(sK11),k1_zfmisc_1(u1_struct_0(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f168,plain,
    ( spl13_8
  <=> l1_orders_2(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f399,plain,
    ( m1_subset_1(sK4(sK11),k1_zfmisc_1(u1_struct_0(sK11)))
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f169,f103])).

fof(f169,plain,
    ( l1_orders_2(sK11)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f421,plain,
    ( spl13_68
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f414,f410,f419])).

fof(f414,plain,
    ( l1_struct_0(sK5(sK5(sK12)))
    | ~ spl13_66 ),
    inference(unit_resulting_resolution,[],[f411,f102])).

fof(f412,plain,
    ( spl13_66
    | ~ spl13_42
    | ~ spl13_64 ),
    inference(avatar_split_clause,[],[f398,f395,f308,f410])).

fof(f398,plain,
    ( l1_orders_2(sK5(sK5(sK12)))
    | ~ spl13_42
    | ~ spl13_64 ),
    inference(unit_resulting_resolution,[],[f309,f396,f106])).

fof(f397,plain,
    ( spl13_64
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f312,f308,f395])).

fof(f312,plain,
    ( l1_waybel_0(sK5(sK5(sK12)),sK5(sK12))
    | ~ spl13_42 ),
    inference(unit_resulting_resolution,[],[f309,f107])).

fof(f389,plain,
    ( spl13_62
    | ~ spl13_60 ),
    inference(avatar_split_clause,[],[f382,f378,f387])).

fof(f382,plain,
    ( l1_struct_0(sK5(sK5(sK0)))
    | ~ spl13_60 ),
    inference(unit_resulting_resolution,[],[f379,f102])).

fof(f381,plain,
    ( ~ spl13_51
    | ~ spl13_57 ),
    inference(avatar_split_clause,[],[f100,f362,f339])).

fof(f100,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | ~ r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( ( ~ r2_waybel_0(sK0,sK1,sK3)
        & r2_waybel_0(sK0,sK1,sK2) )
      | ( ~ r1_waybel_0(sK0,sK1,sK3)
        & r1_waybel_0(sK0,sK1,sK2) ) )
    & r1_tarski(sK2,sK3)
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f70,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ( ( ~ r2_waybel_0(X0,X1,X3)
                    & r2_waybel_0(X0,X1,X2) )
                  | ( ~ r1_waybel_0(X0,X1,X3)
                    & r1_waybel_0(X0,X1,X2) ) )
                & r1_tarski(X2,X3) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ( ( ~ r2_waybel_0(sK0,X1,X3)
                  & r2_waybel_0(sK0,X1,X2) )
                | ( ~ r1_waybel_0(sK0,X1,X3)
                  & r1_waybel_0(sK0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X3,X2] :
            ( ( ( ~ r2_waybel_0(X0,sK1,X3)
                & r2_waybel_0(X0,sK1,X2) )
              | ( ~ r1_waybel_0(X0,sK1,X3)
                & r1_waybel_0(X0,sK1,X2) ) )
            & r1_tarski(X2,X3) )
        & l1_waybel_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ( ( ~ r2_waybel_0(X0,X1,X3)
              & r2_waybel_0(X0,X1,X2) )
            | ( ~ r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) ) )
          & r1_tarski(X2,X3) )
     => ( ( ( ~ r2_waybel_0(X0,X1,sK3)
            & r2_waybel_0(X0,X1,sK2) )
          | ( ~ r1_waybel_0(X0,X1,sK3)
            & r1_waybel_0(X0,X1,sK2) ) )
        & r1_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( r1_tarski(X2,X3)
               => ( ( r2_waybel_0(X0,X1,X2)
                   => r2_waybel_0(X0,X1,X3) )
                  & ( r1_waybel_0(X0,X1,X2)
                   => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',t8_waybel_0)).

fof(f380,plain,
    ( spl13_60
    | ~ spl13_34
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f373,f370,f280,f378])).

fof(f373,plain,
    ( l1_orders_2(sK5(sK5(sK0)))
    | ~ spl13_34
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f281,f371,f106])).

fof(f372,plain,
    ( spl13_58
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f283,f280,f370])).

fof(f283,plain,
    ( l1_waybel_0(sK5(sK5(sK0)),sK5(sK0))
    | ~ spl13_34 ),
    inference(unit_resulting_resolution,[],[f281,f107])).

fof(f364,plain,
    ( spl13_36
    | ~ spl13_57 ),
    inference(avatar_split_clause,[],[f99,f362,f288])).

fof(f99,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f357,plain,
    ( spl13_54
    | ~ spl13_52 ),
    inference(avatar_split_clause,[],[f350,f347,f355])).

fof(f350,plain,
    ( l1_struct_0(sK5(sK1))
    | ~ spl13_52 ),
    inference(unit_resulting_resolution,[],[f348,f102])).

fof(f349,plain,
    ( spl13_52
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f342,f332,f254,f347])).

fof(f342,plain,
    ( l1_orders_2(sK5(sK1))
    | ~ spl13_28
    | ~ spl13_48 ),
    inference(unit_resulting_resolution,[],[f255,f333,f106])).

fof(f341,plain,
    ( ~ spl13_51
    | spl13_38 ),
    inference(avatar_split_clause,[],[f98,f294,f339])).

fof(f98,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f334,plain,
    ( spl13_48
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f257,f254,f332])).

fof(f257,plain,
    ( l1_waybel_0(sK5(sK1),sK1)
    | ~ spl13_28 ),
    inference(unit_resulting_resolution,[],[f255,f107])).

fof(f327,plain,
    ( spl13_46
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f241,f189,f325])).

fof(f189,plain,
    ( spl13_14
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl13_14 ),
    inference(unit_resulting_resolution,[],[f190,f126])).

fof(f190,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f319,plain,
    ( spl13_44
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f311,f301,f317])).

fof(f311,plain,
    ( l1_struct_0(sK5(sK11))
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f302,f102])).

fof(f310,plain,
    ( spl13_42
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f275,f272,f308])).

fof(f275,plain,
    ( l1_struct_0(sK5(sK12))
    | ~ spl13_32 ),
    inference(unit_resulting_resolution,[],[f273,f102])).

fof(f303,plain,
    ( spl13_40
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f240,f234,f197,f301])).

fof(f240,plain,
    ( l1_orders_2(sK5(sK11))
    | ~ spl13_16
    | ~ spl13_24 ),
    inference(unit_resulting_resolution,[],[f198,f235,f106])).

fof(f296,plain,
    ( spl13_36
    | spl13_38 ),
    inference(avatar_split_clause,[],[f97,f294,f288])).

fof(f97,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f282,plain,
    ( spl13_34
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f267,f262,f280])).

fof(f267,plain,
    ( l1_struct_0(sK5(sK0))
    | ~ spl13_30 ),
    inference(unit_resulting_resolution,[],[f263,f102])).

fof(f274,plain,
    ( spl13_32
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f239,f227,f175,f272])).

fof(f239,plain,
    ( l1_orders_2(sK5(sK12))
    | ~ spl13_10
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f176,f228,f106])).

fof(f264,plain,
    ( spl13_30
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f238,f220,f147,f262])).

fof(f238,plain,
    ( l1_orders_2(sK5(sK0))
    | ~ spl13_2
    | ~ spl13_20 ),
    inference(unit_resulting_resolution,[],[f148,f221,f106])).

fof(f256,plain,
    ( spl13_28
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f249,f246,f254])).

fof(f249,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_26 ),
    inference(unit_resulting_resolution,[],[f247,f102])).

fof(f248,plain,
    ( spl13_26
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f237,f182,f147,f246])).

fof(f237,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_2
    | ~ spl13_12 ),
    inference(unit_resulting_resolution,[],[f148,f183,f106])).

fof(f236,plain,
    ( spl13_24
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f215,f197,f234])).

fof(f215,plain,
    ( l1_waybel_0(sK5(sK11),sK11)
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f198,f107])).

fof(f229,plain,
    ( spl13_22
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f214,f175,f227])).

fof(f214,plain,
    ( l1_waybel_0(sK5(sK12),sK12)
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f176,f107])).

fof(f222,plain,
    ( spl13_20
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f213,f147,f220])).

fof(f213,plain,
    ( l1_waybel_0(sK5(sK0),sK0)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f148,f107])).

fof(f209,plain,
    ( spl13_18
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f200,f161,f207])).

fof(f207,plain,
    ( spl13_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f199,plain,
    ( spl13_16
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f192,f168,f197])).

fof(f192,plain,
    ( l1_struct_0(sK11)
    | ~ spl13_8 ),
    inference(unit_resulting_resolution,[],[f169,f102])).

fof(f191,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f96,f189])).

fof(f96,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f71])).

fof(f184,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f95,f182])).

fof(f95,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f177,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f135,f175])).

fof(f135,plain,(
    l1_struct_0(sK12) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    l1_struct_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f21,f90])).

fof(f90,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK12) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',existence_l1_struct_0)).

fof(f170,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f134,f168])).

fof(f134,plain,(
    l1_orders_2(sK11) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    l1_orders_2(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f20,f88])).

fof(f88,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK11) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',existence_l1_orders_2)).

fof(f163,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f101,f161])).

fof(f101,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t8_waybel_0.p',dt_o_0_0_xboole_0)).

fof(f156,plain,(
    ~ spl13_5 ),
    inference(avatar_split_clause,[],[f94,f154])).

fof(f94,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f149,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f93,f147])).

fof(f93,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f142,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f92,f140])).

fof(f92,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------

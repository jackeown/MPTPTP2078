%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t50_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:09 EDT 2019

% Result     : Theorem 1.85s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       : 3084 (19560 expanded)
%              Number of leaves         :  383 (7310 expanded)
%              Depth                    :   15
%              Number of atoms          : 10485 (62518 expanded)
%              Number of equality atoms : 3213 (45250 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f100,f104,f108,f112,f120,f124,f125,f126,f131,f148,f152,f156,f160,f164,f165,f166,f170,f174,f175,f176,f177,f181,f213,f217,f221,f225,f229,f233,f237,f241,f245,f249,f250,f251,f252,f256,f260,f264,f268,f272,f276,f277,f278,f279,f280,f284,f288,f289,f293,f297,f305,f309,f313,f317,f322,f327,f332,f337,f342,f360,f367,f385,f392,f400,f401,f419,f426,f444,f451,f469,f476,f494,f501,f519,f526,f534,f535,f553,f560,f578,f585,f603,f610,f628,f635,f653,f660,f668,f669,f687,f694,f712,f719,f737,f744,f762,f769,f787,f794,f812,f819,f837,f844,f862,f869,f887,f894,f912,f919,f937,f944,f962,f969,f987,f994,f1012,f1019,f1037,f1044,f1062,f1069,f1077,f1078,f1086,f1087,f1095,f1096,f1103,f1107,f1111,f1172,f1174,f1176,f1178,f1180,f1182,f1184,f1196,f1210,f1214,f1222,f1223,f1228,f1229,f1296,f1297,f1298,f1300,f1302,f1304,f1306,f1370,f1371,f1372,f1374,f1376,f1378,f1380,f1444,f1445,f1446,f1448,f1450,f1452,f1454,f1518,f1519,f1520,f1522,f1524,f1526,f1528,f1592,f1593,f1594,f1596,f1598,f1600,f1602,f1666,f1667,f1668,f1670,f1672,f1674,f1676,f1740,f1741,f1742,f1744,f1746,f1748,f1750,f1814,f1815,f1816,f1818,f1820,f1822,f1824,f1888,f1889,f1890,f1892,f1894,f1896,f1898,f1962,f1963,f1964,f1966,f1968,f1970,f1972,f2036,f2037,f2038,f2040,f2042,f2044,f2046,f2111,f2112,f2113,f2115,f2117,f2119,f2121,f2185,f2186,f2187,f2189,f2191,f2193,f2195,f2259,f2260,f2261,f2263,f2265,f2267,f2269,f2333,f2334,f2335,f2337,f2339,f2341,f2343,f2407,f2408,f2409,f2411,f2413,f2415,f2417,f2481,f2482,f2483,f2485,f2487,f2489,f2491,f2555,f2556,f2557,f2559,f2561,f2563,f2565,f2629,f2630,f2631,f2633,f2635,f2637,f2639,f2703,f2704,f2705,f2707,f2709,f2711,f2713,f2777,f2778,f2779,f2781,f2783,f2785,f2787,f2851,f2852,f2853,f2855,f2857,f2859,f2861,f2925,f2926,f2927,f2929,f2931,f2933,f2935,f2999,f3000,f3001,f3003,f3005,f3007,f3009,f3073,f3074,f3075,f3077,f3079,f3081,f3083,f3147,f3148,f3149,f3151,f3153,f3155,f3157,f3221,f3222,f3223,f3225,f3227,f3229,f3231,f3265,f3270,f3275,f3280,f3285,f3290,f3295,f3300,f3305,f3310,f3315,f3320,f3325,f3330,f3335,f3340,f3345,f3350,f3355,f3360,f3365,f3370,f3375,f3380,f3385,f3390,f3395,f3400,f3402,f3436,f3438,f3440,f3442,f3444,f3446,f3448,f3450,f3452,f3454,f3456,f3458,f3460,f3462,f3464,f3466,f3468,f3470,f3472,f3474,f3476,f3478,f3480,f3482,f3484,f3486,f3488,f3504,f3508,f3524,f3528,f3543,f3557,f3563,f3565,f3620,f3626,f3631,f3636,f3641,f3643,f3648,f3653,f3658,f3663,f3668,f3673,f3678,f3683,f3688,f3693,f3698,f3703,f3708,f3713,f3718,f3723,f3728,f3733,f3738,f3743,f3748,f3753,f3758,f3759,f3760,f3766,f3770,f3807,f3809,f3811,f3813,f3815,f3817,f3819,f3821,f3823,f3825,f3827,f3829,f3831,f3833,f3835,f3837,f3839,f3841,f3843,f3845,f3847,f3849,f3851,f3853,f3855,f3857,f3859,f3861,f3863,f3864,f3865,f3902,f3908,f3913,f3918,f3923,f3925,f3930,f3935,f3940,f3945,f3950,f3952,f3957,f3962,f3967,f3972,f3977,f3982,f3987,f3992,f3997,f4002,f4007,f4012,f4017,f4022,f4027,f4032,f4037,f4038,f4039,f4076,f4078,f4080,f4082,f4084,f4086,f4088,f4090,f4092,f4094,f4096,f4098,f4100,f4102,f4104,f4106,f4108,f4110,f4112,f4114,f4116,f4118,f4120,f4122,f4124,f4126,f4128,f4130,f4132,f4133,f4134,f4171,f4177,f4182,f4187,f4192,f4194,f4199,f4204,f4209,f4214,f4219,f4221,f4223,f4228,f4233,f4238,f4243,f4248,f4253,f4258,f4263,f4268,f4273,f4278,f4283,f4288,f4293,f4298,f4303,f4304,f4305,f4342,f4344,f4346,f4348,f4350,f4352,f4354,f4356,f4358,f4360,f4362,f4364,f4366,f4368,f4370,f4372,f4374,f4376,f4378,f4380,f4382,f4384,f4386,f4388,f4390,f4392,f4394,f4396,f4398,f4399,f4400,f4437,f4443,f4448,f4453,f4458,f4460,f4465,f4470,f4475,f4480,f4485,f4487,f4489,f4494,f4496,f4501,f4506,f4511,f4516,f4521,f4526,f4531,f4536,f4541,f4546,f4551,f4556,f4561,f4566,f4567,f4568,f4605,f4607,f4609,f4611,f4613,f4615,f4617,f4619,f4621,f4623,f4625,f4627,f4629,f4631,f4633,f4635,f4637,f4639,f4641,f4643,f4645,f4647,f4649,f4651,f4653,f4655,f4657,f4659,f4661,f4662,f4663,f4700,f4706,f4711,f4716,f4721,f4723,f4728,f4733,f4738,f4743,f4748,f4750,f4752,f4757,f4759,f4761,f4766,f4771,f4776,f4781,f4786,f4791,f4796,f4801,f4806,f4811,f4816,f4821,f4826,f4827,f4828,f4865,f4867,f4869,f4871,f4873,f4875,f4877,f4879,f4881,f4883,f4885,f4887,f4889,f4891,f4893,f4895,f4897,f4899,f4901,f4903,f4905,f4907,f4909,f4911,f4913,f4915,f4917,f4919,f4921,f4922,f4923,f4960,f4966,f4971,f4976,f4981,f4983,f4988,f4993,f4995,f5000,f5005,f5007,f5009,f5014,f5016,f5018,f5023,f5028,f5033,f5038,f5043,f5048,f5053,f5058,f5063,f5068,f5073,f5078,f5083,f5084,f5085,f5150,f5151,f5188,f5190,f5192,f5194,f5196,f5198,f5200,f5202,f5204,f5206,f5208,f5210,f5212,f5214,f5216,f5218,f5220,f5222,f5224,f5226,f5228,f5230,f5232,f5234,f5236,f5238,f5240,f5242,f5244,f5245,f5246,f5283,f5289,f5294,f5299,f5304,f5306,f5308,f5313,f5315,f5320,f5325,f5327,f5329,f5334,f5336,f5338,f5343,f5348,f5353,f5358,f5363,f5368,f5373,f5378,f5383,f5388,f5393,f5398,f5403,f5404,f5405,f5442,f5444,f5446,f5448,f5450,f5452,f5454,f5456,f5458,f5460,f5462,f5464,f5466,f5468,f5470,f5472,f5474,f5476,f5478,f5480,f5482,f5484,f5486,f5488,f5490,f5492,f5494,f5496,f5498,f5499,f5500,f5537,f5543,f5548,f5553,f5558,f5560,f5562,f5567,f5569,f5571,f5576,f5578,f5580,f5585,f5587,f5589,f5594,f5599,f5604,f5609,f5614,f5619,f5624,f5629,f5634,f5639,f5644,f5649,f5654,f5655,f5656,f5693,f5695,f5697,f5699,f5701,f5703,f5705,f5707,f5709,f5711,f5713,f5715,f5717,f5719,f5721,f5723,f5725,f5727,f5729,f5731,f5733,f5735,f5737,f5739,f5741,f5743,f5745,f5747,f5749,f5750,f5751,f5816,f5817])).

fof(f5817,plain,
    ( spl9_1
    | ~ spl9_96 ),
    inference(avatar_contradiction_clause,[],[f5752])).

fof(f5752,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_96 ),
    inference(unit_resulting_resolution,[],[f359,f3547])).

fof(f3547,plain,
    ( ! [X2,X3] : k1_mcart_1(sK3) != k4_tarski(X2,X3)
    | ~ spl9_1
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f3546,f89])).

fof(f89,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_1
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f3546,plain,
    ( ! [X2,X3] :
        ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
        | k1_mcart_1(sK3) != k4_tarski(X2,X3) )
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3532,f359])).

fof(f3532,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK3) != k4_tarski(X2,X3)
        | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))) )
    | ~ spl9_96 ),
    inference(superposition,[],[f82,f359])).

fof(f82,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK4(X0,X1) != X1
              & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK4(X0,X1) != X1
        & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',d1_mcart_1)).

fof(f359,plain,
    ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl9_96
  <=> k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f5816,plain,
    ( spl9_1
    | ~ spl9_96 ),
    inference(avatar_contradiction_clause,[],[f5815])).

fof(f5815,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_96 ),
    inference(trivial_inequality_removal,[],[f5782])).

fof(f5782,plain,
    ( k1_mcart_1(sK3) != k1_mcart_1(sK3)
    | ~ spl9_1
    | ~ spl9_96 ),
    inference(superposition,[],[f3547,f359])).

fof(f5751,plain,
    ( spl9_340
    | ~ spl9_295
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5690,f303,f179,f3303,f3526])).

fof(f3526,plain,
    ( spl9_340
  <=> ! [X14] :
        ( k2_mcart_1(k4_tarski(sK6(sK3,X14),sK7(sK3,X14))) = sK7(sK3,X14)
        | k2_mcart_1(sK3) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_340])])).

fof(f3303,plain,
    ( spl9_295
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_295])])).

fof(f179,plain,
    ( spl9_34
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))) = sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f303,plain,
    ( spl9_76
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f5690,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f568,f362])).

fof(f362,plain,
    ( ! [X7] :
        ( k4_tarski(sK6(sK3,X7),sK7(sK3,X7)) = sK3
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f348,f304])).

fof(f304,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f303])).

fof(f348,plain,
    ( ! [X7] :
        ( k4_tarski(sK6(sK3,X7),sK7(sK3,X7)) = sK3
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = X7 )
    | ~ spl9_76 ),
    inference(superposition,[],[f84,f304])).

fof(f84,plain,(
    ! [X6,X7,X1] :
      ( k4_tarski(X6,X7) = k4_tarski(sK6(k4_tarski(X6,X7),X1),sK7(k4_tarski(X6,X7),X1))
      | k2_mcart_1(k4_tarski(X6,X7)) = X1 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X0,X7,X1] :
      ( k2_mcart_1(X0) = X1
      | k4_tarski(sK6(X0,X1),sK7(X0,X1)) = X0
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK7(X0,X1) != X1
              & k4_tarski(sK6(X0,X1),sK7(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK7(X0,X1) != X1
        & k4_tarski(sK6(X0,X1),sK7(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',d2_mcart_1)).

fof(f568,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_34 ),
    inference(superposition,[],[f86,f180])).

fof(f180,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))) = sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f179])).

fof(f86,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5750,plain,
    ( spl9_336
    | ~ spl9_295
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5688,f303,f179,f3303,f3506])).

fof(f3506,plain,
    ( spl9_336
  <=> ! [X14] :
        ( k2_mcart_1(k4_tarski(sK4(sK3,X14),sK5(sK3,X14))) = sK5(sK3,X14)
        | k1_mcart_1(sK3) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_336])])).

fof(f5688,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f568,f352])).

fof(f352,plain,
    ( ! [X1] :
        ( k4_tarski(sK4(sK3,X1),sK5(sK3,X1)) = sK3
        | k1_mcart_1(sK3) = X1 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f344,f304])).

fof(f344,plain,
    ( ! [X1] :
        ( k4_tarski(sK4(sK3,X1),sK5(sK3,X1)) = sK3
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = X1 )
    | ~ spl9_76 ),
    inference(superposition,[],[f80,f304])).

fof(f80,plain,(
    ! [X6,X7,X1] :
      ( k4_tarski(X6,X7) = k4_tarski(sK4(k4_tarski(X6,X7),X1),sK5(k4_tarski(X6,X7),X1))
      | k1_mcart_1(k4_tarski(X6,X7)) = X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X0,X7,X1] :
      ( k1_mcart_1(X0) = X1
      | k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5749,plain,
    ( ~ spl9_727
    | spl9_204
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5748,f247,f179,f817,f5652])).

fof(f5652,plain,
    ( spl9_727
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_727])])).

fof(f817,plain,
    ( spl9_204
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).

fof(f247,plain,
    ( spl9_54
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))) = sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f5748,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f5686,f248])).

fof(f248,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))) = sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f247])).

fof(f5686,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(superposition,[],[f568,f248])).

fof(f5747,plain,
    ( ~ spl9_725
    | spl9_198
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5746,f243,f179,f792,f5647])).

fof(f5647,plain,
    ( spl9_725
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_725])])).

fof(f792,plain,
    ( spl9_198
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).

fof(f243,plain,
    ( spl9_52
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))) = sK8(k3_zfmisc_1(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f5746,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f5685,f244])).

fof(f244,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))) = sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f243])).

fof(f5685,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(superposition,[],[f568,f244])).

fof(f5745,plain,
    ( ~ spl9_723
    | spl9_192
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5744,f239,f179,f767,f5642])).

fof(f5642,plain,
    ( spl9_723
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_723])])).

fof(f767,plain,
    ( spl9_192
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_192])])).

fof(f239,plain,
    ( spl9_50
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) = sK8(k3_zfmisc_1(sK0,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f5744,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f5684,f240])).

fof(f240,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) = sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f239])).

fof(f5684,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(superposition,[],[f568,f240])).

fof(f5743,plain,
    ( ~ spl9_721
    | spl9_186
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5742,f235,f179,f742,f5637])).

fof(f5637,plain,
    ( spl9_721
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_721])])).

fof(f742,plain,
    ( spl9_186
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f235,plain,
    ( spl9_48
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))) = sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f5742,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f5683,f236])).

fof(f236,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))) = sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f235])).

fof(f5683,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(superposition,[],[f568,f236])).

fof(f5741,plain,
    ( ~ spl9_719
    | spl9_180
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5740,f231,f179,f717,f5632])).

fof(f5632,plain,
    ( spl9_719
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_719])])).

fof(f717,plain,
    ( spl9_180
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f231,plain,
    ( spl9_46
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))) = sK8(k3_zfmisc_1(sK1,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f5740,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f5682,f232])).

fof(f232,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))) = sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f231])).

fof(f5682,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(superposition,[],[f568,f232])).

fof(f5739,plain,
    ( ~ spl9_717
    | spl9_174
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5738,f227,f179,f692,f5627])).

fof(f5627,plain,
    ( spl9_717
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_717])])).

fof(f692,plain,
    ( spl9_174
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_174])])).

fof(f227,plain,
    ( spl9_44
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) = sK8(k3_zfmisc_1(sK0,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f5738,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f5681,f228])).

fof(f228,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) = sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f227])).

fof(f5681,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(superposition,[],[f568,f228])).

fof(f5737,plain,
    ( ~ spl9_715
    | spl9_166
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5736,f223,f179,f658,f5622])).

fof(f5622,plain,
    ( spl9_715
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_715])])).

fof(f658,plain,
    ( spl9_166
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f223,plain,
    ( spl9_42
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) = sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f5736,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f5680,f224])).

fof(f224,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) = sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f223])).

fof(f5680,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(superposition,[],[f568,f224])).

fof(f5735,plain,
    ( ~ spl9_713
    | spl9_160
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5734,f219,f179,f633,f5617])).

fof(f5617,plain,
    ( spl9_713
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_713])])).

fof(f633,plain,
    ( spl9_160
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f219,plain,
    ( spl9_40
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) = sK8(k3_zfmisc_1(sK1,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f5734,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f5679,f220])).

fof(f220,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) = sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f219])).

fof(f5679,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(superposition,[],[f568,f220])).

fof(f5733,plain,
    ( ~ spl9_711
    | spl9_154
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5732,f215,f179,f608,f5612])).

fof(f5612,plain,
    ( spl9_711
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_711])])).

fof(f608,plain,
    ( spl9_154
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f215,plain,
    ( spl9_38
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) = sK8(k3_zfmisc_1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f5732,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f5678,f216])).

fof(f216,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) = sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f215])).

fof(f5678,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(superposition,[],[f568,f216])).

fof(f5731,plain,
    ( ~ spl9_709
    | spl9_222
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5730,f262,f179,f892,f5607])).

fof(f5607,plain,
    ( spl9_709
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_709])])).

fof(f892,plain,
    ( spl9_222
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f262,plain,
    ( spl9_60
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))) = sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f5730,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f5677,f263])).

fof(f263,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))) = sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f262])).

fof(f5677,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(superposition,[],[f568,f263])).

fof(f5729,plain,
    ( ~ spl9_707
    | spl9_216
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5728,f258,f179,f867,f5602])).

fof(f5602,plain,
    ( spl9_707
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_707])])).

fof(f867,plain,
    ( spl9_216
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f258,plain,
    ( spl9_58
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))) = sK8(k3_zfmisc_1(sK1,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f5728,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f5676,f259])).

fof(f259,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))) = sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f258])).

fof(f5676,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(superposition,[],[f568,f259])).

fof(f5727,plain,
    ( ~ spl9_705
    | spl9_210
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5726,f254,f179,f842,f5597])).

fof(f5597,plain,
    ( spl9_705
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_705])])).

fof(f842,plain,
    ( spl9_210
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f254,plain,
    ( spl9_56
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) = sK8(k3_zfmisc_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f5726,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f5675,f255])).

fof(f255,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) = sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f254])).

fof(f5675,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(superposition,[],[f568,f255])).

fof(f5725,plain,
    ( ~ spl9_703
    | spl9_258
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5724,f291,f179,f1042,f5592])).

fof(f5592,plain,
    ( spl9_703
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_703])])).

fof(f1042,plain,
    ( spl9_258
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f291,plain,
    ( spl9_72
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))) = sK8(k3_zfmisc_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f5724,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f5674,f292])).

fof(f292,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))) = sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f291])).

fof(f5674,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(superposition,[],[f568,f292])).

fof(f5723,plain,
    ( ~ spl9_571
    | spl9_128
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5722,f179,f162,f499,f4741])).

fof(f4741,plain,
    ( spl9_571
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_571])])).

fof(f499,plain,
    ( spl9_128
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f162,plain,
    ( spl9_28
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))) = sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f5722,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5673,f163])).

fof(f163,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))) = sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f162])).

fof(f5673,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f163])).

fof(f5721,plain,
    ( ~ spl9_523
    | spl9_122
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5720,f179,f158,f474,f4478])).

fof(f4478,plain,
    ( spl9_523
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_523])])).

fof(f474,plain,
    ( spl9_122
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f158,plain,
    ( spl9_26
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) = sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f5720,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5672,f159])).

fof(f159,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) = sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f158])).

fof(f5672,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f159])).

fof(f5719,plain,
    ( ~ spl9_701
    | spl9_246
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5718,f282,f179,f992,f5583])).

fof(f5583,plain,
    ( spl9_701
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_701])])).

fof(f992,plain,
    ( spl9_246
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).

fof(f282,plain,
    ( spl9_68
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))) = sK8(k3_zfmisc_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f5718,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5671,f283])).

fof(f283,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))) = sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f282])).

fof(f5671,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(superposition,[],[f568,f283])).

fof(f5717,plain,
    ( ~ spl9_473
    | spl9_116
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5716,f179,f154,f449,f4212])).

fof(f4212,plain,
    ( spl9_473
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_473])])).

fof(f449,plain,
    ( spl9_116
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f154,plain,
    ( spl9_24
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) = sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f5716,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5670,f155])).

fof(f155,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) = sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f154])).

fof(f5670,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f155])).

fof(f5715,plain,
    ( ~ spl9_421
    | spl9_110
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5714,f179,f150,f424,f3943])).

fof(f3943,plain,
    ( spl9_421
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_421])])).

fof(f424,plain,
    ( spl9_110
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f150,plain,
    ( spl9_22
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) = sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f5714,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5669,f151])).

fof(f151,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) = sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f5669,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f151])).

fof(f5713,plain,
    ( ~ spl9_699
    | spl9_234
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5712,f270,f179,f942,f5574])).

fof(f5574,plain,
    ( spl9_699
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_699])])).

fof(f942,plain,
    ( spl9_234
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_234])])).

fof(f270,plain,
    ( spl9_64
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))) = sK8(k3_zfmisc_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f5712,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f5668,f271])).

fof(f271,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))) = sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f270])).

fof(f5668,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(superposition,[],[f568,f271])).

fof(f5711,plain,
    ( spl9_148
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5710,f179,f583])).

fof(f583,plain,
    ( spl9_148
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).

fof(f5710,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5691,f180])).

fof(f5691,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34 ),
    inference(trivial_inequality_removal,[],[f5667])).

fof(f5667,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f180])).

fof(f5709,plain,
    ( ~ spl9_615
    | spl9_134
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5708,f179,f168,f524,f4998])).

fof(f4998,plain,
    ( spl9_615
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_615])])).

fof(f524,plain,
    ( spl9_134
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f168,plain,
    ( spl9_30
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) = sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f5708,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5666,f169])).

fof(f169,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) = sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f168])).

fof(f5666,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f169])).

fof(f5707,plain,
    ( ~ spl9_697
    | spl9_240
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f5706,f274,f179,f967,f5565])).

fof(f5565,plain,
    ( spl9_697
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_697])])).

fof(f967,plain,
    ( spl9_240
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f274,plain,
    ( spl9_66
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))) = sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f5706,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5665,f275])).

fof(f275,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))) = sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f274])).

fof(f5665,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(superposition,[],[f568,f275])).

fof(f5705,plain,
    ( ~ spl9_657
    | spl9_142
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5704,f179,f172,f558,f5318])).

fof(f5318,plain,
    ( spl9_657
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_657])])).

fof(f558,plain,
    ( spl9_142
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f172,plain,
    ( spl9_32
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))) = sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f5704,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5664,f173])).

fof(f173,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))) = sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f172])).

fof(f5664,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f173])).

fof(f5703,plain,
    ( ~ spl9_363
    | spl9_102
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5702,f179,f122,f390,f3661])).

fof(f3661,plain,
    ( spl9_363
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_363])])).

fof(f390,plain,
    ( spl9_102
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f122,plain,
    ( spl9_16
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) = sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f5702,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5663,f123])).

fof(f123,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) = sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f5663,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(superposition,[],[f568,f123])).

fof(f5701,plain,
    ( ~ spl9_695
    | spl9_264
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f5700,f295,f179,f1067,f5556])).

fof(f5556,plain,
    ( spl9_695
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_695])])).

fof(f1067,plain,
    ( spl9_264
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_264])])).

fof(f295,plain,
    ( spl9_74
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))) = sK8(k3_zfmisc_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f5700,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f5662,f296])).

fof(f296,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))) = sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f295])).

fof(f5662,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(superposition,[],[f568,f296])).

fof(f5699,plain,
    ( ~ spl9_693
    | spl9_228
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f5698,f266,f179,f917,f5551])).

fof(f5551,plain,
    ( spl9_693
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_693])])).

fof(f917,plain,
    ( spl9_228
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).

fof(f266,plain,
    ( spl9_62
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) = sK8(k3_zfmisc_1(sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f5698,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f5661,f267])).

fof(f267,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) = sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f266])).

fof(f5661,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(superposition,[],[f568,f267])).

fof(f5697,plain,
    ( ~ spl9_691
    | spl9_252
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f5696,f286,f179,f1017,f5546])).

fof(f5546,plain,
    ( spl9_691
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_691])])).

fof(f1017,plain,
    ( spl9_252
  <=> k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_252])])).

fof(f286,plain,
    ( spl9_70
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))) = sK8(k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f5696,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f5660,f287])).

fof(f287,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))) = sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f286])).

fof(f5660,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(superposition,[],[f568,f287])).

fof(f5695,plain,
    ( ~ spl9_689
    | spl9_2
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f5694,f358,f179,f3555,f5541])).

fof(f5541,plain,
    ( spl9_689
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_689])])).

fof(f3555,plain,
    ( spl9_2
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f5694,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f5658,f359])).

fof(f5658,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(superposition,[],[f568,f359])).

fof(f5693,plain,
    ( spl9_148
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5692,f179,f583])).

fof(f5692,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5657,f180])).

fof(f5657,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f180,f568])).

fof(f5656,plain,
    ( spl9_338
    | ~ spl9_295
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5534,f303,f179,f3303,f3522])).

fof(f3522,plain,
    ( spl9_338
  <=> ! [X4] :
        ( k1_mcart_1(k4_tarski(sK6(sK3,X4),sK7(sK3,X4))) = sK6(sK3,X4)
        | k2_mcart_1(sK3) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_338])])).

fof(f5534,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f564,f362])).

fof(f564,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_34 ),
    inference(superposition,[],[f82,f180])).

fof(f5655,plain,
    ( spl9_334
    | ~ spl9_295
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5532,f303,f179,f3303,f3502])).

fof(f3502,plain,
    ( spl9_334
  <=> ! [X4] :
        ( k1_mcart_1(k4_tarski(sK4(sK3,X4),sK5(sK3,X4))) = sK4(sK3,X4)
        | k1_mcart_1(sK3) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_334])])).

fof(f5532,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f564,f352])).

fof(f5654,plain,
    ( ~ spl9_727
    | spl9_202
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5650,f247,f179,f810,f5652])).

fof(f810,plain,
    ( spl9_202
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_202])])).

fof(f5650,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f5530,f248])).

fof(f5530,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_34
    | ~ spl9_54 ),
    inference(superposition,[],[f564,f248])).

fof(f5649,plain,
    ( ~ spl9_725
    | spl9_196
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5645,f243,f179,f785,f5647])).

fof(f785,plain,
    ( spl9_196
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_196])])).

fof(f5645,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f5529,f244])).

fof(f5529,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_34
    | ~ spl9_52 ),
    inference(superposition,[],[f564,f244])).

fof(f5644,plain,
    ( ~ spl9_723
    | spl9_190
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5640,f239,f179,f760,f5642])).

fof(f760,plain,
    ( spl9_190
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_190])])).

fof(f5640,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f5528,f240])).

fof(f5528,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_34
    | ~ spl9_50 ),
    inference(superposition,[],[f564,f240])).

fof(f5639,plain,
    ( ~ spl9_721
    | spl9_184
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5635,f235,f179,f735,f5637])).

fof(f735,plain,
    ( spl9_184
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f5635,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f5527,f236])).

fof(f5527,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_34
    | ~ spl9_48 ),
    inference(superposition,[],[f564,f236])).

fof(f5634,plain,
    ( ~ spl9_719
    | spl9_178
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5630,f231,f179,f710,f5632])).

fof(f710,plain,
    ( spl9_178
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_178])])).

fof(f5630,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f5526,f232])).

fof(f5526,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_34
    | ~ spl9_46 ),
    inference(superposition,[],[f564,f232])).

fof(f5629,plain,
    ( ~ spl9_717
    | spl9_172
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5625,f227,f179,f685,f5627])).

fof(f685,plain,
    ( spl9_172
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f5625,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f5525,f228])).

fof(f5525,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(superposition,[],[f564,f228])).

fof(f5624,plain,
    ( ~ spl9_715
    | spl9_164
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5620,f223,f179,f651,f5622])).

fof(f651,plain,
    ( spl9_164
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_164])])).

fof(f5620,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f5524,f224])).

fof(f5524,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(superposition,[],[f564,f224])).

fof(f5619,plain,
    ( ~ spl9_713
    | spl9_158
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5615,f219,f179,f626,f5617])).

fof(f626,plain,
    ( spl9_158
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f5615,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f5523,f220])).

fof(f5523,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_34
    | ~ spl9_40 ),
    inference(superposition,[],[f564,f220])).

fof(f5614,plain,
    ( ~ spl9_711
    | spl9_152
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5610,f215,f179,f601,f5612])).

fof(f601,plain,
    ( spl9_152
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_152])])).

fof(f5610,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f5522,f216])).

fof(f5522,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(superposition,[],[f564,f216])).

fof(f5609,plain,
    ( ~ spl9_709
    | spl9_220
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5605,f262,f179,f885,f5607])).

fof(f885,plain,
    ( spl9_220
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_220])])).

fof(f5605,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f5521,f263])).

fof(f5521,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_34
    | ~ spl9_60 ),
    inference(superposition,[],[f564,f263])).

fof(f5604,plain,
    ( ~ spl9_707
    | spl9_214
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5600,f258,f179,f860,f5602])).

fof(f860,plain,
    ( spl9_214
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f5600,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f5520,f259])).

fof(f5520,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_34
    | ~ spl9_58 ),
    inference(superposition,[],[f564,f259])).

fof(f5599,plain,
    ( ~ spl9_705
    | spl9_208
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5595,f254,f179,f835,f5597])).

fof(f835,plain,
    ( spl9_208
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_208])])).

fof(f5595,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f5519,f255])).

fof(f5519,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_34
    | ~ spl9_56 ),
    inference(superposition,[],[f564,f255])).

fof(f5594,plain,
    ( ~ spl9_703
    | spl9_256
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5590,f291,f179,f1035,f5592])).

fof(f1035,plain,
    ( spl9_256
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_256])])).

fof(f5590,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f5518,f292])).

fof(f5518,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_34
    | ~ spl9_72 ),
    inference(superposition,[],[f564,f292])).

fof(f5589,plain,
    ( ~ spl9_571
    | spl9_126
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5588,f179,f162,f492,f4741])).

fof(f492,plain,
    ( spl9_126
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f5588,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5517,f163])).

fof(f5517,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f163])).

fof(f5587,plain,
    ( ~ spl9_523
    | spl9_120
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5586,f179,f158,f467,f4478])).

fof(f467,plain,
    ( spl9_120
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f5586,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5516,f159])).

fof(f5516,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f159])).

fof(f5585,plain,
    ( ~ spl9_701
    | spl9_244
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5581,f282,f179,f985,f5583])).

fof(f985,plain,
    ( spl9_244
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f5581,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5515,f283])).

fof(f5515,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_34
    | ~ spl9_68 ),
    inference(superposition,[],[f564,f283])).

fof(f5580,plain,
    ( ~ spl9_473
    | spl9_114
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5579,f179,f154,f442,f4212])).

fof(f442,plain,
    ( spl9_114
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f5579,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5514,f155])).

fof(f5514,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f155])).

fof(f5578,plain,
    ( ~ spl9_421
    | spl9_108
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5577,f179,f150,f417,f3943])).

fof(f417,plain,
    ( spl9_108
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f5577,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5513,f151])).

fof(f5513,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f151])).

fof(f5576,plain,
    ( ~ spl9_699
    | spl9_232
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5572,f270,f179,f935,f5574])).

fof(f935,plain,
    ( spl9_232
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_232])])).

fof(f5572,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f5512,f271])).

fof(f5512,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_34
    | ~ spl9_64 ),
    inference(superposition,[],[f564,f271])).

fof(f5571,plain,
    ( spl9_146
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5570,f179,f576])).

fof(f576,plain,
    ( spl9_146
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f5570,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5535,f180])).

fof(f5535,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34 ),
    inference(trivial_inequality_removal,[],[f5511])).

fof(f5511,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f180])).

fof(f5569,plain,
    ( ~ spl9_615
    | spl9_132
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5568,f179,f168,f517,f4998])).

fof(f517,plain,
    ( spl9_132
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f5568,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5510,f169])).

fof(f5510,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f169])).

fof(f5567,plain,
    ( ~ spl9_697
    | spl9_238
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f5563,f274,f179,f960,f5565])).

fof(f960,plain,
    ( spl9_238
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f5563,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5509,f275])).

fof(f5509,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_34
    | ~ spl9_66 ),
    inference(superposition,[],[f564,f275])).

fof(f5562,plain,
    ( ~ spl9_657
    | spl9_140
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5561,f179,f172,f551,f5318])).

fof(f551,plain,
    ( spl9_140
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f5561,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5508,f173])).

fof(f5508,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f173])).

fof(f5560,plain,
    ( ~ spl9_363
    | spl9_100
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5559,f179,f122,f383,f3661])).

fof(f383,plain,
    ( spl9_100
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f5559,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5507,f123])).

fof(f5507,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(superposition,[],[f564,f123])).

fof(f5558,plain,
    ( ~ spl9_695
    | spl9_262
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f5554,f295,f179,f1060,f5556])).

fof(f1060,plain,
    ( spl9_262
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_262])])).

fof(f5554,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f5506,f296])).

fof(f5506,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_34
    | ~ spl9_74 ),
    inference(superposition,[],[f564,f296])).

fof(f5553,plain,
    ( ~ spl9_693
    | spl9_226
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f5549,f266,f179,f910,f5551])).

fof(f910,plain,
    ( spl9_226
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).

fof(f5549,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f5505,f267])).

fof(f5505,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_34
    | ~ spl9_62 ),
    inference(superposition,[],[f564,f267])).

fof(f5548,plain,
    ( ~ spl9_691
    | spl9_250
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f5544,f286,f179,f1010,f5546])).

fof(f1010,plain,
    ( spl9_250
  <=> k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_250])])).

fof(f5544,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f5504,f287])).

fof(f5504,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_34
    | ~ spl9_70 ),
    inference(superposition,[],[f564,f287])).

fof(f5543,plain,
    ( ~ spl9_689
    | spl9_1
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f5539,f358,f179,f88,f5541])).

fof(f5539,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f5538,f89])).

fof(f5538,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f5502,f359])).

fof(f5502,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_34
    | ~ spl9_96 ),
    inference(superposition,[],[f564,f359])).

fof(f5537,plain,
    ( spl9_146
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5536,f179,f576])).

fof(f5536,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5501,f180])).

fof(f5501,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f180,f564])).

fof(f5500,plain,
    ( spl9_340
    | ~ spl9_289
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5439,f303,f172,f3288,f3526])).

fof(f3288,plain,
    ( spl9_289
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_289])])).

fof(f5439,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f543,f362])).

fof(f543,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_32 ),
    inference(superposition,[],[f86,f173])).

fof(f5499,plain,
    ( spl9_336
    | ~ spl9_289
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5437,f303,f172,f3288,f3506])).

fof(f5437,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f543,f352])).

fof(f5498,plain,
    ( ~ spl9_687
    | spl9_204
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5497,f247,f172,f817,f5401])).

fof(f5401,plain,
    ( spl9_687
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_687])])).

fof(f5497,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f5435,f248])).

fof(f5435,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(superposition,[],[f543,f248])).

fof(f5496,plain,
    ( ~ spl9_685
    | spl9_198
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5495,f243,f172,f792,f5396])).

fof(f5396,plain,
    ( spl9_685
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_685])])).

fof(f5495,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f5434,f244])).

fof(f5434,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(superposition,[],[f543,f244])).

fof(f5494,plain,
    ( ~ spl9_683
    | spl9_192
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5493,f239,f172,f767,f5391])).

fof(f5391,plain,
    ( spl9_683
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_683])])).

fof(f5493,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f5433,f240])).

fof(f5433,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(superposition,[],[f543,f240])).

fof(f5492,plain,
    ( ~ spl9_681
    | spl9_186
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5491,f235,f172,f742,f5386])).

fof(f5386,plain,
    ( spl9_681
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_681])])).

fof(f5491,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f5432,f236])).

fof(f5432,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(superposition,[],[f543,f236])).

fof(f5490,plain,
    ( ~ spl9_679
    | spl9_180
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5489,f231,f172,f717,f5381])).

fof(f5381,plain,
    ( spl9_679
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_679])])).

fof(f5489,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f5431,f232])).

fof(f5431,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(superposition,[],[f543,f232])).

fof(f5488,plain,
    ( ~ spl9_677
    | spl9_174
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5487,f227,f172,f692,f5376])).

fof(f5376,plain,
    ( spl9_677
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_677])])).

fof(f5487,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f5430,f228])).

fof(f5430,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(superposition,[],[f543,f228])).

fof(f5486,plain,
    ( ~ spl9_675
    | spl9_166
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5485,f223,f172,f658,f5371])).

fof(f5371,plain,
    ( spl9_675
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_675])])).

fof(f5485,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f5429,f224])).

fof(f5429,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(superposition,[],[f543,f224])).

fof(f5484,plain,
    ( ~ spl9_673
    | spl9_160
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5483,f219,f172,f633,f5366])).

fof(f5366,plain,
    ( spl9_673
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_673])])).

fof(f5483,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f5428,f220])).

fof(f5428,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(superposition,[],[f543,f220])).

fof(f5482,plain,
    ( ~ spl9_671
    | spl9_154
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5481,f215,f172,f608,f5361])).

fof(f5361,plain,
    ( spl9_671
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_671])])).

fof(f5481,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f5427,f216])).

fof(f5427,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(superposition,[],[f543,f216])).

fof(f5480,plain,
    ( ~ spl9_669
    | spl9_222
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5479,f262,f172,f892,f5356])).

fof(f5356,plain,
    ( spl9_669
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_669])])).

fof(f5479,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f5426,f263])).

fof(f5426,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(superposition,[],[f543,f263])).

fof(f5478,plain,
    ( ~ spl9_667
    | spl9_216
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5477,f258,f172,f867,f5351])).

fof(f5351,plain,
    ( spl9_667
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_667])])).

fof(f5477,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f5425,f259])).

fof(f5425,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(superposition,[],[f543,f259])).

fof(f5476,plain,
    ( ~ spl9_665
    | spl9_210
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5475,f254,f172,f842,f5346])).

fof(f5346,plain,
    ( spl9_665
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_665])])).

fof(f5475,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f5424,f255])).

fof(f5424,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(superposition,[],[f543,f255])).

fof(f5474,plain,
    ( ~ spl9_663
    | spl9_258
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5473,f291,f172,f1042,f5341])).

fof(f5341,plain,
    ( spl9_663
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_663])])).

fof(f5473,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f5423,f292])).

fof(f5423,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(superposition,[],[f543,f292])).

fof(f5472,plain,
    ( ~ spl9_565
    | spl9_128
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5471,f172,f162,f499,f4726])).

fof(f4726,plain,
    ( spl9_565
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_565])])).

fof(f5471,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5422,f163])).

fof(f5422,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f163])).

fof(f5470,plain,
    ( ~ spl9_517
    | spl9_122
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5469,f172,f158,f474,f4463])).

fof(f4463,plain,
    ( spl9_517
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_517])])).

fof(f5469,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5421,f159])).

fof(f5421,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f159])).

fof(f5468,plain,
    ( ~ spl9_661
    | spl9_246
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5467,f282,f172,f992,f5332])).

fof(f5332,plain,
    ( spl9_661
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_661])])).

fof(f5467,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5420,f283])).

fof(f5420,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(superposition,[],[f543,f283])).

fof(f5466,plain,
    ( ~ spl9_467
    | spl9_116
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5465,f172,f154,f449,f4197])).

fof(f4197,plain,
    ( spl9_467
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_467])])).

fof(f5465,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5419,f155])).

fof(f5419,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f155])).

fof(f5464,plain,
    ( ~ spl9_415
    | spl9_110
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5463,f172,f150,f424,f3928])).

fof(f3928,plain,
    ( spl9_415
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_415])])).

fof(f5463,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5418,f151])).

fof(f5418,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f151])).

fof(f5462,plain,
    ( ~ spl9_659
    | spl9_234
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5461,f270,f172,f942,f5323])).

fof(f5323,plain,
    ( spl9_659
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_659])])).

fof(f5461,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f5417,f271])).

fof(f5417,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(superposition,[],[f543,f271])).

fof(f5460,plain,
    ( ~ spl9_657
    | spl9_148
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5459,f179,f172,f583,f5318])).

fof(f5459,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5416,f180])).

fof(f5416,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(superposition,[],[f543,f180])).

fof(f5458,plain,
    ( ~ spl9_611
    | spl9_134
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5457,f172,f168,f524,f4986])).

fof(f4986,plain,
    ( spl9_611
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_611])])).

fof(f5457,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5415,f169])).

fof(f5415,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f169])).

fof(f5456,plain,
    ( ~ spl9_655
    | spl9_240
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f5455,f274,f172,f967,f5311])).

fof(f5311,plain,
    ( spl9_655
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_655])])).

fof(f5455,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5414,f275])).

fof(f5414,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(superposition,[],[f543,f275])).

fof(f5454,plain,
    ( spl9_142
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5453,f172,f558])).

fof(f5453,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5440,f173])).

fof(f5440,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32 ),
    inference(trivial_inequality_removal,[],[f5413])).

fof(f5413,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f173])).

fof(f5452,plain,
    ( ~ spl9_357
    | spl9_102
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5451,f172,f122,f390,f3646])).

fof(f3646,plain,
    ( spl9_357
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_357])])).

fof(f5451,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5412,f123])).

fof(f5412,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(superposition,[],[f543,f123])).

fof(f5450,plain,
    ( ~ spl9_653
    | spl9_264
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f5449,f295,f172,f1067,f5302])).

fof(f5302,plain,
    ( spl9_653
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_653])])).

fof(f5449,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f5411,f296])).

fof(f5411,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(superposition,[],[f543,f296])).

fof(f5448,plain,
    ( ~ spl9_651
    | spl9_228
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f5447,f266,f172,f917,f5297])).

fof(f5297,plain,
    ( spl9_651
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_651])])).

fof(f5447,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f5410,f267])).

fof(f5410,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(superposition,[],[f543,f267])).

fof(f5446,plain,
    ( ~ spl9_649
    | spl9_252
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f5445,f286,f172,f1017,f5292])).

fof(f5292,plain,
    ( spl9_649
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_649])])).

fof(f5445,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f5409,f287])).

fof(f5409,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(superposition,[],[f543,f287])).

fof(f5444,plain,
    ( ~ spl9_647
    | spl9_2
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f5443,f358,f172,f3555,f5287])).

fof(f5287,plain,
    ( spl9_647
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_647])])).

fof(f5443,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f5407,f359])).

fof(f5407,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(superposition,[],[f543,f359])).

fof(f5442,plain,
    ( spl9_142
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5441,f172,f558])).

fof(f5441,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5406,f173])).

fof(f5406,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f173,f543])).

fof(f5405,plain,
    ( spl9_338
    | ~ spl9_289
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5280,f303,f172,f3288,f3522])).

fof(f5280,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f539,f362])).

fof(f539,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_32 ),
    inference(superposition,[],[f82,f173])).

fof(f5404,plain,
    ( spl9_334
    | ~ spl9_289
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5278,f303,f172,f3288,f3502])).

fof(f5278,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f539,f352])).

fof(f5403,plain,
    ( ~ spl9_687
    | spl9_202
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5399,f247,f172,f810,f5401])).

fof(f5399,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f5276,f248])).

fof(f5276,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_32
    | ~ spl9_54 ),
    inference(superposition,[],[f539,f248])).

fof(f5398,plain,
    ( ~ spl9_685
    | spl9_196
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5394,f243,f172,f785,f5396])).

fof(f5394,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f5275,f244])).

fof(f5275,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_32
    | ~ spl9_52 ),
    inference(superposition,[],[f539,f244])).

fof(f5393,plain,
    ( ~ spl9_683
    | spl9_190
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5389,f239,f172,f760,f5391])).

fof(f5389,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f5274,f240])).

fof(f5274,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_32
    | ~ spl9_50 ),
    inference(superposition,[],[f539,f240])).

fof(f5388,plain,
    ( ~ spl9_681
    | spl9_184
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5384,f235,f172,f735,f5386])).

fof(f5384,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f5273,f236])).

fof(f5273,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(superposition,[],[f539,f236])).

fof(f5383,plain,
    ( ~ spl9_679
    | spl9_178
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5379,f231,f172,f710,f5381])).

fof(f5379,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f5272,f232])).

fof(f5272,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(superposition,[],[f539,f232])).

fof(f5378,plain,
    ( ~ spl9_677
    | spl9_172
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5374,f227,f172,f685,f5376])).

fof(f5374,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f5271,f228])).

fof(f5271,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_32
    | ~ spl9_44 ),
    inference(superposition,[],[f539,f228])).

fof(f5373,plain,
    ( ~ spl9_675
    | spl9_164
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5369,f223,f172,f651,f5371])).

fof(f5369,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f5270,f224])).

fof(f5270,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_32
    | ~ spl9_42 ),
    inference(superposition,[],[f539,f224])).

fof(f5368,plain,
    ( ~ spl9_673
    | spl9_158
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5364,f219,f172,f626,f5366])).

fof(f5364,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f5269,f220])).

fof(f5269,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_32
    | ~ spl9_40 ),
    inference(superposition,[],[f539,f220])).

fof(f5363,plain,
    ( ~ spl9_671
    | spl9_152
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5359,f215,f172,f601,f5361])).

fof(f5359,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f5268,f216])).

fof(f5268,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(superposition,[],[f539,f216])).

fof(f5358,plain,
    ( ~ spl9_669
    | spl9_220
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5354,f262,f172,f885,f5356])).

fof(f5354,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f5267,f263])).

fof(f5267,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(superposition,[],[f539,f263])).

fof(f5353,plain,
    ( ~ spl9_667
    | spl9_214
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5349,f258,f172,f860,f5351])).

fof(f5349,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f5266,f259])).

fof(f5266,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_32
    | ~ spl9_58 ),
    inference(superposition,[],[f539,f259])).

fof(f5348,plain,
    ( ~ spl9_665
    | spl9_208
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5344,f254,f172,f835,f5346])).

fof(f5344,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f5265,f255])).

fof(f5265,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(superposition,[],[f539,f255])).

fof(f5343,plain,
    ( ~ spl9_663
    | spl9_256
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5339,f291,f172,f1035,f5341])).

fof(f5339,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f5264,f292])).

fof(f5264,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_32
    | ~ spl9_72 ),
    inference(superposition,[],[f539,f292])).

fof(f5338,plain,
    ( ~ spl9_565
    | spl9_126
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5337,f172,f162,f492,f4726])).

fof(f5337,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5263,f163])).

fof(f5263,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f163])).

fof(f5336,plain,
    ( ~ spl9_517
    | spl9_120
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5335,f172,f158,f467,f4463])).

fof(f5335,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5262,f159])).

fof(f5262,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f159])).

fof(f5334,plain,
    ( ~ spl9_661
    | spl9_244
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5330,f282,f172,f985,f5332])).

fof(f5330,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5261,f283])).

fof(f5261,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(superposition,[],[f539,f283])).

fof(f5329,plain,
    ( ~ spl9_467
    | spl9_114
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5328,f172,f154,f442,f4197])).

fof(f5328,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5260,f155])).

fof(f5260,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f155])).

fof(f5327,plain,
    ( ~ spl9_415
    | spl9_108
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5326,f172,f150,f417,f3928])).

fof(f5326,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5259,f151])).

fof(f5259,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f151])).

fof(f5325,plain,
    ( ~ spl9_659
    | spl9_232
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5321,f270,f172,f935,f5323])).

fof(f5321,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f5258,f271])).

fof(f5258,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_32
    | ~ spl9_64 ),
    inference(superposition,[],[f539,f271])).

fof(f5320,plain,
    ( ~ spl9_657
    | spl9_146
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5316,f179,f172,f576,f5318])).

fof(f5316,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5257,f180])).

fof(f5257,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_32
    | ~ spl9_34 ),
    inference(superposition,[],[f539,f180])).

fof(f5315,plain,
    ( ~ spl9_611
    | spl9_132
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5314,f172,f168,f517,f4986])).

fof(f5314,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5256,f169])).

fof(f5256,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f169])).

fof(f5313,plain,
    ( ~ spl9_655
    | spl9_238
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f5309,f274,f172,f960,f5311])).

fof(f5309,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5255,f275])).

fof(f5255,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_32
    | ~ spl9_66 ),
    inference(superposition,[],[f539,f275])).

fof(f5308,plain,
    ( spl9_140
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5307,f172,f551])).

fof(f5307,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5281,f173])).

fof(f5281,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32 ),
    inference(trivial_inequality_removal,[],[f5254])).

fof(f5254,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f173])).

fof(f5306,plain,
    ( ~ spl9_357
    | spl9_100
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5305,f172,f122,f383,f3646])).

fof(f5305,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5253,f123])).

fof(f5253,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(superposition,[],[f539,f123])).

fof(f5304,plain,
    ( ~ spl9_653
    | spl9_262
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f5300,f295,f172,f1060,f5302])).

fof(f5300,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f5252,f296])).

fof(f5252,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_32
    | ~ spl9_74 ),
    inference(superposition,[],[f539,f296])).

fof(f5299,plain,
    ( ~ spl9_651
    | spl9_226
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f5295,f266,f172,f910,f5297])).

fof(f5295,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f5251,f267])).

fof(f5251,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_32
    | ~ spl9_62 ),
    inference(superposition,[],[f539,f267])).

fof(f5294,plain,
    ( ~ spl9_649
    | spl9_250
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f5290,f286,f172,f1010,f5292])).

fof(f5290,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f5250,f287])).

fof(f5250,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_32
    | ~ spl9_70 ),
    inference(superposition,[],[f539,f287])).

fof(f5289,plain,
    ( ~ spl9_647
    | spl9_1
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f5285,f358,f172,f88,f5287])).

fof(f5285,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f5284,f89])).

fof(f5284,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f5248,f359])).

fof(f5248,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_32
    | ~ spl9_96 ),
    inference(superposition,[],[f539,f359])).

fof(f5283,plain,
    ( spl9_140
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5282,f172,f551])).

fof(f5282,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5247,f173])).

fof(f5247,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f173,f539])).

fof(f5246,plain,
    ( spl9_340
    | ~ spl9_293
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5185,f303,f168,f3298,f3526])).

fof(f3298,plain,
    ( spl9_293
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).

fof(f5185,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f509,f362])).

fof(f509,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_30 ),
    inference(superposition,[],[f86,f169])).

fof(f5245,plain,
    ( spl9_336
    | ~ spl9_293
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f5183,f303,f168,f3298,f3506])).

fof(f5183,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f509,f352])).

fof(f5244,plain,
    ( ~ spl9_645
    | spl9_204
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5243,f247,f168,f817,f5081])).

fof(f5081,plain,
    ( spl9_645
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_645])])).

fof(f5243,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f5181,f248])).

fof(f5181,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(superposition,[],[f509,f248])).

fof(f5242,plain,
    ( ~ spl9_643
    | spl9_198
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5241,f243,f168,f792,f5076])).

fof(f5076,plain,
    ( spl9_643
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_643])])).

fof(f5241,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f5180,f244])).

fof(f5180,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(superposition,[],[f509,f244])).

fof(f5240,plain,
    ( ~ spl9_641
    | spl9_192
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5239,f239,f168,f767,f5071])).

fof(f5071,plain,
    ( spl9_641
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_641])])).

fof(f5239,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f5179,f240])).

fof(f5179,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(superposition,[],[f509,f240])).

fof(f5238,plain,
    ( ~ spl9_639
    | spl9_186
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5237,f235,f168,f742,f5066])).

fof(f5066,plain,
    ( spl9_639
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_639])])).

fof(f5237,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f5178,f236])).

fof(f5178,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(superposition,[],[f509,f236])).

fof(f5236,plain,
    ( ~ spl9_637
    | spl9_180
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5235,f231,f168,f717,f5061])).

fof(f5061,plain,
    ( spl9_637
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_637])])).

fof(f5235,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f5177,f232])).

fof(f5177,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(superposition,[],[f509,f232])).

fof(f5234,plain,
    ( ~ spl9_635
    | spl9_174
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5233,f227,f168,f692,f5056])).

fof(f5056,plain,
    ( spl9_635
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_635])])).

fof(f5233,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f5176,f228])).

fof(f5176,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(superposition,[],[f509,f228])).

fof(f5232,plain,
    ( ~ spl9_633
    | spl9_166
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5231,f223,f168,f658,f5051])).

fof(f5051,plain,
    ( spl9_633
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_633])])).

fof(f5231,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f5175,f224])).

fof(f5175,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(superposition,[],[f509,f224])).

fof(f5230,plain,
    ( ~ spl9_631
    | spl9_160
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5229,f219,f168,f633,f5046])).

fof(f5046,plain,
    ( spl9_631
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_631])])).

fof(f5229,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f5174,f220])).

fof(f5174,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(superposition,[],[f509,f220])).

fof(f5228,plain,
    ( ~ spl9_629
    | spl9_154
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5227,f215,f168,f608,f5041])).

fof(f5041,plain,
    ( spl9_629
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_629])])).

fof(f5227,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f5173,f216])).

fof(f5173,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(superposition,[],[f509,f216])).

fof(f5226,plain,
    ( ~ spl9_627
    | spl9_222
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5225,f262,f168,f892,f5036])).

fof(f5036,plain,
    ( spl9_627
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_627])])).

fof(f5225,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f5172,f263])).

fof(f5172,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(superposition,[],[f509,f263])).

fof(f5224,plain,
    ( ~ spl9_625
    | spl9_216
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5223,f258,f168,f867,f5031])).

fof(f5031,plain,
    ( spl9_625
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_625])])).

fof(f5223,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f5171,f259])).

fof(f5171,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(superposition,[],[f509,f259])).

fof(f5222,plain,
    ( ~ spl9_623
    | spl9_210
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5221,f254,f168,f842,f5026])).

fof(f5026,plain,
    ( spl9_623
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_623])])).

fof(f5221,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f5170,f255])).

fof(f5170,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(superposition,[],[f509,f255])).

fof(f5220,plain,
    ( ~ spl9_621
    | spl9_258
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5219,f291,f168,f1042,f5021])).

fof(f5021,plain,
    ( spl9_621
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_621])])).

fof(f5219,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f5169,f292])).

fof(f5169,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(superposition,[],[f509,f292])).

fof(f5218,plain,
    ( ~ spl9_569
    | spl9_128
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5217,f168,f162,f499,f4736])).

fof(f4736,plain,
    ( spl9_569
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_569])])).

fof(f5217,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5168,f163])).

fof(f5168,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f163])).

fof(f5216,plain,
    ( ~ spl9_521
    | spl9_122
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5215,f168,f158,f474,f4473])).

fof(f4473,plain,
    ( spl9_521
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_521])])).

fof(f5215,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5167,f159])).

fof(f5167,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f159])).

fof(f5214,plain,
    ( ~ spl9_619
    | spl9_246
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5213,f282,f168,f992,f5012])).

fof(f5012,plain,
    ( spl9_619
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_619])])).

fof(f5213,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f5166,f283])).

fof(f5166,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(superposition,[],[f509,f283])).

fof(f5212,plain,
    ( ~ spl9_471
    | spl9_116
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5211,f168,f154,f449,f4207])).

fof(f4207,plain,
    ( spl9_471
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_471])])).

fof(f5211,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5165,f155])).

fof(f5165,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f155])).

fof(f5210,plain,
    ( ~ spl9_419
    | spl9_110
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5209,f168,f150,f424,f3938])).

fof(f3938,plain,
    ( spl9_419
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_419])])).

fof(f5209,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5164,f151])).

fof(f5164,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f151])).

fof(f5208,plain,
    ( ~ spl9_617
    | spl9_234
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5207,f270,f168,f942,f5003])).

fof(f5003,plain,
    ( spl9_617
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_617])])).

fof(f5207,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f5163,f271])).

fof(f5163,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(superposition,[],[f509,f271])).

fof(f5206,plain,
    ( ~ spl9_615
    | spl9_148
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f5205,f179,f168,f583,f4998])).

fof(f5205,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f5162,f180])).

fof(f5162,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(superposition,[],[f509,f180])).

fof(f5204,plain,
    ( spl9_134
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5203,f168,f524])).

fof(f5203,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5186,f169])).

fof(f5186,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30 ),
    inference(trivial_inequality_removal,[],[f5161])).

fof(f5161,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f169])).

fof(f5202,plain,
    ( ~ spl9_613
    | spl9_240
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f5201,f274,f168,f967,f4991])).

fof(f4991,plain,
    ( spl9_613
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_613])])).

fof(f5201,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f5160,f275])).

fof(f5160,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(superposition,[],[f509,f275])).

fof(f5200,plain,
    ( ~ spl9_611
    | spl9_142
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f5199,f172,f168,f558,f4986])).

fof(f5199,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f5159,f173])).

fof(f5159,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(superposition,[],[f509,f173])).

fof(f5198,plain,
    ( ~ spl9_361
    | spl9_102
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5197,f168,f122,f390,f3656])).

fof(f3656,plain,
    ( spl9_361
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_361])])).

fof(f5197,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5158,f123])).

fof(f5158,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(superposition,[],[f509,f123])).

fof(f5196,plain,
    ( ~ spl9_609
    | spl9_264
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f5195,f295,f168,f1067,f4979])).

fof(f4979,plain,
    ( spl9_609
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_609])])).

fof(f5195,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f5157,f296])).

fof(f5157,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(superposition,[],[f509,f296])).

fof(f5194,plain,
    ( ~ spl9_607
    | spl9_228
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f5193,f266,f168,f917,f4974])).

fof(f4974,plain,
    ( spl9_607
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_607])])).

fof(f5193,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f5156,f267])).

fof(f5156,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(superposition,[],[f509,f267])).

fof(f5192,plain,
    ( ~ spl9_605
    | spl9_252
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f5191,f286,f168,f1017,f4969])).

fof(f4969,plain,
    ( spl9_605
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_605])])).

fof(f5191,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f5155,f287])).

fof(f5155,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(superposition,[],[f509,f287])).

fof(f5190,plain,
    ( ~ spl9_603
    | spl9_2
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f5189,f358,f168,f3555,f4964])).

fof(f4964,plain,
    ( spl9_603
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_603])])).

fof(f5189,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f5153,f359])).

fof(f5153,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(superposition,[],[f509,f359])).

fof(f5188,plain,
    ( spl9_134
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5187,f168,f524])).

fof(f5187,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f5152,f169])).

fof(f5152,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f169,f509])).

fof(f5151,plain,
    ( ~ spl9_96
    | ~ spl9_344 ),
    inference(avatar_contradiction_clause,[],[f5086])).

fof(f5086,plain,
    ( $false
    | ~ spl9_96
    | ~ spl9_344 ),
    inference(unit_resulting_resolution,[],[f359,f3553])).

fof(f3553,plain,
    ( ! [X8,X9] : k1_mcart_1(sK3) != k4_tarski(X8,X9)
    | ~ spl9_344 ),
    inference(avatar_component_clause,[],[f3552])).

fof(f3552,plain,
    ( spl9_344
  <=> ! [X9,X8] : k1_mcart_1(sK3) != k4_tarski(X8,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_344])])).

fof(f5150,plain,
    ( ~ spl9_96
    | ~ spl9_344 ),
    inference(avatar_contradiction_clause,[],[f5149])).

fof(f5149,plain,
    ( $false
    | ~ spl9_96
    | ~ spl9_344 ),
    inference(trivial_inequality_removal,[],[f5116])).

fof(f5116,plain,
    ( k1_mcart_1(sK3) != k1_mcart_1(sK3)
    | ~ spl9_96
    | ~ spl9_344 ),
    inference(superposition,[],[f3553,f359])).

fof(f5085,plain,
    ( spl9_338
    | ~ spl9_293
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4957,f303,f168,f3298,f3522])).

fof(f4957,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f505,f362])).

fof(f505,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_30 ),
    inference(superposition,[],[f82,f169])).

fof(f5084,plain,
    ( spl9_334
    | ~ spl9_293
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4955,f303,f168,f3298,f3502])).

fof(f4955,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f505,f352])).

fof(f5083,plain,
    ( ~ spl9_645
    | spl9_202
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f5079,f247,f168,f810,f5081])).

fof(f5079,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4953,f248])).

fof(f4953,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_30
    | ~ spl9_54 ),
    inference(superposition,[],[f505,f248])).

fof(f5078,plain,
    ( ~ spl9_643
    | spl9_196
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f5074,f243,f168,f785,f5076])).

fof(f5074,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4952,f244])).

fof(f4952,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_30
    | ~ spl9_52 ),
    inference(superposition,[],[f505,f244])).

fof(f5073,plain,
    ( ~ spl9_641
    | spl9_190
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f5069,f239,f168,f760,f5071])).

fof(f5069,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4951,f240])).

fof(f4951,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_30
    | ~ spl9_50 ),
    inference(superposition,[],[f505,f240])).

fof(f5068,plain,
    ( ~ spl9_639
    | spl9_184
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f5064,f235,f168,f735,f5066])).

fof(f5064,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4950,f236])).

fof(f4950,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(superposition,[],[f505,f236])).

fof(f5063,plain,
    ( ~ spl9_637
    | spl9_178
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f5059,f231,f168,f710,f5061])).

fof(f5059,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4949,f232])).

fof(f4949,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(superposition,[],[f505,f232])).

fof(f5058,plain,
    ( ~ spl9_635
    | spl9_172
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f5054,f227,f168,f685,f5056])).

fof(f5054,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4948,f228])).

fof(f4948,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_30
    | ~ spl9_44 ),
    inference(superposition,[],[f505,f228])).

fof(f5053,plain,
    ( ~ spl9_633
    | spl9_164
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f5049,f223,f168,f651,f5051])).

fof(f5049,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4947,f224])).

fof(f4947,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_30
    | ~ spl9_42 ),
    inference(superposition,[],[f505,f224])).

fof(f5048,plain,
    ( ~ spl9_631
    | spl9_158
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f5044,f219,f168,f626,f5046])).

fof(f5044,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4946,f220])).

fof(f4946,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_30
    | ~ spl9_40 ),
    inference(superposition,[],[f505,f220])).

fof(f5043,plain,
    ( ~ spl9_629
    | spl9_152
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f5039,f215,f168,f601,f5041])).

fof(f5039,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4945,f216])).

fof(f4945,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(superposition,[],[f505,f216])).

fof(f5038,plain,
    ( ~ spl9_627
    | spl9_220
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f5034,f262,f168,f885,f5036])).

fof(f5034,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4944,f263])).

fof(f4944,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(superposition,[],[f505,f263])).

fof(f5033,plain,
    ( ~ spl9_625
    | spl9_214
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f5029,f258,f168,f860,f5031])).

fof(f5029,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4943,f259])).

fof(f4943,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_30
    | ~ spl9_58 ),
    inference(superposition,[],[f505,f259])).

fof(f5028,plain,
    ( ~ spl9_623
    | spl9_208
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f5024,f254,f168,f835,f5026])).

fof(f5024,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4942,f255])).

fof(f4942,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(superposition,[],[f505,f255])).

fof(f5023,plain,
    ( ~ spl9_621
    | spl9_256
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f5019,f291,f168,f1035,f5021])).

fof(f5019,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4941,f292])).

fof(f4941,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_30
    | ~ spl9_72 ),
    inference(superposition,[],[f505,f292])).

fof(f5018,plain,
    ( ~ spl9_569
    | spl9_126
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5017,f168,f162,f492,f4736])).

fof(f5017,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4940,f163])).

fof(f4940,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f163])).

fof(f5016,plain,
    ( ~ spl9_521
    | spl9_120
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5015,f168,f158,f467,f4473])).

fof(f5015,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4939,f159])).

fof(f4939,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f159])).

fof(f5014,plain,
    ( ~ spl9_619
    | spl9_244
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f5010,f282,f168,f985,f5012])).

fof(f5010,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4938,f283])).

fof(f4938,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(superposition,[],[f505,f283])).

fof(f5009,plain,
    ( ~ spl9_471
    | spl9_114
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5008,f168,f154,f442,f4207])).

fof(f5008,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4937,f155])).

fof(f4937,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f155])).

fof(f5007,plain,
    ( ~ spl9_419
    | spl9_108
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f5006,f168,f150,f417,f3938])).

fof(f5006,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4936,f151])).

fof(f4936,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f151])).

fof(f5005,plain,
    ( ~ spl9_617
    | spl9_232
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f5001,f270,f168,f935,f5003])).

fof(f5001,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4935,f271])).

fof(f4935,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_30
    | ~ spl9_64 ),
    inference(superposition,[],[f505,f271])).

fof(f5000,plain,
    ( ~ spl9_615
    | spl9_146
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4996,f179,f168,f576,f4998])).

fof(f4996,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4934,f180])).

fof(f4934,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_30
    | ~ spl9_34 ),
    inference(superposition,[],[f505,f180])).

fof(f4995,plain,
    ( spl9_132
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4994,f168,f517])).

fof(f4994,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4958,f169])).

fof(f4958,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30 ),
    inference(trivial_inequality_removal,[],[f4933])).

fof(f4933,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f169])).

fof(f4993,plain,
    ( ~ spl9_613
    | spl9_238
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4989,f274,f168,f960,f4991])).

fof(f4989,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4932,f275])).

fof(f4932,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_30
    | ~ spl9_66 ),
    inference(superposition,[],[f505,f275])).

fof(f4988,plain,
    ( ~ spl9_611
    | spl9_140
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4984,f172,f168,f551,f4986])).

fof(f4984,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4931,f173])).

fof(f4931,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(superposition,[],[f505,f173])).

fof(f4983,plain,
    ( ~ spl9_361
    | spl9_100
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4982,f168,f122,f383,f3656])).

fof(f4982,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4930,f123])).

fof(f4930,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(superposition,[],[f505,f123])).

fof(f4981,plain,
    ( ~ spl9_609
    | spl9_262
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4977,f295,f168,f1060,f4979])).

fof(f4977,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4929,f296])).

fof(f4929,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_30
    | ~ spl9_74 ),
    inference(superposition,[],[f505,f296])).

fof(f4976,plain,
    ( ~ spl9_607
    | spl9_226
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4972,f266,f168,f910,f4974])).

fof(f4972,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4928,f267])).

fof(f4928,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_30
    | ~ spl9_62 ),
    inference(superposition,[],[f505,f267])).

fof(f4971,plain,
    ( ~ spl9_605
    | spl9_250
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4967,f286,f168,f1010,f4969])).

fof(f4967,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4927,f287])).

fof(f4927,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_30
    | ~ spl9_70 ),
    inference(superposition,[],[f505,f287])).

fof(f4966,plain,
    ( ~ spl9_603
    | spl9_1
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4962,f358,f168,f88,f4964])).

fof(f4962,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f4961,f89])).

fof(f4961,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4925,f359])).

fof(f4925,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_30
    | ~ spl9_96 ),
    inference(superposition,[],[f505,f359])).

fof(f4960,plain,
    ( spl9_132
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4959,f168,f517])).

fof(f4959,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4924,f169])).

fof(f4924,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f169,f505])).

fof(f4923,plain,
    ( spl9_340
    | ~ spl9_307
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4862,f303,f162,f3333,f3526])).

fof(f3333,plain,
    ( spl9_307
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_307])])).

fof(f4862,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f484,f362])).

fof(f484,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_28 ),
    inference(superposition,[],[f86,f163])).

fof(f4922,plain,
    ( spl9_336
    | ~ spl9_307
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4860,f303,f162,f3333,f3506])).

fof(f4860,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f484,f352])).

fof(f4921,plain,
    ( ~ spl9_601
    | spl9_204
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4920,f247,f162,f817,f4824])).

fof(f4824,plain,
    ( spl9_601
  <=> sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_601])])).

fof(f4920,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4858,f248])).

fof(f4858,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(superposition,[],[f484,f248])).

fof(f4919,plain,
    ( ~ spl9_599
    | spl9_198
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4918,f243,f162,f792,f4819])).

fof(f4819,plain,
    ( spl9_599
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_599])])).

fof(f4918,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4857,f244])).

fof(f4857,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(superposition,[],[f484,f244])).

fof(f4917,plain,
    ( ~ spl9_597
    | spl9_192
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4916,f239,f162,f767,f4814])).

fof(f4814,plain,
    ( spl9_597
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_597])])).

fof(f4916,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4856,f240])).

fof(f4856,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(superposition,[],[f484,f240])).

fof(f4915,plain,
    ( ~ spl9_595
    | spl9_186
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4914,f235,f162,f742,f4809])).

fof(f4809,plain,
    ( spl9_595
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_595])])).

fof(f4914,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4855,f236])).

fof(f4855,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(superposition,[],[f484,f236])).

fof(f4913,plain,
    ( ~ spl9_593
    | spl9_180
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4912,f231,f162,f717,f4804])).

fof(f4804,plain,
    ( spl9_593
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_593])])).

fof(f4912,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4854,f232])).

fof(f4854,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(superposition,[],[f484,f232])).

fof(f4911,plain,
    ( ~ spl9_591
    | spl9_174
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4910,f227,f162,f692,f4799])).

fof(f4799,plain,
    ( spl9_591
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_591])])).

fof(f4910,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4853,f228])).

fof(f4853,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(superposition,[],[f484,f228])).

fof(f4909,plain,
    ( ~ spl9_589
    | spl9_166
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4908,f223,f162,f658,f4794])).

fof(f4794,plain,
    ( spl9_589
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_589])])).

fof(f4908,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4852,f224])).

fof(f4852,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(superposition,[],[f484,f224])).

fof(f4907,plain,
    ( ~ spl9_587
    | spl9_160
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4906,f219,f162,f633,f4789])).

fof(f4789,plain,
    ( spl9_587
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_587])])).

fof(f4906,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4851,f220])).

fof(f4851,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(superposition,[],[f484,f220])).

fof(f4905,plain,
    ( ~ spl9_585
    | spl9_154
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4904,f215,f162,f608,f4784])).

fof(f4784,plain,
    ( spl9_585
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_585])])).

fof(f4904,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4850,f216])).

fof(f4850,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(superposition,[],[f484,f216])).

fof(f4903,plain,
    ( ~ spl9_583
    | spl9_222
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4902,f262,f162,f892,f4779])).

fof(f4779,plain,
    ( spl9_583
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_583])])).

fof(f4902,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4849,f263])).

fof(f4849,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(superposition,[],[f484,f263])).

fof(f4901,plain,
    ( ~ spl9_581
    | spl9_216
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4900,f258,f162,f867,f4774])).

fof(f4774,plain,
    ( spl9_581
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_581])])).

fof(f4900,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4848,f259])).

fof(f4848,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(superposition,[],[f484,f259])).

fof(f4899,plain,
    ( ~ spl9_579
    | spl9_210
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4898,f254,f162,f842,f4769])).

fof(f4769,plain,
    ( spl9_579
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_579])])).

fof(f4898,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4847,f255])).

fof(f4847,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(superposition,[],[f484,f255])).

fof(f4897,plain,
    ( ~ spl9_577
    | spl9_258
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4896,f291,f162,f1042,f4764])).

fof(f4764,plain,
    ( spl9_577
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_577])])).

fof(f4896,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4846,f292])).

fof(f4846,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(superposition,[],[f484,f292])).

fof(f4895,plain,
    ( spl9_128
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4894,f162,f499])).

fof(f4894,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4863,f163])).

fof(f4863,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28 ),
    inference(trivial_inequality_removal,[],[f4845])).

fof(f4845,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28 ),
    inference(superposition,[],[f484,f163])).

fof(f4893,plain,
    ( ~ spl9_529
    | spl9_122
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4892,f162,f158,f474,f4499])).

fof(f4499,plain,
    ( spl9_529
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_529])])).

fof(f4892,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4844,f159])).

fof(f4844,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(superposition,[],[f484,f159])).

fof(f4891,plain,
    ( ~ spl9_575
    | spl9_246
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4890,f282,f162,f992,f4755])).

fof(f4755,plain,
    ( spl9_575
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_575])])).

fof(f4890,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4843,f283])).

fof(f4843,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(superposition,[],[f484,f283])).

fof(f4889,plain,
    ( ~ spl9_481
    | spl9_116
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4888,f162,f154,f449,f4236])).

fof(f4236,plain,
    ( spl9_481
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_481])])).

fof(f4888,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4842,f155])).

fof(f4842,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(superposition,[],[f484,f155])).

fof(f4887,plain,
    ( ~ spl9_431
    | spl9_110
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4886,f162,f150,f424,f3970])).

fof(f3970,plain,
    ( spl9_431
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_431])])).

fof(f4886,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4841,f151])).

fof(f4841,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(superposition,[],[f484,f151])).

fof(f4885,plain,
    ( ~ spl9_573
    | spl9_234
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4884,f270,f162,f942,f4746])).

fof(f4746,plain,
    ( spl9_573
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_573])])).

fof(f4884,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4840,f271])).

fof(f4840,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(superposition,[],[f484,f271])).

fof(f4883,plain,
    ( ~ spl9_571
    | spl9_148
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4882,f179,f162,f583,f4741])).

fof(f4882,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4839,f180])).

fof(f4839,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(superposition,[],[f484,f180])).

fof(f4881,plain,
    ( ~ spl9_569
    | spl9_134
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4880,f168,f162,f524,f4736])).

fof(f4880,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4838,f169])).

fof(f4838,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(superposition,[],[f484,f169])).

fof(f4879,plain,
    ( ~ spl9_567
    | spl9_240
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4878,f274,f162,f967,f4731])).

fof(f4731,plain,
    ( spl9_567
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_567])])).

fof(f4878,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4837,f275])).

fof(f4837,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(superposition,[],[f484,f275])).

fof(f4877,plain,
    ( ~ spl9_565
    | spl9_142
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4876,f172,f162,f558,f4726])).

fof(f4876,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4836,f173])).

fof(f4836,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(superposition,[],[f484,f173])).

fof(f4875,plain,
    ( ~ spl9_375
    | spl9_102
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4874,f162,f122,f390,f3691])).

fof(f3691,plain,
    ( spl9_375
  <=> sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_375])])).

fof(f4874,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4835,f123])).

fof(f4835,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(superposition,[],[f484,f123])).

fof(f4873,plain,
    ( ~ spl9_563
    | spl9_264
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4872,f295,f162,f1067,f4719])).

fof(f4719,plain,
    ( spl9_563
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_563])])).

fof(f4872,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4834,f296])).

fof(f4834,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(superposition,[],[f484,f296])).

fof(f4871,plain,
    ( ~ spl9_561
    | spl9_228
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4870,f266,f162,f917,f4714])).

fof(f4714,plain,
    ( spl9_561
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_561])])).

fof(f4870,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4833,f267])).

fof(f4833,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(superposition,[],[f484,f267])).

fof(f4869,plain,
    ( ~ spl9_559
    | spl9_252
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4868,f286,f162,f1017,f4709])).

fof(f4709,plain,
    ( spl9_559
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_559])])).

fof(f4868,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4832,f287])).

fof(f4832,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(superposition,[],[f484,f287])).

fof(f4867,plain,
    ( ~ spl9_557
    | spl9_2
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4866,f358,f162,f3555,f4704])).

fof(f4704,plain,
    ( spl9_557
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_557])])).

fof(f4866,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4830,f359])).

fof(f4830,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(superposition,[],[f484,f359])).

fof(f4865,plain,
    ( spl9_128
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4864,f162,f499])).

fof(f4864,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4829,f163])).

fof(f4829,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f163,f484])).

fof(f4828,plain,
    ( spl9_338
    | ~ spl9_307
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4697,f303,f162,f3333,f3522])).

fof(f4697,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f480,f362])).

fof(f480,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_28 ),
    inference(superposition,[],[f82,f163])).

fof(f4827,plain,
    ( spl9_334
    | ~ spl9_307
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4695,f303,f162,f3333,f3502])).

fof(f4695,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f480,f352])).

fof(f4826,plain,
    ( ~ spl9_601
    | spl9_202
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4822,f247,f162,f810,f4824])).

fof(f4822,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4693,f248])).

fof(f4693,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_28
    | ~ spl9_54 ),
    inference(superposition,[],[f480,f248])).

fof(f4821,plain,
    ( ~ spl9_599
    | spl9_196
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4817,f243,f162,f785,f4819])).

fof(f4817,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4692,f244])).

fof(f4692,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_28
    | ~ spl9_52 ),
    inference(superposition,[],[f480,f244])).

fof(f4816,plain,
    ( ~ spl9_597
    | spl9_190
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4812,f239,f162,f760,f4814])).

fof(f4812,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4691,f240])).

fof(f4691,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(superposition,[],[f480,f240])).

fof(f4811,plain,
    ( ~ spl9_595
    | spl9_184
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4807,f235,f162,f735,f4809])).

fof(f4807,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4690,f236])).

fof(f4690,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_28
    | ~ spl9_48 ),
    inference(superposition,[],[f480,f236])).

fof(f4806,plain,
    ( ~ spl9_593
    | spl9_178
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4802,f231,f162,f710,f4804])).

fof(f4802,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4689,f232])).

fof(f4689,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_28
    | ~ spl9_46 ),
    inference(superposition,[],[f480,f232])).

fof(f4801,plain,
    ( ~ spl9_591
    | spl9_172
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4797,f227,f162,f685,f4799])).

fof(f4797,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4688,f228])).

fof(f4688,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_28
    | ~ spl9_44 ),
    inference(superposition,[],[f480,f228])).

fof(f4796,plain,
    ( ~ spl9_589
    | spl9_164
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4792,f223,f162,f651,f4794])).

fof(f4792,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4687,f224])).

fof(f4687,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_28
    | ~ spl9_42 ),
    inference(superposition,[],[f480,f224])).

fof(f4791,plain,
    ( ~ spl9_587
    | spl9_158
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4787,f219,f162,f626,f4789])).

fof(f4787,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4686,f220])).

fof(f4686,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_28
    | ~ spl9_40 ),
    inference(superposition,[],[f480,f220])).

fof(f4786,plain,
    ( ~ spl9_585
    | spl9_152
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4782,f215,f162,f601,f4784])).

fof(f4782,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4685,f216])).

fof(f4685,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_28
    | ~ spl9_38 ),
    inference(superposition,[],[f480,f216])).

fof(f4781,plain,
    ( ~ spl9_583
    | spl9_220
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4777,f262,f162,f885,f4779])).

fof(f4777,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4684,f263])).

fof(f4684,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_28
    | ~ spl9_60 ),
    inference(superposition,[],[f480,f263])).

fof(f4776,plain,
    ( ~ spl9_581
    | spl9_214
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4772,f258,f162,f860,f4774])).

fof(f4772,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4683,f259])).

fof(f4683,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_28
    | ~ spl9_58 ),
    inference(superposition,[],[f480,f259])).

fof(f4771,plain,
    ( ~ spl9_579
    | spl9_208
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4767,f254,f162,f835,f4769])).

fof(f4767,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4682,f255])).

fof(f4682,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_28
    | ~ spl9_56 ),
    inference(superposition,[],[f480,f255])).

fof(f4766,plain,
    ( ~ spl9_577
    | spl9_256
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4762,f291,f162,f1035,f4764])).

fof(f4762,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4681,f292])).

fof(f4681,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_28
    | ~ spl9_72 ),
    inference(superposition,[],[f480,f292])).

fof(f4761,plain,
    ( spl9_126
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4760,f162,f492])).

fof(f4760,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4698,f163])).

fof(f4698,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28 ),
    inference(trivial_inequality_removal,[],[f4680])).

fof(f4680,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28 ),
    inference(superposition,[],[f480,f163])).

fof(f4759,plain,
    ( ~ spl9_529
    | spl9_120
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4758,f162,f158,f467,f4499])).

fof(f4758,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4679,f159])).

fof(f4679,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(superposition,[],[f480,f159])).

fof(f4757,plain,
    ( ~ spl9_575
    | spl9_244
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4753,f282,f162,f985,f4755])).

fof(f4753,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4678,f283])).

fof(f4678,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_28
    | ~ spl9_68 ),
    inference(superposition,[],[f480,f283])).

fof(f4752,plain,
    ( ~ spl9_481
    | spl9_114
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4751,f162,f154,f442,f4236])).

fof(f4751,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4677,f155])).

fof(f4677,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(superposition,[],[f480,f155])).

fof(f4750,plain,
    ( ~ spl9_431
    | spl9_108
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4749,f162,f150,f417,f3970])).

fof(f4749,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4676,f151])).

fof(f4676,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(superposition,[],[f480,f151])).

fof(f4748,plain,
    ( ~ spl9_573
    | spl9_232
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4744,f270,f162,f935,f4746])).

fof(f4744,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4675,f271])).

fof(f4675,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(superposition,[],[f480,f271])).

fof(f4743,plain,
    ( ~ spl9_571
    | spl9_146
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4739,f179,f162,f576,f4741])).

fof(f4739,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4674,f180])).

fof(f4674,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_28
    | ~ spl9_34 ),
    inference(superposition,[],[f480,f180])).

fof(f4738,plain,
    ( ~ spl9_569
    | spl9_132
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4734,f168,f162,f517,f4736])).

fof(f4734,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4673,f169])).

fof(f4673,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_28
    | ~ spl9_30 ),
    inference(superposition,[],[f480,f169])).

fof(f4733,plain,
    ( ~ spl9_567
    | spl9_238
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4729,f274,f162,f960,f4731])).

fof(f4729,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4672,f275])).

fof(f4672,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_28
    | ~ spl9_66 ),
    inference(superposition,[],[f480,f275])).

fof(f4728,plain,
    ( ~ spl9_565
    | spl9_140
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4724,f172,f162,f551,f4726])).

fof(f4724,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4671,f173])).

fof(f4671,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_28
    | ~ spl9_32 ),
    inference(superposition,[],[f480,f173])).

fof(f4723,plain,
    ( ~ spl9_375
    | spl9_100
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4722,f162,f122,f383,f3691])).

fof(f4722,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4670,f123])).

fof(f4670,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(superposition,[],[f480,f123])).

fof(f4721,plain,
    ( ~ spl9_563
    | spl9_262
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4717,f295,f162,f1060,f4719])).

fof(f4717,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4669,f296])).

fof(f4669,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_28
    | ~ spl9_74 ),
    inference(superposition,[],[f480,f296])).

fof(f4716,plain,
    ( ~ spl9_561
    | spl9_226
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4712,f266,f162,f910,f4714])).

fof(f4712,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4668,f267])).

fof(f4668,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_28
    | ~ spl9_62 ),
    inference(superposition,[],[f480,f267])).

fof(f4711,plain,
    ( ~ spl9_559
    | spl9_250
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4707,f286,f162,f1010,f4709])).

fof(f4707,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4667,f287])).

fof(f4667,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_28
    | ~ spl9_70 ),
    inference(superposition,[],[f480,f287])).

fof(f4706,plain,
    ( ~ spl9_557
    | spl9_1
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4702,f358,f162,f88,f4704])).

fof(f4702,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f4701,f89])).

fof(f4701,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4665,f359])).

fof(f4665,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(superposition,[],[f480,f359])).

fof(f4700,plain,
    ( spl9_126
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4699,f162,f492])).

fof(f4699,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4664,f163])).

fof(f4664,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f163,f480])).

fof(f4663,plain,
    ( spl9_340
    | ~ spl9_305
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4602,f303,f158,f3328,f3526])).

fof(f3328,plain,
    ( spl9_305
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_305])])).

fof(f4602,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f459,f362])).

fof(f459,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_26 ),
    inference(superposition,[],[f86,f159])).

fof(f4662,plain,
    ( spl9_336
    | ~ spl9_305
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4600,f303,f158,f3328,f3506])).

fof(f4600,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f459,f352])).

fof(f4661,plain,
    ( ~ spl9_555
    | spl9_204
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4660,f247,f158,f817,f4564])).

fof(f4564,plain,
    ( spl9_555
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_555])])).

fof(f4660,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4598,f248])).

fof(f4598,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(superposition,[],[f459,f248])).

fof(f4659,plain,
    ( ~ spl9_553
    | spl9_198
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4658,f243,f158,f792,f4559])).

fof(f4559,plain,
    ( spl9_553
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_553])])).

fof(f4658,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4597,f244])).

fof(f4597,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(superposition,[],[f459,f244])).

fof(f4657,plain,
    ( ~ spl9_551
    | spl9_192
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4656,f239,f158,f767,f4554])).

fof(f4554,plain,
    ( spl9_551
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_551])])).

fof(f4656,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4596,f240])).

fof(f4596,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(superposition,[],[f459,f240])).

fof(f4655,plain,
    ( ~ spl9_549
    | spl9_186
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4654,f235,f158,f742,f4549])).

fof(f4549,plain,
    ( spl9_549
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_549])])).

fof(f4654,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4595,f236])).

fof(f4595,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(superposition,[],[f459,f236])).

fof(f4653,plain,
    ( ~ spl9_547
    | spl9_180
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4652,f231,f158,f717,f4544])).

fof(f4544,plain,
    ( spl9_547
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_547])])).

fof(f4652,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4594,f232])).

fof(f4594,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(superposition,[],[f459,f232])).

fof(f4651,plain,
    ( ~ spl9_545
    | spl9_174
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4650,f227,f158,f692,f4539])).

fof(f4539,plain,
    ( spl9_545
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_545])])).

fof(f4650,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4593,f228])).

fof(f4593,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(superposition,[],[f459,f228])).

fof(f4649,plain,
    ( ~ spl9_543
    | spl9_166
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4648,f223,f158,f658,f4534])).

fof(f4534,plain,
    ( spl9_543
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_543])])).

fof(f4648,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4592,f224])).

fof(f4592,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(superposition,[],[f459,f224])).

fof(f4647,plain,
    ( ~ spl9_541
    | spl9_160
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4646,f219,f158,f633,f4529])).

fof(f4529,plain,
    ( spl9_541
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_541])])).

fof(f4646,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4591,f220])).

fof(f4591,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(superposition,[],[f459,f220])).

fof(f4645,plain,
    ( ~ spl9_539
    | spl9_154
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4644,f215,f158,f608,f4524])).

fof(f4524,plain,
    ( spl9_539
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_539])])).

fof(f4644,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4590,f216])).

fof(f4590,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(superposition,[],[f459,f216])).

fof(f4643,plain,
    ( ~ spl9_537
    | spl9_222
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4642,f262,f158,f892,f4519])).

fof(f4519,plain,
    ( spl9_537
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_537])])).

fof(f4642,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4589,f263])).

fof(f4589,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(superposition,[],[f459,f263])).

fof(f4641,plain,
    ( ~ spl9_535
    | spl9_216
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4640,f258,f158,f867,f4514])).

fof(f4514,plain,
    ( spl9_535
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_535])])).

fof(f4640,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4588,f259])).

fof(f4588,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(superposition,[],[f459,f259])).

fof(f4639,plain,
    ( ~ spl9_533
    | spl9_210
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4638,f254,f158,f842,f4509])).

fof(f4509,plain,
    ( spl9_533
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_533])])).

fof(f4638,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4587,f255])).

fof(f4587,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(superposition,[],[f459,f255])).

fof(f4637,plain,
    ( ~ spl9_531
    | spl9_258
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4636,f291,f158,f1042,f4504])).

fof(f4504,plain,
    ( spl9_531
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_531])])).

fof(f4636,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4586,f292])).

fof(f4586,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(superposition,[],[f459,f292])).

fof(f4635,plain,
    ( ~ spl9_529
    | spl9_128
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4634,f162,f158,f499,f4499])).

fof(f4634,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4585,f163])).

fof(f4585,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(superposition,[],[f459,f163])).

fof(f4633,plain,
    ( spl9_122
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4632,f158,f474])).

fof(f4632,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4603,f159])).

fof(f4603,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26 ),
    inference(trivial_inequality_removal,[],[f4584])).

fof(f4584,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26 ),
    inference(superposition,[],[f459,f159])).

fof(f4631,plain,
    ( ~ spl9_527
    | spl9_246
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4630,f282,f158,f992,f4492])).

fof(f4492,plain,
    ( spl9_527
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_527])])).

fof(f4630,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4583,f283])).

fof(f4583,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(superposition,[],[f459,f283])).

fof(f4629,plain,
    ( ~ spl9_479
    | spl9_116
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4628,f158,f154,f449,f4231])).

fof(f4231,plain,
    ( spl9_479
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_479])])).

fof(f4628,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4582,f155])).

fof(f4582,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(superposition,[],[f459,f155])).

fof(f4627,plain,
    ( ~ spl9_429
    | spl9_110
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4626,f158,f150,f424,f3965])).

fof(f3965,plain,
    ( spl9_429
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_429])])).

fof(f4626,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4581,f151])).

fof(f4581,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(superposition,[],[f459,f151])).

fof(f4625,plain,
    ( ~ spl9_525
    | spl9_234
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4624,f270,f158,f942,f4483])).

fof(f4483,plain,
    ( spl9_525
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_525])])).

fof(f4624,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4580,f271])).

fof(f4580,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(superposition,[],[f459,f271])).

fof(f4623,plain,
    ( ~ spl9_523
    | spl9_148
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4622,f179,f158,f583,f4478])).

fof(f4622,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4579,f180])).

fof(f4579,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(superposition,[],[f459,f180])).

fof(f4621,plain,
    ( ~ spl9_521
    | spl9_134
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4620,f168,f158,f524,f4473])).

fof(f4620,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4578,f169])).

fof(f4578,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(superposition,[],[f459,f169])).

fof(f4619,plain,
    ( ~ spl9_519
    | spl9_240
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4618,f274,f158,f967,f4468])).

fof(f4468,plain,
    ( spl9_519
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_519])])).

fof(f4618,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4577,f275])).

fof(f4577,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(superposition,[],[f459,f275])).

fof(f4617,plain,
    ( ~ spl9_517
    | spl9_142
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4616,f172,f158,f558,f4463])).

fof(f4616,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4576,f173])).

fof(f4576,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(superposition,[],[f459,f173])).

fof(f4615,plain,
    ( ~ spl9_373
    | spl9_102
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4614,f158,f122,f390,f3686])).

fof(f3686,plain,
    ( spl9_373
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_373])])).

fof(f4614,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4575,f123])).

fof(f4575,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(superposition,[],[f459,f123])).

fof(f4613,plain,
    ( ~ spl9_515
    | spl9_264
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4612,f295,f158,f1067,f4456])).

fof(f4456,plain,
    ( spl9_515
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_515])])).

fof(f4612,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4574,f296])).

fof(f4574,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(superposition,[],[f459,f296])).

fof(f4611,plain,
    ( ~ spl9_513
    | spl9_228
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4610,f266,f158,f917,f4451])).

fof(f4451,plain,
    ( spl9_513
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_513])])).

fof(f4610,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4573,f267])).

fof(f4573,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(superposition,[],[f459,f267])).

fof(f4609,plain,
    ( ~ spl9_511
    | spl9_252
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4608,f286,f158,f1017,f4446])).

fof(f4446,plain,
    ( spl9_511
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_511])])).

fof(f4608,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4572,f287])).

fof(f4572,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(superposition,[],[f459,f287])).

fof(f4607,plain,
    ( ~ spl9_509
    | spl9_2
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4606,f358,f158,f3555,f4441])).

fof(f4441,plain,
    ( spl9_509
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_509])])).

fof(f4606,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4570,f359])).

fof(f4570,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(superposition,[],[f459,f359])).

fof(f4605,plain,
    ( spl9_122
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4604,f158,f474])).

fof(f4604,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4569,f159])).

fof(f4569,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f159,f459])).

fof(f4568,plain,
    ( spl9_338
    | ~ spl9_305
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4434,f303,f158,f3328,f3522])).

fof(f4434,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f455,f362])).

fof(f455,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_26 ),
    inference(superposition,[],[f82,f159])).

fof(f4567,plain,
    ( spl9_334
    | ~ spl9_305
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4432,f303,f158,f3328,f3502])).

fof(f4432,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f455,f352])).

fof(f4566,plain,
    ( ~ spl9_555
    | spl9_202
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4562,f247,f158,f810,f4564])).

fof(f4562,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4430,f248])).

fof(f4430,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_26
    | ~ spl9_54 ),
    inference(superposition,[],[f455,f248])).

fof(f4561,plain,
    ( ~ spl9_553
    | spl9_196
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4557,f243,f158,f785,f4559])).

fof(f4557,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4429,f244])).

fof(f4429,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_26
    | ~ spl9_52 ),
    inference(superposition,[],[f455,f244])).

fof(f4556,plain,
    ( ~ spl9_551
    | spl9_190
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4552,f239,f158,f760,f4554])).

fof(f4552,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4428,f240])).

fof(f4428,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_26
    | ~ spl9_50 ),
    inference(superposition,[],[f455,f240])).

fof(f4551,plain,
    ( ~ spl9_549
    | spl9_184
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4547,f235,f158,f735,f4549])).

fof(f4547,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4427,f236])).

fof(f4427,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_26
    | ~ spl9_48 ),
    inference(superposition,[],[f455,f236])).

fof(f4546,plain,
    ( ~ spl9_547
    | spl9_178
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4542,f231,f158,f710,f4544])).

fof(f4542,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4426,f232])).

fof(f4426,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_26
    | ~ spl9_46 ),
    inference(superposition,[],[f455,f232])).

fof(f4541,plain,
    ( ~ spl9_545
    | spl9_172
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4537,f227,f158,f685,f4539])).

fof(f4537,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4425,f228])).

fof(f4425,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_26
    | ~ spl9_44 ),
    inference(superposition,[],[f455,f228])).

fof(f4536,plain,
    ( ~ spl9_543
    | spl9_164
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4532,f223,f158,f651,f4534])).

fof(f4532,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4424,f224])).

fof(f4424,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_26
    | ~ spl9_42 ),
    inference(superposition,[],[f455,f224])).

fof(f4531,plain,
    ( ~ spl9_541
    | spl9_158
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4527,f219,f158,f626,f4529])).

fof(f4527,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4423,f220])).

fof(f4423,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_26
    | ~ spl9_40 ),
    inference(superposition,[],[f455,f220])).

fof(f4526,plain,
    ( ~ spl9_539
    | spl9_152
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4522,f215,f158,f601,f4524])).

fof(f4522,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4422,f216])).

fof(f4422,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_26
    | ~ spl9_38 ),
    inference(superposition,[],[f455,f216])).

fof(f4521,plain,
    ( ~ spl9_537
    | spl9_220
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4517,f262,f158,f885,f4519])).

fof(f4517,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4421,f263])).

fof(f4421,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_26
    | ~ spl9_60 ),
    inference(superposition,[],[f455,f263])).

fof(f4516,plain,
    ( ~ spl9_535
    | spl9_214
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4512,f258,f158,f860,f4514])).

fof(f4512,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4420,f259])).

fof(f4420,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_26
    | ~ spl9_58 ),
    inference(superposition,[],[f455,f259])).

fof(f4511,plain,
    ( ~ spl9_533
    | spl9_208
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4507,f254,f158,f835,f4509])).

fof(f4507,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4419,f255])).

fof(f4419,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_26
    | ~ spl9_56 ),
    inference(superposition,[],[f455,f255])).

fof(f4506,plain,
    ( ~ spl9_531
    | spl9_256
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4502,f291,f158,f1035,f4504])).

fof(f4502,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4418,f292])).

fof(f4418,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_72 ),
    inference(superposition,[],[f455,f292])).

fof(f4501,plain,
    ( ~ spl9_529
    | spl9_126
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4497,f162,f158,f492,f4499])).

fof(f4497,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4417,f163])).

fof(f4417,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_28 ),
    inference(superposition,[],[f455,f163])).

fof(f4496,plain,
    ( spl9_120
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4495,f158,f467])).

fof(f4495,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4435,f159])).

fof(f4435,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26 ),
    inference(trivial_inequality_removal,[],[f4416])).

fof(f4416,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26 ),
    inference(superposition,[],[f455,f159])).

fof(f4494,plain,
    ( ~ spl9_527
    | spl9_244
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4490,f282,f158,f985,f4492])).

fof(f4490,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4415,f283])).

fof(f4415,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(superposition,[],[f455,f283])).

fof(f4489,plain,
    ( ~ spl9_479
    | spl9_114
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4488,f158,f154,f442,f4231])).

fof(f4488,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4414,f155])).

fof(f4414,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(superposition,[],[f455,f155])).

fof(f4487,plain,
    ( ~ spl9_429
    | spl9_108
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4486,f158,f150,f417,f3965])).

fof(f4486,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4413,f151])).

fof(f4413,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(superposition,[],[f455,f151])).

fof(f4485,plain,
    ( ~ spl9_525
    | spl9_232
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4481,f270,f158,f935,f4483])).

fof(f4481,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4412,f271])).

fof(f4412,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_26
    | ~ spl9_64 ),
    inference(superposition,[],[f455,f271])).

fof(f4480,plain,
    ( ~ spl9_523
    | spl9_146
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4476,f179,f158,f576,f4478])).

fof(f4476,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4411,f180])).

fof(f4411,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_26
    | ~ spl9_34 ),
    inference(superposition,[],[f455,f180])).

fof(f4475,plain,
    ( ~ spl9_521
    | spl9_132
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4471,f168,f158,f517,f4473])).

fof(f4471,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4410,f169])).

fof(f4410,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(superposition,[],[f455,f169])).

fof(f4470,plain,
    ( ~ spl9_519
    | spl9_238
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4466,f274,f158,f960,f4468])).

fof(f4466,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4409,f275])).

fof(f4409,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_26
    | ~ spl9_66 ),
    inference(superposition,[],[f455,f275])).

fof(f4465,plain,
    ( ~ spl9_517
    | spl9_140
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4461,f172,f158,f551,f4463])).

fof(f4461,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4408,f173])).

fof(f4408,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(superposition,[],[f455,f173])).

fof(f4460,plain,
    ( ~ spl9_373
    | spl9_100
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4459,f158,f122,f383,f3686])).

fof(f4459,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4407,f123])).

fof(f4407,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(superposition,[],[f455,f123])).

fof(f4458,plain,
    ( ~ spl9_515
    | spl9_262
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4454,f295,f158,f1060,f4456])).

fof(f4454,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4406,f296])).

fof(f4406,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_26
    | ~ spl9_74 ),
    inference(superposition,[],[f455,f296])).

fof(f4453,plain,
    ( ~ spl9_513
    | spl9_226
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4449,f266,f158,f910,f4451])).

fof(f4449,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4405,f267])).

fof(f4405,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_26
    | ~ spl9_62 ),
    inference(superposition,[],[f455,f267])).

fof(f4448,plain,
    ( ~ spl9_511
    | spl9_250
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4444,f286,f158,f1010,f4446])).

fof(f4444,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4404,f287])).

fof(f4404,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_26
    | ~ spl9_70 ),
    inference(superposition,[],[f455,f287])).

fof(f4443,plain,
    ( ~ spl9_509
    | spl9_1
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4439,f358,f158,f88,f4441])).

fof(f4439,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f4438,f89])).

fof(f4438,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4402,f359])).

fof(f4402,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_26
    | ~ spl9_96 ),
    inference(superposition,[],[f455,f359])).

fof(f4437,plain,
    ( spl9_120
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4436,f158,f467])).

fof(f4436,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4401,f159])).

fof(f4401,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f159,f455])).

fof(f4400,plain,
    ( spl9_340
    | ~ spl9_301
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4339,f303,f154,f3318,f3526])).

fof(f3318,plain,
    ( spl9_301
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_301])])).

fof(f4339,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f434,f362])).

fof(f434,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_24 ),
    inference(superposition,[],[f86,f155])).

fof(f4399,plain,
    ( spl9_336
    | ~ spl9_301
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4337,f303,f154,f3318,f3506])).

fof(f4337,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f434,f352])).

fof(f4398,plain,
    ( ~ spl9_507
    | spl9_204
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4397,f247,f154,f817,f4301])).

fof(f4301,plain,
    ( spl9_507
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_507])])).

fof(f4397,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4335,f248])).

fof(f4335,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(superposition,[],[f434,f248])).

fof(f4396,plain,
    ( ~ spl9_505
    | spl9_198
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4395,f243,f154,f792,f4296])).

fof(f4296,plain,
    ( spl9_505
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_505])])).

fof(f4395,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4334,f244])).

fof(f4334,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(superposition,[],[f434,f244])).

fof(f4394,plain,
    ( ~ spl9_503
    | spl9_192
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4393,f239,f154,f767,f4291])).

fof(f4291,plain,
    ( spl9_503
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_503])])).

fof(f4393,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4333,f240])).

fof(f4333,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(superposition,[],[f434,f240])).

fof(f4392,plain,
    ( ~ spl9_501
    | spl9_186
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4391,f235,f154,f742,f4286])).

fof(f4286,plain,
    ( spl9_501
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_501])])).

fof(f4391,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4332,f236])).

fof(f4332,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(superposition,[],[f434,f236])).

fof(f4390,plain,
    ( ~ spl9_499
    | spl9_180
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4389,f231,f154,f717,f4281])).

fof(f4281,plain,
    ( spl9_499
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_499])])).

fof(f4389,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4331,f232])).

fof(f4331,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(superposition,[],[f434,f232])).

fof(f4388,plain,
    ( ~ spl9_497
    | spl9_174
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4387,f227,f154,f692,f4276])).

fof(f4276,plain,
    ( spl9_497
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_497])])).

fof(f4387,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4330,f228])).

fof(f4330,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(superposition,[],[f434,f228])).

fof(f4386,plain,
    ( ~ spl9_495
    | spl9_166
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4385,f223,f154,f658,f4271])).

fof(f4271,plain,
    ( spl9_495
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_495])])).

fof(f4385,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4329,f224])).

fof(f4329,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(superposition,[],[f434,f224])).

fof(f4384,plain,
    ( ~ spl9_493
    | spl9_160
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4383,f219,f154,f633,f4266])).

fof(f4266,plain,
    ( spl9_493
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_493])])).

fof(f4383,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4328,f220])).

fof(f4328,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(superposition,[],[f434,f220])).

fof(f4382,plain,
    ( ~ spl9_491
    | spl9_154
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4381,f215,f154,f608,f4261])).

fof(f4261,plain,
    ( spl9_491
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_491])])).

fof(f4381,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4327,f216])).

fof(f4327,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(superposition,[],[f434,f216])).

fof(f4380,plain,
    ( ~ spl9_489
    | spl9_222
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4379,f262,f154,f892,f4256])).

fof(f4256,plain,
    ( spl9_489
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_489])])).

fof(f4379,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4326,f263])).

fof(f4326,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(superposition,[],[f434,f263])).

fof(f4378,plain,
    ( ~ spl9_487
    | spl9_216
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4377,f258,f154,f867,f4251])).

fof(f4251,plain,
    ( spl9_487
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_487])])).

fof(f4377,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4325,f259])).

fof(f4325,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(superposition,[],[f434,f259])).

fof(f4376,plain,
    ( ~ spl9_485
    | spl9_210
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4375,f254,f154,f842,f4246])).

fof(f4246,plain,
    ( spl9_485
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_485])])).

fof(f4375,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4324,f255])).

fof(f4324,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(superposition,[],[f434,f255])).

fof(f4374,plain,
    ( ~ spl9_483
    | spl9_258
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4373,f291,f154,f1042,f4241])).

fof(f4241,plain,
    ( spl9_483
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_483])])).

fof(f4373,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4323,f292])).

fof(f4323,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(superposition,[],[f434,f292])).

fof(f4372,plain,
    ( ~ spl9_481
    | spl9_128
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4371,f162,f154,f499,f4236])).

fof(f4371,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4322,f163])).

fof(f4322,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(superposition,[],[f434,f163])).

fof(f4370,plain,
    ( ~ spl9_479
    | spl9_122
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4369,f158,f154,f474,f4231])).

fof(f4369,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4321,f159])).

fof(f4321,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(superposition,[],[f434,f159])).

fof(f4368,plain,
    ( ~ spl9_477
    | spl9_246
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4367,f282,f154,f992,f4226])).

fof(f4226,plain,
    ( spl9_477
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_477])])).

fof(f4367,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4320,f283])).

fof(f4320,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(superposition,[],[f434,f283])).

fof(f4366,plain,
    ( spl9_116
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4365,f154,f449])).

fof(f4365,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4340,f155])).

fof(f4340,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24 ),
    inference(trivial_inequality_removal,[],[f4319])).

fof(f4319,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24 ),
    inference(superposition,[],[f434,f155])).

fof(f4364,plain,
    ( ~ spl9_425
    | spl9_110
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4363,f154,f150,f424,f3955])).

fof(f3955,plain,
    ( spl9_425
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_425])])).

fof(f4363,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4318,f151])).

fof(f4318,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(superposition,[],[f434,f151])).

fof(f4362,plain,
    ( ~ spl9_475
    | spl9_234
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4361,f270,f154,f942,f4217])).

fof(f4217,plain,
    ( spl9_475
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_475])])).

fof(f4361,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4317,f271])).

fof(f4317,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(superposition,[],[f434,f271])).

fof(f4360,plain,
    ( ~ spl9_473
    | spl9_148
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4359,f179,f154,f583,f4212])).

fof(f4359,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4316,f180])).

fof(f4316,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(superposition,[],[f434,f180])).

fof(f4358,plain,
    ( ~ spl9_471
    | spl9_134
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4357,f168,f154,f524,f4207])).

fof(f4357,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4315,f169])).

fof(f4315,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(superposition,[],[f434,f169])).

fof(f4356,plain,
    ( ~ spl9_469
    | spl9_240
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4355,f274,f154,f967,f4202])).

fof(f4202,plain,
    ( spl9_469
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_469])])).

fof(f4355,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4314,f275])).

fof(f4314,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(superposition,[],[f434,f275])).

fof(f4354,plain,
    ( ~ spl9_467
    | spl9_142
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4353,f172,f154,f558,f4197])).

fof(f4353,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4313,f173])).

fof(f4313,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(superposition,[],[f434,f173])).

fof(f4352,plain,
    ( ~ spl9_369
    | spl9_102
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4351,f154,f122,f390,f3676])).

fof(f3676,plain,
    ( spl9_369
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_369])])).

fof(f4351,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4312,f123])).

fof(f4312,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(superposition,[],[f434,f123])).

fof(f4350,plain,
    ( ~ spl9_465
    | spl9_264
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4349,f295,f154,f1067,f4190])).

fof(f4190,plain,
    ( spl9_465
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_465])])).

fof(f4349,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4311,f296])).

fof(f4311,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(superposition,[],[f434,f296])).

fof(f4348,plain,
    ( ~ spl9_463
    | spl9_228
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4347,f266,f154,f917,f4185])).

fof(f4185,plain,
    ( spl9_463
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_463])])).

fof(f4347,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4310,f267])).

fof(f4310,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(superposition,[],[f434,f267])).

fof(f4346,plain,
    ( ~ spl9_461
    | spl9_252
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4345,f286,f154,f1017,f4180])).

fof(f4180,plain,
    ( spl9_461
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_461])])).

fof(f4345,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4309,f287])).

fof(f4309,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(superposition,[],[f434,f287])).

fof(f4344,plain,
    ( ~ spl9_459
    | spl9_2
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4343,f358,f154,f3555,f4175])).

fof(f4175,plain,
    ( spl9_459
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_459])])).

fof(f4343,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4307,f359])).

fof(f4307,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(superposition,[],[f434,f359])).

fof(f4342,plain,
    ( spl9_116
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4341,f154,f449])).

fof(f4341,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4306,f155])).

fof(f4306,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f155,f434])).

fof(f4305,plain,
    ( spl9_338
    | ~ spl9_301
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4168,f303,f154,f3318,f3522])).

fof(f4168,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f430,f362])).

fof(f430,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_24 ),
    inference(superposition,[],[f82,f155])).

fof(f4304,plain,
    ( spl9_334
    | ~ spl9_301
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4166,f303,f154,f3318,f3502])).

fof(f4166,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f430,f352])).

fof(f4303,plain,
    ( ~ spl9_507
    | spl9_202
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4299,f247,f154,f810,f4301])).

fof(f4299,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4164,f248])).

fof(f4164,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_24
    | ~ spl9_54 ),
    inference(superposition,[],[f430,f248])).

fof(f4298,plain,
    ( ~ spl9_505
    | spl9_196
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4294,f243,f154,f785,f4296])).

fof(f4294,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4163,f244])).

fof(f4163,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_24
    | ~ spl9_52 ),
    inference(superposition,[],[f430,f244])).

fof(f4293,plain,
    ( ~ spl9_503
    | spl9_190
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4289,f239,f154,f760,f4291])).

fof(f4289,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4162,f240])).

fof(f4162,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_24
    | ~ spl9_50 ),
    inference(superposition,[],[f430,f240])).

fof(f4288,plain,
    ( ~ spl9_501
    | spl9_184
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4284,f235,f154,f735,f4286])).

fof(f4284,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4161,f236])).

fof(f4161,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_24
    | ~ spl9_48 ),
    inference(superposition,[],[f430,f236])).

fof(f4283,plain,
    ( ~ spl9_499
    | spl9_178
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4279,f231,f154,f710,f4281])).

fof(f4279,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4160,f232])).

fof(f4160,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_24
    | ~ spl9_46 ),
    inference(superposition,[],[f430,f232])).

fof(f4278,plain,
    ( ~ spl9_497
    | spl9_172
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4274,f227,f154,f685,f4276])).

fof(f4274,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4159,f228])).

fof(f4159,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_24
    | ~ spl9_44 ),
    inference(superposition,[],[f430,f228])).

fof(f4273,plain,
    ( ~ spl9_495
    | spl9_164
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4269,f223,f154,f651,f4271])).

fof(f4269,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4158,f224])).

fof(f4158,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_24
    | ~ spl9_42 ),
    inference(superposition,[],[f430,f224])).

fof(f4268,plain,
    ( ~ spl9_493
    | spl9_158
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4264,f219,f154,f626,f4266])).

fof(f4264,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4157,f220])).

fof(f4157,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_24
    | ~ spl9_40 ),
    inference(superposition,[],[f430,f220])).

fof(f4263,plain,
    ( ~ spl9_491
    | spl9_152
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4259,f215,f154,f601,f4261])).

fof(f4259,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4156,f216])).

fof(f4156,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_24
    | ~ spl9_38 ),
    inference(superposition,[],[f430,f216])).

fof(f4258,plain,
    ( ~ spl9_489
    | spl9_220
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4254,f262,f154,f885,f4256])).

fof(f4254,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4155,f263])).

fof(f4155,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_24
    | ~ spl9_60 ),
    inference(superposition,[],[f430,f263])).

fof(f4253,plain,
    ( ~ spl9_487
    | spl9_214
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4249,f258,f154,f860,f4251])).

fof(f4249,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4154,f259])).

fof(f4154,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_24
    | ~ spl9_58 ),
    inference(superposition,[],[f430,f259])).

fof(f4248,plain,
    ( ~ spl9_485
    | spl9_208
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4244,f254,f154,f835,f4246])).

fof(f4244,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4153,f255])).

fof(f4153,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_24
    | ~ spl9_56 ),
    inference(superposition,[],[f430,f255])).

fof(f4243,plain,
    ( ~ spl9_483
    | spl9_256
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4239,f291,f154,f1035,f4241])).

fof(f4239,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4152,f292])).

fof(f4152,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_24
    | ~ spl9_72 ),
    inference(superposition,[],[f430,f292])).

fof(f4238,plain,
    ( ~ spl9_481
    | spl9_126
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4234,f162,f154,f492,f4236])).

fof(f4234,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4151,f163])).

fof(f4151,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(superposition,[],[f430,f163])).

fof(f4233,plain,
    ( ~ spl9_479
    | spl9_120
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4229,f158,f154,f467,f4231])).

fof(f4229,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4150,f159])).

fof(f4150,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(superposition,[],[f430,f159])).

fof(f4228,plain,
    ( ~ spl9_477
    | spl9_244
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4224,f282,f154,f985,f4226])).

fof(f4224,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4149,f283])).

fof(f4149,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_68 ),
    inference(superposition,[],[f430,f283])).

fof(f4223,plain,
    ( spl9_114
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4222,f154,f442])).

fof(f4222,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4169,f155])).

fof(f4169,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24 ),
    inference(trivial_inequality_removal,[],[f4148])).

fof(f4148,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24 ),
    inference(superposition,[],[f430,f155])).

fof(f4221,plain,
    ( ~ spl9_425
    | spl9_108
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4220,f154,f150,f417,f3955])).

fof(f4220,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4147,f151])).

fof(f4147,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(superposition,[],[f430,f151])).

fof(f4219,plain,
    ( ~ spl9_475
    | spl9_232
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4215,f270,f154,f935,f4217])).

fof(f4215,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4146,f271])).

fof(f4146,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_24
    | ~ spl9_64 ),
    inference(superposition,[],[f430,f271])).

fof(f4214,plain,
    ( ~ spl9_473
    | spl9_146
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4210,f179,f154,f576,f4212])).

fof(f4210,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4145,f180])).

fof(f4145,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_24
    | ~ spl9_34 ),
    inference(superposition,[],[f430,f180])).

fof(f4209,plain,
    ( ~ spl9_471
    | spl9_132
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4205,f168,f154,f517,f4207])).

fof(f4205,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4144,f169])).

fof(f4144,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(superposition,[],[f430,f169])).

fof(f4204,plain,
    ( ~ spl9_469
    | spl9_238
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4200,f274,f154,f960,f4202])).

fof(f4200,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4143,f275])).

fof(f4143,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_24
    | ~ spl9_66 ),
    inference(superposition,[],[f430,f275])).

fof(f4199,plain,
    ( ~ spl9_467
    | spl9_140
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4195,f172,f154,f551,f4197])).

fof(f4195,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4142,f173])).

fof(f4142,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_24
    | ~ spl9_32 ),
    inference(superposition,[],[f430,f173])).

fof(f4194,plain,
    ( ~ spl9_369
    | spl9_100
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4193,f154,f122,f383,f3676])).

fof(f4193,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4141,f123])).

fof(f4141,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(superposition,[],[f430,f123])).

fof(f4192,plain,
    ( ~ spl9_465
    | spl9_262
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4188,f295,f154,f1060,f4190])).

fof(f4188,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4140,f296])).

fof(f4140,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_24
    | ~ spl9_74 ),
    inference(superposition,[],[f430,f296])).

fof(f4187,plain,
    ( ~ spl9_463
    | spl9_226
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4183,f266,f154,f910,f4185])).

fof(f4183,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4139,f267])).

fof(f4139,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_24
    | ~ spl9_62 ),
    inference(superposition,[],[f430,f267])).

fof(f4182,plain,
    ( ~ spl9_461
    | spl9_250
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4178,f286,f154,f1010,f4180])).

fof(f4178,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4138,f287])).

fof(f4138,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_24
    | ~ spl9_70 ),
    inference(superposition,[],[f430,f287])).

fof(f4177,plain,
    ( ~ spl9_459
    | spl9_1
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4173,f358,f154,f88,f4175])).

fof(f4173,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_1
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f4172,f89])).

fof(f4172,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4136,f359])).

fof(f4136,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_24
    | ~ spl9_96 ),
    inference(superposition,[],[f430,f359])).

fof(f4171,plain,
    ( spl9_114
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4170,f154,f442])).

fof(f4170,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4135,f155])).

fof(f4135,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f155,f430])).

fof(f4134,plain,
    ( spl9_340
    | ~ spl9_299
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4073,f303,f150,f3313,f3526])).

fof(f3313,plain,
    ( spl9_299
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).

fof(f4073,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f409,f362])).

fof(f409,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_22 ),
    inference(superposition,[],[f86,f151])).

fof(f4133,plain,
    ( spl9_336
    | ~ spl9_299
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f4071,f303,f150,f3313,f3506])).

fof(f4071,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f409,f352])).

fof(f4132,plain,
    ( ~ spl9_457
    | spl9_204
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4131,f247,f150,f817,f4035])).

fof(f4035,plain,
    ( spl9_457
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_457])])).

fof(f4131,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f4069,f248])).

fof(f4069,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(superposition,[],[f409,f248])).

fof(f4130,plain,
    ( ~ spl9_455
    | spl9_198
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4129,f243,f150,f792,f4030])).

fof(f4030,plain,
    ( spl9_455
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_455])])).

fof(f4129,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f4068,f244])).

fof(f4068,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(superposition,[],[f409,f244])).

fof(f4128,plain,
    ( ~ spl9_453
    | spl9_192
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4127,f239,f150,f767,f4025])).

fof(f4025,plain,
    ( spl9_453
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_453])])).

fof(f4127,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f4067,f240])).

fof(f4067,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(superposition,[],[f409,f240])).

fof(f4126,plain,
    ( ~ spl9_451
    | spl9_186
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4125,f235,f150,f742,f4020])).

fof(f4020,plain,
    ( spl9_451
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_451])])).

fof(f4125,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f4066,f236])).

fof(f4066,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(superposition,[],[f409,f236])).

fof(f4124,plain,
    ( ~ spl9_449
    | spl9_180
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4123,f231,f150,f717,f4015])).

fof(f4015,plain,
    ( spl9_449
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_449])])).

fof(f4123,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f4065,f232])).

fof(f4065,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(superposition,[],[f409,f232])).

fof(f4122,plain,
    ( ~ spl9_447
    | spl9_174
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4121,f227,f150,f692,f4010])).

fof(f4010,plain,
    ( spl9_447
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).

fof(f4121,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f4064,f228])).

fof(f4064,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(superposition,[],[f409,f228])).

fof(f4120,plain,
    ( ~ spl9_445
    | spl9_166
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4119,f223,f150,f658,f4005])).

fof(f4005,plain,
    ( spl9_445
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_445])])).

fof(f4119,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f4063,f224])).

fof(f4063,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(superposition,[],[f409,f224])).

fof(f4118,plain,
    ( ~ spl9_443
    | spl9_160
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f4117,f219,f150,f633,f4000])).

fof(f4000,plain,
    ( spl9_443
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_443])])).

fof(f4117,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f4062,f220])).

fof(f4062,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(superposition,[],[f409,f220])).

fof(f4116,plain,
    ( ~ spl9_441
    | spl9_154
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f4115,f215,f150,f608,f3995])).

fof(f3995,plain,
    ( spl9_441
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_441])])).

fof(f4115,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f4061,f216])).

fof(f4061,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(superposition,[],[f409,f216])).

fof(f4114,plain,
    ( ~ spl9_439
    | spl9_222
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f4113,f262,f150,f892,f3990])).

fof(f3990,plain,
    ( spl9_439
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_439])])).

fof(f4113,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f4060,f263])).

fof(f4060,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(superposition,[],[f409,f263])).

fof(f4112,plain,
    ( ~ spl9_437
    | spl9_216
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f4111,f258,f150,f867,f3985])).

fof(f3985,plain,
    ( spl9_437
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_437])])).

fof(f4111,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f4059,f259])).

fof(f4059,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(superposition,[],[f409,f259])).

fof(f4110,plain,
    ( ~ spl9_435
    | spl9_210
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f4109,f254,f150,f842,f3980])).

fof(f3980,plain,
    ( spl9_435
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_435])])).

fof(f4109,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f4058,f255])).

fof(f4058,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(superposition,[],[f409,f255])).

fof(f4108,plain,
    ( ~ spl9_433
    | spl9_258
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f4107,f291,f150,f1042,f3975])).

fof(f3975,plain,
    ( spl9_433
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_433])])).

fof(f4107,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f4057,f292])).

fof(f4057,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(superposition,[],[f409,f292])).

fof(f4106,plain,
    ( ~ spl9_431
    | spl9_128
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4105,f162,f150,f499,f3970])).

fof(f4105,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f4056,f163])).

fof(f4056,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(superposition,[],[f409,f163])).

fof(f4104,plain,
    ( ~ spl9_429
    | spl9_122
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f4103,f158,f150,f474,f3965])).

fof(f4103,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f4055,f159])).

fof(f4055,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(superposition,[],[f409,f159])).

fof(f4102,plain,
    ( ~ spl9_427
    | spl9_246
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f4101,f282,f150,f992,f3960])).

fof(f3960,plain,
    ( spl9_427
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_427])])).

fof(f4101,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f4054,f283])).

fof(f4054,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(superposition,[],[f409,f283])).

fof(f4100,plain,
    ( ~ spl9_425
    | spl9_116
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4099,f154,f150,f449,f3955])).

fof(f4099,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f4053,f155])).

fof(f4053,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(superposition,[],[f409,f155])).

fof(f4098,plain,
    ( spl9_110
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f4097,f150,f424])).

fof(f4097,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f4074,f151])).

fof(f4074,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22 ),
    inference(trivial_inequality_removal,[],[f4052])).

fof(f4052,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22 ),
    inference(superposition,[],[f409,f151])).

fof(f4096,plain,
    ( ~ spl9_423
    | spl9_234
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4095,f270,f150,f942,f3948])).

fof(f3948,plain,
    ( spl9_423
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_423])])).

fof(f4095,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f4051,f271])).

fof(f4051,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(superposition,[],[f409,f271])).

fof(f4094,plain,
    ( ~ spl9_421
    | spl9_148
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f4093,f179,f150,f583,f3943])).

fof(f4093,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f4050,f180])).

fof(f4050,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(superposition,[],[f409,f180])).

fof(f4092,plain,
    ( ~ spl9_419
    | spl9_134
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f4091,f168,f150,f524,f3938])).

fof(f4091,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f4049,f169])).

fof(f4049,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(superposition,[],[f409,f169])).

fof(f4090,plain,
    ( ~ spl9_417
    | spl9_240
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f4089,f274,f150,f967,f3933])).

fof(f3933,plain,
    ( spl9_417
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_417])])).

fof(f4089,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f4048,f275])).

fof(f4048,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(superposition,[],[f409,f275])).

fof(f4088,plain,
    ( ~ spl9_415
    | spl9_142
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f4087,f172,f150,f558,f3928])).

fof(f4087,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f4047,f173])).

fof(f4047,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(superposition,[],[f409,f173])).

fof(f4086,plain,
    ( ~ spl9_367
    | spl9_102
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f4085,f150,f122,f390,f3671])).

fof(f3671,plain,
    ( spl9_367
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_367])])).

fof(f4085,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f4046,f123])).

fof(f4046,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(superposition,[],[f409,f123])).

fof(f4084,plain,
    ( ~ spl9_413
    | spl9_264
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4083,f295,f150,f1067,f3921])).

fof(f3921,plain,
    ( spl9_413
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_413])])).

fof(f4083,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f4045,f296])).

fof(f4045,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(superposition,[],[f409,f296])).

fof(f4082,plain,
    ( ~ spl9_411
    | spl9_228
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f4081,f266,f150,f917,f3916])).

fof(f3916,plain,
    ( spl9_411
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_411])])).

fof(f4081,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f4044,f267])).

fof(f4044,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(superposition,[],[f409,f267])).

fof(f4080,plain,
    ( ~ spl9_409
    | spl9_252
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f4079,f286,f150,f1017,f3911])).

fof(f3911,plain,
    ( spl9_409
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_409])])).

fof(f4079,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f4043,f287])).

fof(f4043,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(superposition,[],[f409,f287])).

fof(f4078,plain,
    ( ~ spl9_407
    | spl9_2
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f4077,f358,f150,f3555,f3906])).

fof(f3906,plain,
    ( spl9_407
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_407])])).

fof(f4077,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f4041,f359])).

fof(f4041,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(superposition,[],[f409,f359])).

fof(f4076,plain,
    ( spl9_110
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f4075,f150,f424])).

fof(f4075,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f4040,f151])).

fof(f4040,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f151,f409])).

fof(f4039,plain,
    ( spl9_338
    | ~ spl9_299
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3899,f303,f150,f3313,f3522])).

fof(f3899,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f405,f362])).

fof(f405,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_22 ),
    inference(superposition,[],[f82,f151])).

fof(f4038,plain,
    ( spl9_334
    | ~ spl9_299
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3897,f303,f150,f3313,f3502])).

fof(f3897,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f405,f352])).

fof(f4037,plain,
    ( ~ spl9_457
    | spl9_202
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f4033,f247,f150,f810,f4035])).

fof(f4033,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f3895,f248])).

fof(f3895,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_22
    | ~ spl9_54 ),
    inference(superposition,[],[f405,f248])).

fof(f4032,plain,
    ( ~ spl9_455
    | spl9_196
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f4028,f243,f150,f785,f4030])).

fof(f4028,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3894,f244])).

fof(f3894,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_22
    | ~ spl9_52 ),
    inference(superposition,[],[f405,f244])).

fof(f4027,plain,
    ( ~ spl9_453
    | spl9_190
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f4023,f239,f150,f760,f4025])).

fof(f4023,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f3893,f240])).

fof(f3893,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_22
    | ~ spl9_50 ),
    inference(superposition,[],[f405,f240])).

fof(f4022,plain,
    ( ~ spl9_451
    | spl9_184
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f4018,f235,f150,f735,f4020])).

fof(f4018,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f3892,f236])).

fof(f3892,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_22
    | ~ spl9_48 ),
    inference(superposition,[],[f405,f236])).

fof(f4017,plain,
    ( ~ spl9_449
    | spl9_178
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f4013,f231,f150,f710,f4015])).

fof(f4013,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3891,f232])).

fof(f3891,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_22
    | ~ spl9_46 ),
    inference(superposition,[],[f405,f232])).

fof(f4012,plain,
    ( ~ spl9_447
    | spl9_172
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f4008,f227,f150,f685,f4010])).

fof(f4008,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f3890,f228])).

fof(f3890,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_22
    | ~ spl9_44 ),
    inference(superposition,[],[f405,f228])).

fof(f4007,plain,
    ( ~ spl9_445
    | spl9_164
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f4003,f223,f150,f651,f4005])).

fof(f4003,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f3889,f224])).

fof(f3889,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_22
    | ~ spl9_42 ),
    inference(superposition,[],[f405,f224])).

fof(f4002,plain,
    ( ~ spl9_443
    | spl9_158
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f3998,f219,f150,f626,f4000])).

fof(f3998,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f3888,f220])).

fof(f3888,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(superposition,[],[f405,f220])).

fof(f3997,plain,
    ( ~ spl9_441
    | spl9_152
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f3993,f215,f150,f601,f3995])).

fof(f3993,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f3887,f216])).

fof(f3887,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_22
    | ~ spl9_38 ),
    inference(superposition,[],[f405,f216])).

fof(f3992,plain,
    ( ~ spl9_439
    | spl9_220
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f3988,f262,f150,f885,f3990])).

fof(f3988,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f3886,f263])).

fof(f3886,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(superposition,[],[f405,f263])).

fof(f3987,plain,
    ( ~ spl9_437
    | spl9_214
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f3983,f258,f150,f860,f3985])).

fof(f3983,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f3885,f259])).

fof(f3885,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_22
    | ~ spl9_58 ),
    inference(superposition,[],[f405,f259])).

fof(f3982,plain,
    ( ~ spl9_435
    | spl9_208
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f3978,f254,f150,f835,f3980])).

fof(f3978,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f3884,f255])).

fof(f3884,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_22
    | ~ spl9_56 ),
    inference(superposition,[],[f405,f255])).

fof(f3977,plain,
    ( ~ spl9_433
    | spl9_256
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f3973,f291,f150,f1035,f3975])).

fof(f3973,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f3883,f292])).

fof(f3883,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_22
    | ~ spl9_72 ),
    inference(superposition,[],[f405,f292])).

fof(f3972,plain,
    ( ~ spl9_431
    | spl9_126
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f3968,f162,f150,f492,f3970])).

fof(f3968,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3882,f163])).

fof(f3882,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_22
    | ~ spl9_28 ),
    inference(superposition,[],[f405,f163])).

fof(f3967,plain,
    ( ~ spl9_429
    | spl9_120
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f3963,f158,f150,f467,f3965])).

fof(f3963,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f3881,f159])).

fof(f3881,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(superposition,[],[f405,f159])).

fof(f3962,plain,
    ( ~ spl9_427
    | spl9_244
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f3958,f282,f150,f985,f3960])).

fof(f3958,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f3880,f283])).

fof(f3880,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_68 ),
    inference(superposition,[],[f405,f283])).

fof(f3957,plain,
    ( ~ spl9_425
    | spl9_114
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f3953,f154,f150,f442,f3955])).

fof(f3953,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f3879,f155])).

fof(f3879,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(superposition,[],[f405,f155])).

fof(f3952,plain,
    ( spl9_108
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f3951,f150,f417])).

fof(f3951,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3900,f151])).

fof(f3900,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22 ),
    inference(trivial_inequality_removal,[],[f3878])).

fof(f3878,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22 ),
    inference(superposition,[],[f405,f151])).

fof(f3950,plain,
    ( ~ spl9_423
    | spl9_232
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f3946,f270,f150,f935,f3948])).

fof(f3946,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f3877,f271])).

fof(f3877,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_22
    | ~ spl9_64 ),
    inference(superposition,[],[f405,f271])).

fof(f3945,plain,
    ( ~ spl9_421
    | spl9_146
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f3941,f179,f150,f576,f3943])).

fof(f3941,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f3876,f180])).

fof(f3876,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_22
    | ~ spl9_34 ),
    inference(superposition,[],[f405,f180])).

fof(f3940,plain,
    ( ~ spl9_419
    | spl9_132
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f3936,f168,f150,f517,f3938])).

fof(f3936,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f3875,f169])).

fof(f3875,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_22
    | ~ spl9_30 ),
    inference(superposition,[],[f405,f169])).

fof(f3935,plain,
    ( ~ spl9_417
    | spl9_238
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f3931,f274,f150,f960,f3933])).

fof(f3931,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f3874,f275])).

fof(f3874,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_22
    | ~ spl9_66 ),
    inference(superposition,[],[f405,f275])).

fof(f3930,plain,
    ( ~ spl9_415
    | spl9_140
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f3926,f172,f150,f551,f3928])).

fof(f3926,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f3873,f173])).

fof(f3873,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_22
    | ~ spl9_32 ),
    inference(superposition,[],[f405,f173])).

fof(f3925,plain,
    ( ~ spl9_367
    | spl9_100
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f3924,f150,f122,f383,f3671])).

fof(f3924,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3872,f123])).

fof(f3872,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(superposition,[],[f405,f123])).

fof(f3923,plain,
    ( ~ spl9_413
    | spl9_262
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f3919,f295,f150,f1060,f3921])).

fof(f3919,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f3871,f296])).

fof(f3871,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_22
    | ~ spl9_74 ),
    inference(superposition,[],[f405,f296])).

fof(f3918,plain,
    ( ~ spl9_411
    | spl9_226
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f3914,f266,f150,f910,f3916])).

fof(f3914,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f3870,f267])).

fof(f3870,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_22
    | ~ spl9_62 ),
    inference(superposition,[],[f405,f267])).

fof(f3913,plain,
    ( ~ spl9_409
    | spl9_250
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f3909,f286,f150,f1010,f3911])).

fof(f3909,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f3869,f287])).

fof(f3869,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_22
    | ~ spl9_70 ),
    inference(superposition,[],[f405,f287])).

fof(f3908,plain,
    ( ~ spl9_407
    | spl9_1
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3904,f358,f150,f88,f3906])).

fof(f3904,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_1
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f3903,f89])).

fof(f3903,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3867,f359])).

fof(f3867,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_22
    | ~ spl9_96 ),
    inference(superposition,[],[f405,f359])).

fof(f3902,plain,
    ( spl9_108
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f3901,f150,f417])).

fof(f3901,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3866,f151])).

fof(f3866,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f151,f405])).

fof(f3865,plain,
    ( spl9_340
    | ~ spl9_287
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3804,f303,f122,f3283,f3526])).

fof(f3283,plain,
    ( spl9_287
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_287])])).

fof(f3804,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k2_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK7(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f375,f362])).

fof(f375,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_16 ),
    inference(superposition,[],[f86,f123])).

fof(f3864,plain,
    ( spl9_336
    | ~ spl9_287
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3802,f303,f122,f3283,f3506])).

fof(f3802,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k2_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK5(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f375,f352])).

fof(f3863,plain,
    ( ~ spl9_401
    | spl9_204
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f3862,f247,f122,f817,f3756])).

fof(f3756,plain,
    ( spl9_401
  <=> sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_401])])).

fof(f3862,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f3800,f248])).

fof(f3800,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(superposition,[],[f375,f248])).

fof(f3861,plain,
    ( ~ spl9_399
    | spl9_198
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f3860,f243,f122,f792,f3751])).

fof(f3751,plain,
    ( spl9_399
  <=> sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_399])])).

fof(f3860,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3799,f244])).

fof(f3799,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(superposition,[],[f375,f244])).

fof(f3859,plain,
    ( ~ spl9_397
    | spl9_192
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f3858,f239,f122,f767,f3746])).

fof(f3746,plain,
    ( spl9_397
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_397])])).

fof(f3858,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f3798,f240])).

fof(f3798,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(superposition,[],[f375,f240])).

fof(f3857,plain,
    ( ~ spl9_395
    | spl9_186
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f3856,f235,f122,f742,f3741])).

fof(f3741,plain,
    ( spl9_395
  <=> sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_395])])).

fof(f3856,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f3797,f236])).

fof(f3797,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(superposition,[],[f375,f236])).

fof(f3855,plain,
    ( ~ spl9_393
    | spl9_180
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f3854,f231,f122,f717,f3736])).

fof(f3736,plain,
    ( spl9_393
  <=> sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_393])])).

fof(f3854,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3796,f232])).

fof(f3796,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(superposition,[],[f375,f232])).

fof(f3853,plain,
    ( ~ spl9_391
    | spl9_174
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f3852,f227,f122,f692,f3731])).

fof(f3731,plain,
    ( spl9_391
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_391])])).

fof(f3852,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f3795,f228])).

fof(f3795,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(superposition,[],[f375,f228])).

fof(f3851,plain,
    ( ~ spl9_389
    | spl9_166
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f3850,f223,f122,f658,f3726])).

fof(f3726,plain,
    ( spl9_389
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_389])])).

fof(f3850,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f3794,f224])).

fof(f3794,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(superposition,[],[f375,f224])).

fof(f3849,plain,
    ( ~ spl9_387
    | spl9_160
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f3848,f219,f122,f633,f3721])).

fof(f3721,plain,
    ( spl9_387
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_387])])).

fof(f3848,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f3793,f220])).

fof(f3793,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(superposition,[],[f375,f220])).

fof(f3847,plain,
    ( ~ spl9_385
    | spl9_154
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f3846,f215,f122,f608,f3716])).

fof(f3716,plain,
    ( spl9_385
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_385])])).

fof(f3846,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f3792,f216])).

fof(f3792,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(superposition,[],[f375,f216])).

fof(f3845,plain,
    ( ~ spl9_383
    | spl9_222
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f3844,f262,f122,f892,f3711])).

fof(f3711,plain,
    ( spl9_383
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_383])])).

fof(f3844,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f3791,f263])).

fof(f3791,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(superposition,[],[f375,f263])).

fof(f3843,plain,
    ( ~ spl9_381
    | spl9_216
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f3842,f258,f122,f867,f3706])).

fof(f3706,plain,
    ( spl9_381
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_381])])).

fof(f3842,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f3790,f259])).

fof(f3790,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(superposition,[],[f375,f259])).

fof(f3841,plain,
    ( ~ spl9_379
    | spl9_210
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f3840,f254,f122,f842,f3701])).

fof(f3701,plain,
    ( spl9_379
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_379])])).

fof(f3840,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f3789,f255])).

fof(f3789,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(superposition,[],[f375,f255])).

fof(f3839,plain,
    ( ~ spl9_377
    | spl9_258
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f3838,f291,f122,f1042,f3696])).

fof(f3696,plain,
    ( spl9_377
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).

fof(f3838,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f3788,f292])).

fof(f3788,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(superposition,[],[f375,f292])).

fof(f3837,plain,
    ( ~ spl9_375
    | spl9_128
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f3836,f162,f122,f499,f3691])).

fof(f3836,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3787,f163])).

fof(f3787,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(superposition,[],[f375,f163])).

fof(f3835,plain,
    ( ~ spl9_373
    | spl9_122
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f3834,f158,f122,f474,f3686])).

fof(f3834,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f3786,f159])).

fof(f3786,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(superposition,[],[f375,f159])).

fof(f3833,plain,
    ( ~ spl9_371
    | spl9_246
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f3832,f282,f122,f992,f3681])).

fof(f3681,plain,
    ( spl9_371
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_371])])).

fof(f3832,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f3785,f283])).

fof(f3785,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(superposition,[],[f375,f283])).

fof(f3831,plain,
    ( ~ spl9_369
    | spl9_116
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f3830,f154,f122,f449,f3676])).

fof(f3830,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f3784,f155])).

fof(f3784,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(superposition,[],[f375,f155])).

fof(f3829,plain,
    ( ~ spl9_367
    | spl9_110
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f3828,f150,f122,f424,f3671])).

fof(f3828,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3783,f151])).

fof(f3783,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(superposition,[],[f375,f151])).

fof(f3827,plain,
    ( ~ spl9_365
    | spl9_234
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f3826,f270,f122,f942,f3666])).

fof(f3666,plain,
    ( spl9_365
  <=> sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_365])])).

fof(f3826,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f3782,f271])).

fof(f3782,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(superposition,[],[f375,f271])).

fof(f3825,plain,
    ( ~ spl9_363
    | spl9_148
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f3824,f179,f122,f583,f3661])).

fof(f3824,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f3781,f180])).

fof(f3781,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(superposition,[],[f375,f180])).

fof(f3823,plain,
    ( ~ spl9_361
    | spl9_134
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f3822,f168,f122,f524,f3656])).

fof(f3822,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f3780,f169])).

fof(f3780,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(superposition,[],[f375,f169])).

fof(f3821,plain,
    ( ~ spl9_359
    | spl9_240
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f3820,f274,f122,f967,f3651])).

fof(f3651,plain,
    ( spl9_359
  <=> sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_359])])).

fof(f3820,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f3779,f275])).

fof(f3779,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(superposition,[],[f375,f275])).

fof(f3819,plain,
    ( ~ spl9_357
    | spl9_142
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f3818,f172,f122,f558,f3646])).

fof(f3818,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f3778,f173])).

fof(f3778,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(superposition,[],[f375,f173])).

fof(f3817,plain,
    ( spl9_102
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f3816,f122,f390])).

fof(f3816,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f3805,f123])).

fof(f3805,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16 ),
    inference(trivial_inequality_removal,[],[f3777])).

fof(f3777,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16 ),
    inference(superposition,[],[f375,f123])).

fof(f3815,plain,
    ( ~ spl9_355
    | spl9_264
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f3814,f295,f122,f1067,f3639])).

fof(f3639,plain,
    ( spl9_355
  <=> sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_355])])).

fof(f3814,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f3776,f296])).

fof(f3776,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(superposition,[],[f375,f296])).

fof(f3813,plain,
    ( ~ spl9_353
    | spl9_228
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f3812,f266,f122,f917,f3634])).

fof(f3634,plain,
    ( spl9_353
  <=> sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_353])])).

fof(f3812,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f3775,f267])).

fof(f3775,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(superposition,[],[f375,f267])).

fof(f3811,plain,
    ( ~ spl9_351
    | spl9_252
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f3810,f286,f122,f1017,f3629])).

fof(f3629,plain,
    ( spl9_351
  <=> sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_351])])).

fof(f3810,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f3774,f287])).

fof(f3774,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(superposition,[],[f375,f287])).

fof(f3809,plain,
    ( ~ spl9_349
    | spl9_2
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3808,f358,f122,f3555,f3624])).

fof(f3624,plain,
    ( spl9_349
  <=> k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_349])])).

fof(f3808,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3772,f359])).

fof(f3772,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(superposition,[],[f375,f359])).

fof(f3807,plain,
    ( spl9_102
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f3806,f122,f390])).

fof(f3806,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f3771,f123])).

fof(f3771,plain,
    ( k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f123,f375])).

fof(f3770,plain,
    ( spl9_404
    | ~ spl9_76
    | spl9_347 ),
    inference(avatar_split_clause,[],[f3761,f3561,f303,f3768])).

fof(f3768,plain,
    ( spl9_404
  <=> k4_tarski(sK4(sK3,sK3),sK5(sK3,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_404])])).

fof(f3561,plain,
    ( spl9_347
  <=> k1_mcart_1(sK3) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_347])])).

fof(f3761,plain,
    ( k4_tarski(sK4(sK3,sK3),sK5(sK3,sK3)) = sK3
    | ~ spl9_76
    | ~ spl9_347 ),
    inference(unit_resulting_resolution,[],[f3562,f352])).

fof(f3562,plain,
    ( k1_mcart_1(sK3) != sK3
    | ~ spl9_347 ),
    inference(avatar_component_clause,[],[f3561])).

fof(f3766,plain,
    ( ~ spl9_403
    | ~ spl9_76
    | spl9_347 ),
    inference(avatar_split_clause,[],[f3762,f3561,f303,f3764])).

fof(f3764,plain,
    ( spl9_403
  <=> sK3 != sK4(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_403])])).

fof(f3762,plain,
    ( sK3 != sK4(sK3,sK3)
    | ~ spl9_76
    | ~ spl9_347 ),
    inference(unit_resulting_resolution,[],[f3562,f351])).

fof(f351,plain,
    ( ! [X0] :
        ( sK4(sK3,X0) != X0
        | k1_mcart_1(sK3) = X0 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f343,f304])).

fof(f343,plain,
    ( ! [X0] :
        ( sK4(sK3,X0) != X0
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = X0 )
    | ~ spl9_76 ),
    inference(superposition,[],[f79,f304])).

fof(f79,plain,(
    ! [X6,X7,X1] :
      ( sK4(k4_tarski(X6,X7),X1) != X1
      | k1_mcart_1(k4_tarski(X6,X7)) = X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X7,X1] :
      ( k1_mcart_1(X0) = X1
      | sK4(X0,X1) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3760,plain,
    ( spl9_338
    | ~ spl9_287
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3617,f303,f122,f3283,f3522])).

fof(f3617,plain,
    ( ! [X7] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k1_mcart_1(k4_tarski(sK6(sK3,X7),sK7(sK3,X7))) = sK6(sK3,X7)
        | k2_mcart_1(sK3) = X7 )
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f371,f362])).

fof(f371,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_16 ),
    inference(superposition,[],[f82,f123])).

fof(f3759,plain,
    ( spl9_334
    | ~ spl9_287
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3615,f303,f122,f3283,f3502])).

fof(f3615,plain,
    ( ! [X3] :
        ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k1_mcart_1(k4_tarski(sK4(sK3,X3),sK5(sK3,X3))) = sK4(sK3,X3)
        | k1_mcart_1(sK3) = X3 )
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f371,f352])).

fof(f3758,plain,
    ( ~ spl9_401
    | spl9_202
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f3754,f247,f122,f810,f3756])).

fof(f3754,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f3613,f248])).

fof(f3613,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(superposition,[],[f371,f248])).

fof(f3753,plain,
    ( ~ spl9_399
    | spl9_196
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f3749,f243,f122,f785,f3751])).

fof(f3749,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3612,f244])).

fof(f3612,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_16
    | ~ spl9_52 ),
    inference(superposition,[],[f371,f244])).

fof(f3748,plain,
    ( ~ spl9_397
    | spl9_190
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f3744,f239,f122,f760,f3746])).

fof(f3744,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f3611,f240])).

fof(f3611,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_16
    | ~ spl9_50 ),
    inference(superposition,[],[f371,f240])).

fof(f3743,plain,
    ( ~ spl9_395
    | spl9_184
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f3739,f235,f122,f735,f3741])).

fof(f3739,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f3610,f236])).

fof(f3610,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(superposition,[],[f371,f236])).

fof(f3738,plain,
    ( ~ spl9_393
    | spl9_178
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f3734,f231,f122,f710,f3736])).

fof(f3734,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3609,f232])).

fof(f3609,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_16
    | ~ spl9_46 ),
    inference(superposition,[],[f371,f232])).

fof(f3733,plain,
    ( ~ spl9_391
    | spl9_172
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f3729,f227,f122,f685,f3731])).

fof(f3729,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f3608,f228])).

fof(f3608,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_16
    | ~ spl9_44 ),
    inference(superposition,[],[f371,f228])).

fof(f3728,plain,
    ( ~ spl9_389
    | spl9_164
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f3724,f223,f122,f651,f3726])).

fof(f3724,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f3607,f224])).

fof(f3607,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(superposition,[],[f371,f224])).

fof(f3723,plain,
    ( ~ spl9_387
    | spl9_158
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f3719,f219,f122,f626,f3721])).

fof(f3719,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f3606,f220])).

fof(f3606,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_16
    | ~ spl9_40 ),
    inference(superposition,[],[f371,f220])).

fof(f3718,plain,
    ( ~ spl9_385
    | spl9_152
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f3714,f215,f122,f601,f3716])).

fof(f3714,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f3605,f216])).

fof(f3605,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_16
    | ~ spl9_38 ),
    inference(superposition,[],[f371,f216])).

fof(f3713,plain,
    ( ~ spl9_383
    | spl9_220
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f3709,f262,f122,f885,f3711])).

fof(f3709,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f3604,f263])).

fof(f3604,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_16
    | ~ spl9_60 ),
    inference(superposition,[],[f371,f263])).

fof(f3708,plain,
    ( ~ spl9_381
    | spl9_214
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f3704,f258,f122,f860,f3706])).

fof(f3704,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f3603,f259])).

fof(f3603,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_16
    | ~ spl9_58 ),
    inference(superposition,[],[f371,f259])).

fof(f3703,plain,
    ( ~ spl9_379
    | spl9_208
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f3699,f254,f122,f835,f3701])).

fof(f3699,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f3602,f255])).

fof(f3602,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_16
    | ~ spl9_56 ),
    inference(superposition,[],[f371,f255])).

fof(f3698,plain,
    ( ~ spl9_377
    | spl9_256
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f3694,f291,f122,f1035,f3696])).

fof(f3694,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f3601,f292])).

fof(f3601,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_16
    | ~ spl9_72 ),
    inference(superposition,[],[f371,f292])).

fof(f3693,plain,
    ( ~ spl9_375
    | spl9_126
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f3689,f162,f122,f492,f3691])).

fof(f3689,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3600,f163])).

fof(f3600,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_16
    | ~ spl9_28 ),
    inference(superposition,[],[f371,f163])).

fof(f3688,plain,
    ( ~ spl9_373
    | spl9_120
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f3684,f158,f122,f467,f3686])).

fof(f3684,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f3599,f159])).

fof(f3599,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_16
    | ~ spl9_26 ),
    inference(superposition,[],[f371,f159])).

fof(f3683,plain,
    ( ~ spl9_371
    | spl9_244
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f3679,f282,f122,f985,f3681])).

fof(f3679,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f3598,f283])).

fof(f3598,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_16
    | ~ spl9_68 ),
    inference(superposition,[],[f371,f283])).

fof(f3678,plain,
    ( ~ spl9_369
    | spl9_114
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f3674,f154,f122,f442,f3676])).

fof(f3674,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f3597,f155])).

fof(f3597,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_16
    | ~ spl9_24 ),
    inference(superposition,[],[f371,f155])).

fof(f3673,plain,
    ( ~ spl9_367
    | spl9_108
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f3669,f150,f122,f417,f3671])).

fof(f3669,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3596,f151])).

fof(f3596,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(superposition,[],[f371,f151])).

fof(f3668,plain,
    ( ~ spl9_365
    | spl9_232
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f3664,f270,f122,f935,f3666])).

fof(f3664,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f3595,f271])).

fof(f3595,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(superposition,[],[f371,f271])).

fof(f3663,plain,
    ( ~ spl9_363
    | spl9_146
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f3659,f179,f122,f576,f3661])).

fof(f3659,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f3594,f180])).

fof(f3594,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_34 ),
    inference(superposition,[],[f371,f180])).

fof(f3658,plain,
    ( ~ spl9_361
    | spl9_132
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f3654,f168,f122,f517,f3656])).

fof(f3654,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f3593,f169])).

fof(f3593,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_16
    | ~ spl9_30 ),
    inference(superposition,[],[f371,f169])).

fof(f3653,plain,
    ( ~ spl9_359
    | spl9_238
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f3649,f274,f122,f960,f3651])).

fof(f3649,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f3592,f275])).

fof(f3592,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_16
    | ~ spl9_66 ),
    inference(superposition,[],[f371,f275])).

fof(f3648,plain,
    ( ~ spl9_357
    | spl9_140
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f3644,f172,f122,f551,f3646])).

fof(f3644,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f3591,f173])).

fof(f3591,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_16
    | ~ spl9_32 ),
    inference(superposition,[],[f371,f173])).

fof(f3643,plain,
    ( spl9_100
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f3642,f122,f383])).

fof(f3642,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f3618,f123])).

fof(f3618,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16 ),
    inference(trivial_inequality_removal,[],[f3590])).

fof(f3590,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16 ),
    inference(superposition,[],[f371,f123])).

fof(f3641,plain,
    ( ~ spl9_355
    | spl9_262
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f3637,f295,f122,f1060,f3639])).

fof(f3637,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f3589,f296])).

fof(f3589,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_74 ),
    inference(superposition,[],[f371,f296])).

fof(f3636,plain,
    ( ~ spl9_353
    | spl9_226
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f3632,f266,f122,f910,f3634])).

fof(f3632,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f3588,f267])).

fof(f3588,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_16
    | ~ spl9_62 ),
    inference(superposition,[],[f371,f267])).

fof(f3631,plain,
    ( ~ spl9_351
    | spl9_250
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f3627,f286,f122,f1010,f3629])).

fof(f3627,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f3587,f287])).

fof(f3587,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_16
    | ~ spl9_70 ),
    inference(superposition,[],[f371,f287])).

fof(f3626,plain,
    ( ~ spl9_349
    | spl9_1
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3622,f358,f122,f88,f3624])).

fof(f3622,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f3621,f89])).

fof(f3621,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3585,f359])).

fof(f3585,plain,
    ( k1_mcart_1(sK3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_16
    | ~ spl9_96 ),
    inference(superposition,[],[f371,f359])).

fof(f3620,plain,
    ( spl9_100
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f3619,f122,f383])).

fof(f3619,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f3584,f123])).

fof(f3584,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f123,f371])).

fof(f3565,plain,
    ( ~ spl9_347
    | spl9_2
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3564,f358,f303,f3555,f3561])).

fof(f3564,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK3
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3539,f359])).

fof(f3539,plain,
    ( k1_mcart_1(sK3) != sK3
    | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(superposition,[],[f350,f359])).

fof(f350,plain,
    ( ! [X10,X11] :
        ( k4_tarski(X10,X11) != sK3
        | k2_mcart_1(k4_tarski(X10,X11)) = X11 )
    | ~ spl9_76 ),
    inference(superposition,[],[f86,f304])).

fof(f3563,plain,
    ( ~ spl9_347
    | spl9_1
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3559,f358,f303,f88,f3561])).

fof(f3559,plain,
    ( k1_mcart_1(sK3) != sK3
    | ~ spl9_1
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(subsumption_resolution,[],[f3558,f89])).

fof(f3558,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_mcart_1(sK3) != sK3
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3538,f359])).

fof(f3538,plain,
    ( k1_mcart_1(sK3) != sK3
    | k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)))
    | ~ spl9_76
    | ~ spl9_96 ),
    inference(superposition,[],[f346,f359])).

fof(f346,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK3
        | k1_mcart_1(k4_tarski(X4,X5)) = X4 )
    | ~ spl9_76 ),
    inference(superposition,[],[f82,f304])).

fof(f3557,plain,
    ( spl9_344
    | spl9_2
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f3550,f358,f3555,f3552])).

fof(f3550,plain,
    ( ! [X8,X9] :
        ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
        | k1_mcart_1(sK3) != k4_tarski(X8,X9) )
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f3536,f359])).

fof(f3536,plain,
    ( ! [X8,X9] :
        ( k1_mcart_1(sK3) != k4_tarski(X8,X9)
        | k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))) )
    | ~ spl9_96 ),
    inference(superposition,[],[f86,f359])).

fof(f3543,plain,
    ( spl9_342
    | ~ spl9_96
    | ~ spl9_274 ),
    inference(avatar_split_clause,[],[f3529,f1105,f358,f3541])).

fof(f3541,plain,
    ( spl9_342
  <=> k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_342])])).

fof(f1105,plain,
    ( spl9_274
  <=> k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_274])])).

fof(f3529,plain,
    ( k4_tarski(k1_mcart_1(sK3),k2_mcart_1(sK3)) = sK3
    | ~ spl9_96
    | ~ spl9_274 ),
    inference(backward_demodulation,[],[f359,f1106])).

fof(f1106,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) = sK3
    | ~ spl9_274 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f3528,plain,
    ( spl9_340
    | spl9_94
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3515,f303,f355,f3526])).

fof(f355,plain,
    ( spl9_94
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f3515,plain,
    ( ! [X14,X15,X16] :
        ( k4_tarski(X15,X16) != sK3
        | k2_mcart_1(k4_tarski(sK6(sK3,X14),sK7(sK3,X14))) = sK7(sK3,X14)
        | k2_mcart_1(sK3) = X14 )
    | ~ spl9_76 ),
    inference(superposition,[],[f86,f362])).

fof(f3524,plain,
    ( spl9_338
    | spl9_94
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3511,f303,f355,f3522])).

fof(f3511,plain,
    ( ! [X6,X4,X5] :
        ( k4_tarski(X5,X6) != sK3
        | k1_mcart_1(k4_tarski(sK6(sK3,X4),sK7(sK3,X4))) = sK6(sK3,X4)
        | k2_mcart_1(sK3) = X4 )
    | ~ spl9_76 ),
    inference(superposition,[],[f82,f362])).

fof(f3508,plain,
    ( spl9_336
    | spl9_94
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3495,f303,f355,f3506])).

fof(f3495,plain,
    ( ! [X14,X15,X16] :
        ( k4_tarski(X15,X16) != sK3
        | k2_mcart_1(k4_tarski(sK4(sK3,X14),sK5(sK3,X14))) = sK5(sK3,X14)
        | k1_mcart_1(sK3) = X14 )
    | ~ spl9_76 ),
    inference(superposition,[],[f86,f352])).

fof(f3504,plain,
    ( spl9_334
    | spl9_94
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3491,f303,f355,f3502])).

fof(f3491,plain,
    ( ! [X6,X4,X5] :
        ( k4_tarski(X5,X6) != sK3
        | k1_mcart_1(k4_tarski(sK4(sK3,X4),sK5(sK3,X4))) = sK4(sK3,X4)
        | k1_mcart_1(sK3) = X4 )
    | ~ spl9_76 ),
    inference(superposition,[],[f82,f352])).

fof(f3488,plain,
    ( ~ spl9_333
    | spl9_204
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3487,f303,f247,f817,f3398])).

fof(f3398,plain,
    ( spl9_333
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_333])])).

fof(f3487,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3432,f248])).

fof(f3432,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f248])).

fof(f3486,plain,
    ( ~ spl9_331
    | spl9_198
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3485,f303,f243,f792,f3393])).

fof(f3393,plain,
    ( spl9_331
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).

fof(f3485,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3431,f244])).

fof(f3431,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f244])).

fof(f3484,plain,
    ( ~ spl9_329
    | spl9_192
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3483,f303,f239,f767,f3388])).

fof(f3388,plain,
    ( spl9_329
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_329])])).

fof(f3483,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3430,f240])).

fof(f3430,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f240])).

fof(f3482,plain,
    ( ~ spl9_327
    | spl9_186
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3481,f303,f235,f742,f3383])).

fof(f3383,plain,
    ( spl9_327
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_327])])).

fof(f3481,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3429,f236])).

fof(f3429,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f236])).

fof(f3480,plain,
    ( ~ spl9_325
    | spl9_180
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3479,f303,f231,f717,f3378])).

fof(f3378,plain,
    ( spl9_325
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_325])])).

fof(f3479,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3428,f232])).

fof(f3428,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f232])).

fof(f3478,plain,
    ( ~ spl9_323
    | spl9_174
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3477,f303,f227,f692,f3373])).

fof(f3373,plain,
    ( spl9_323
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_323])])).

fof(f3477,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3427,f228])).

fof(f3427,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f228])).

fof(f3476,plain,
    ( ~ spl9_321
    | spl9_166
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3475,f303,f223,f658,f3368])).

fof(f3368,plain,
    ( spl9_321
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_321])])).

fof(f3475,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3426,f224])).

fof(f3426,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f224])).

fof(f3474,plain,
    ( ~ spl9_319
    | spl9_160
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3473,f303,f219,f633,f3363])).

fof(f3363,plain,
    ( spl9_319
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).

fof(f3473,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3425,f220])).

fof(f3425,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f220])).

fof(f3472,plain,
    ( ~ spl9_317
    | spl9_154
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3471,f303,f215,f608,f3358])).

fof(f3358,plain,
    ( spl9_317
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_317])])).

fof(f3471,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3424,f216])).

fof(f3424,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f216])).

fof(f3470,plain,
    ( ~ spl9_315
    | spl9_222
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3469,f303,f262,f892,f3353])).

fof(f3353,plain,
    ( spl9_315
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f3469,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3423,f263])).

fof(f3423,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f263])).

fof(f3468,plain,
    ( ~ spl9_313
    | spl9_216
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3467,f303,f258,f867,f3348])).

fof(f3348,plain,
    ( spl9_313
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_313])])).

fof(f3467,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3422,f259])).

fof(f3422,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f259])).

fof(f3466,plain,
    ( ~ spl9_311
    | spl9_210
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3465,f303,f254,f842,f3343])).

fof(f3343,plain,
    ( spl9_311
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_311])])).

fof(f3465,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3421,f255])).

fof(f3421,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f255])).

fof(f3464,plain,
    ( ~ spl9_309
    | spl9_258
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3463,f303,f291,f1042,f3338])).

fof(f3338,plain,
    ( spl9_309
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_309])])).

fof(f3463,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3420,f292])).

fof(f3420,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f292])).

fof(f3462,plain,
    ( ~ spl9_307
    | spl9_128
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3461,f303,f162,f499,f3333])).

fof(f3461,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3419,f163])).

fof(f3419,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f163])).

fof(f3460,plain,
    ( ~ spl9_305
    | spl9_122
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3459,f303,f158,f474,f3328])).

fof(f3459,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3418,f159])).

fof(f3418,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f159])).

fof(f3458,plain,
    ( ~ spl9_303
    | spl9_246
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3457,f303,f282,f992,f3323])).

fof(f3323,plain,
    ( spl9_303
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_303])])).

fof(f3457,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3417,f283])).

fof(f3417,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f283])).

fof(f3456,plain,
    ( ~ spl9_301
    | spl9_116
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3455,f303,f154,f449,f3318])).

fof(f3455,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3416,f155])).

fof(f3416,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f155])).

fof(f3454,plain,
    ( ~ spl9_299
    | spl9_110
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3453,f303,f150,f424,f3313])).

fof(f3453,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3415,f151])).

fof(f3415,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f151])).

fof(f3452,plain,
    ( ~ spl9_297
    | spl9_234
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3451,f303,f270,f942,f3308])).

fof(f3308,plain,
    ( spl9_297
  <=> sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_297])])).

fof(f3451,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3414,f271])).

fof(f3414,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f271])).

fof(f3450,plain,
    ( ~ spl9_295
    | spl9_148
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3449,f303,f179,f583,f3303])).

fof(f3449,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3413,f180])).

fof(f3413,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f180])).

fof(f3448,plain,
    ( ~ spl9_293
    | spl9_134
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3447,f303,f168,f524,f3298])).

fof(f3447,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3412,f169])).

fof(f3412,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f169])).

fof(f3446,plain,
    ( ~ spl9_291
    | spl9_240
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3445,f303,f274,f967,f3293])).

fof(f3293,plain,
    ( spl9_291
  <=> sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).

fof(f3445,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3411,f275])).

fof(f3411,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f275])).

fof(f3444,plain,
    ( ~ spl9_289
    | spl9_142
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3443,f303,f172,f558,f3288])).

fof(f3443,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3410,f173])).

fof(f3410,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f173])).

fof(f3442,plain,
    ( ~ spl9_287
    | spl9_102
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3441,f303,f122,f390,f3283])).

fof(f3441,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3409,f123])).

fof(f3409,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f123])).

fof(f3440,plain,
    ( ~ spl9_285
    | spl9_264
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3439,f303,f295,f1067,f3278])).

fof(f3278,plain,
    ( spl9_285
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_285])])).

fof(f3439,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3408,f296])).

fof(f3408,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f296])).

fof(f3438,plain,
    ( ~ spl9_283
    | spl9_228
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3437,f303,f266,f917,f3273])).

fof(f3273,plain,
    ( spl9_283
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_283])])).

fof(f3437,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3407,f267])).

fof(f3407,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f267])).

fof(f3436,plain,
    ( ~ spl9_281
    | spl9_252
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3435,f303,f286,f1017,f3268])).

fof(f3268,plain,
    ( spl9_281
  <=> sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_281])])).

fof(f3435,plain,
    ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3406,f287])).

fof(f3406,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(superposition,[],[f350,f287])).

fof(f3402,plain,
    ( spl9_96
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(avatar_split_clause,[],[f3401,f1105,f303,f358])).

fof(f3401,plain,
    ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(forward_demodulation,[],[f3263,f1106])).

fof(f3263,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(trivial_inequality_removal,[],[f3262])).

fof(f3262,plain,
    ( sK3 != sK3
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(superposition,[],[f346,f1106])).

fof(f3400,plain,
    ( ~ spl9_333
    | spl9_202
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3396,f303,f247,f810,f3398])).

fof(f3396,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3261,f248])).

fof(f3261,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
    | ~ spl9_54
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f248])).

fof(f3395,plain,
    ( ~ spl9_331
    | spl9_196
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3391,f303,f243,f785,f3393])).

fof(f3391,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3260,f244])).

fof(f3260,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
    | ~ spl9_52
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f244])).

fof(f3390,plain,
    ( ~ spl9_329
    | spl9_190
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3386,f303,f239,f760,f3388])).

fof(f3386,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3259,f240])).

fof(f3259,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
    | ~ spl9_50
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f240])).

fof(f3385,plain,
    ( ~ spl9_327
    | spl9_184
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3381,f303,f235,f735,f3383])).

fof(f3381,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3258,f236])).

fof(f3258,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
    | ~ spl9_48
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f236])).

fof(f3380,plain,
    ( ~ spl9_325
    | spl9_178
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3376,f303,f231,f710,f3378])).

fof(f3376,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3257,f232])).

fof(f3257,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
    | ~ spl9_46
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f232])).

fof(f3375,plain,
    ( ~ spl9_323
    | spl9_172
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3371,f303,f227,f685,f3373])).

fof(f3371,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3256,f228])).

fof(f3256,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
    | ~ spl9_44
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f228])).

fof(f3370,plain,
    ( ~ spl9_321
    | spl9_164
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3366,f303,f223,f651,f3368])).

fof(f3366,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3255,f224])).

fof(f3255,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
    | ~ spl9_42
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f224])).

fof(f3365,plain,
    ( ~ spl9_319
    | spl9_158
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3361,f303,f219,f626,f3363])).

fof(f3361,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3254,f220])).

fof(f3254,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
    | ~ spl9_40
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f220])).

fof(f3360,plain,
    ( ~ spl9_317
    | spl9_152
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3356,f303,f215,f601,f3358])).

fof(f3356,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3253,f216])).

fof(f3253,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
    | ~ spl9_38
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f216])).

fof(f3355,plain,
    ( ~ spl9_315
    | spl9_220
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3351,f303,f262,f885,f3353])).

fof(f3351,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3252,f263])).

fof(f3252,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
    | ~ spl9_60
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f263])).

fof(f3350,plain,
    ( ~ spl9_313
    | spl9_214
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3346,f303,f258,f860,f3348])).

fof(f3346,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3251,f259])).

fof(f3251,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
    | ~ spl9_58
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f259])).

fof(f3345,plain,
    ( ~ spl9_311
    | spl9_208
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3341,f303,f254,f835,f3343])).

fof(f3341,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3250,f255])).

fof(f3250,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
    | ~ spl9_56
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f255])).

fof(f3340,plain,
    ( ~ spl9_309
    | spl9_256
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3336,f303,f291,f1035,f3338])).

fof(f3336,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3249,f292])).

fof(f3249,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
    | ~ spl9_72
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f292])).

fof(f3335,plain,
    ( ~ spl9_307
    | spl9_126
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3331,f303,f162,f492,f3333])).

fof(f3331,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3248,f163])).

fof(f3248,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
    | ~ spl9_28
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f163])).

fof(f3330,plain,
    ( ~ spl9_305
    | spl9_120
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3326,f303,f158,f467,f3328])).

fof(f3326,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3247,f159])).

fof(f3247,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
    | ~ spl9_26
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f159])).

fof(f3325,plain,
    ( ~ spl9_303
    | spl9_244
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3321,f303,f282,f985,f3323])).

fof(f3321,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3246,f283])).

fof(f3246,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
    | ~ spl9_68
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f283])).

fof(f3320,plain,
    ( ~ spl9_301
    | spl9_114
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3316,f303,f154,f442,f3318])).

fof(f3316,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3245,f155])).

fof(f3245,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
    | ~ spl9_24
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f155])).

fof(f3315,plain,
    ( ~ spl9_299
    | spl9_108
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3311,f303,f150,f417,f3313])).

fof(f3311,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3244,f151])).

fof(f3244,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
    | ~ spl9_22
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f151])).

fof(f3310,plain,
    ( ~ spl9_297
    | spl9_232
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3306,f303,f270,f935,f3308])).

fof(f3306,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3243,f271])).

fof(f3243,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
    | ~ spl9_64
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f271])).

fof(f3305,plain,
    ( ~ spl9_295
    | spl9_146
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3301,f303,f179,f576,f3303])).

fof(f3301,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3242,f180])).

fof(f3242,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
    | ~ spl9_34
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f180])).

fof(f3300,plain,
    ( ~ spl9_293
    | spl9_132
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3296,f303,f168,f517,f3298])).

fof(f3296,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3241,f169])).

fof(f3241,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
    | ~ spl9_30
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f169])).

fof(f3295,plain,
    ( ~ spl9_291
    | spl9_238
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3291,f303,f274,f960,f3293])).

fof(f3291,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3240,f275])).

fof(f3240,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
    | ~ spl9_66
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f275])).

fof(f3290,plain,
    ( ~ spl9_289
    | spl9_140
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3286,f303,f172,f551,f3288])).

fof(f3286,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3239,f173])).

fof(f3239,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
    | ~ spl9_32
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f173])).

fof(f3285,plain,
    ( ~ spl9_287
    | spl9_100
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3281,f303,f122,f383,f3283])).

fof(f3281,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3238,f123])).

fof(f3238,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
    | ~ spl9_16
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f123])).

fof(f3280,plain,
    ( ~ spl9_285
    | spl9_262
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3276,f303,f295,f1060,f3278])).

fof(f3276,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3237,f296])).

fof(f3237,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
    | ~ spl9_74
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f296])).

fof(f3275,plain,
    ( ~ spl9_283
    | spl9_226
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3271,f303,f266,f910,f3273])).

fof(f3271,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3236,f267])).

fof(f3236,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
    | ~ spl9_62
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f267])).

fof(f3270,plain,
    ( ~ spl9_281
    | spl9_250
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f3266,f303,f286,f1010,f3268])).

fof(f3266,plain,
    ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f3235,f287])).

fof(f3235,plain,
    ( sK3 != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
    | ~ spl9_70
    | ~ spl9_76 ),
    inference(superposition,[],[f346,f287])).

fof(f3265,plain,
    ( spl9_96
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(avatar_split_clause,[],[f3264,f1105,f303,f358])).

fof(f3264,plain,
    ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(forward_demodulation,[],[f3232,f1106])).

fof(f3232,plain,
    ( k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_76
    | ~ spl9_274 ),
    inference(unit_resulting_resolution,[],[f1106,f346])).

fof(f3231,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3230])).

fof(f3230,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(subsumption_resolution,[],[f3161,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',existence_m1_subset_1)).

fof(f3161,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK2,sK2)),k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f111,f103,f103,f1058,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f74,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',d3_mcart_1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',t48_mcart_1)).

fof(f1058,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_260 ),
    inference(avatar_component_clause,[],[f1057])).

fof(f1057,plain,
    ( spl9_260
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_260])])).

fof(f103,plain,
    ( k1_xboole_0 != sK2
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_9
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f111,plain,
    ( k1_xboole_0 != sK0
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_13
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f3229,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3228])).

fof(f3228,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(subsumption_resolution,[],[f3186,f103])).

fof(f3186,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f1058,f78])).

fof(f3227,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3226])).

fof(f3226,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(subsumption_resolution,[],[f3187,f103])).

fof(f3187,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f1058,f78])).

fof(f3225,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3224])).

fof(f3224,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(subsumption_resolution,[],[f3188,f111])).

fof(f3188,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f1058,f78])).

fof(f3223,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3189])).

fof(f3189,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f111,f103,f103,f67,f1058,f78])).

fof(f3222,plain,
    ( ~ spl9_74
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3158])).

fof(f3158,plain,
    ( $false
    | ~ spl9_74
    | ~ spl9_260 ),
    inference(unit_resulting_resolution,[],[f296,f1058])).

fof(f3221,plain,
    ( ~ spl9_74
    | ~ spl9_260 ),
    inference(avatar_contradiction_clause,[],[f3220])).

fof(f3220,plain,
    ( $false
    | ~ spl9_74
    | ~ spl9_260 ),
    inference(trivial_inequality_removal,[],[f3194])).

fof(f3194,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK2)) != sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_74
    | ~ spl9_260 ),
    inference(superposition,[],[f1058,f296])).

fof(f3157,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3156])).

fof(f3156,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(subsumption_resolution,[],[f3096,f67])).

fof(f3096,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK2,sK1)),k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f111,f103,f107,f1033,f78])).

fof(f1033,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_254 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl9_254
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_254])])).

fof(f107,plain,
    ( k1_xboole_0 != sK1
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl9_11
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f3155,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3154])).

fof(f3154,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(subsumption_resolution,[],[f3112,f107])).

fof(f3112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f1033,f78])).

fof(f3153,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3152])).

fof(f3152,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(subsumption_resolution,[],[f3113,f103])).

fof(f3113,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f1033,f78])).

fof(f3151,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3150])).

fof(f3150,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(subsumption_resolution,[],[f3114,f111])).

fof(f3114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f1033,f78])).

fof(f3149,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3115])).

fof(f3115,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f111,f103,f107,f67,f1033,f78])).

fof(f3148,plain,
    ( ~ spl9_72
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | ~ spl9_72
    | ~ spl9_254 ),
    inference(unit_resulting_resolution,[],[f292,f1033])).

fof(f3147,plain,
    ( ~ spl9_72
    | ~ spl9_254 ),
    inference(avatar_contradiction_clause,[],[f3146])).

fof(f3146,plain,
    ( $false
    | ~ spl9_72
    | ~ spl9_254 ),
    inference(trivial_inequality_removal,[],[f3132])).

fof(f3132,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK1)) != sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_72
    | ~ spl9_254 ),
    inference(superposition,[],[f1033,f292])).

fof(f3083,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3082])).

fof(f3082,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(subsumption_resolution,[],[f3016,f67])).

fof(f3016,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK1,sK2)),k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f111,f107,f103,f1008,f78])).

fof(f1008,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_248 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl9_248
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f3081,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3080])).

fof(f3080,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(subsumption_resolution,[],[f3038,f103])).

fof(f3038,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f1008,f78])).

fof(f3079,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3078])).

fof(f3078,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(subsumption_resolution,[],[f3039,f107])).

fof(f3039,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f1008,f78])).

fof(f3077,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3076])).

fof(f3076,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(subsumption_resolution,[],[f3040,f111])).

fof(f3040,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f1008,f78])).

fof(f3075,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3041])).

fof(f3041,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f111,f107,f103,f67,f1008,f78])).

fof(f3074,plain,
    ( ~ spl9_70
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3010])).

fof(f3010,plain,
    ( $false
    | ~ spl9_70
    | ~ spl9_248 ),
    inference(unit_resulting_resolution,[],[f287,f1008])).

fof(f3073,plain,
    ( ~ spl9_70
    | ~ spl9_248 ),
    inference(avatar_contradiction_clause,[],[f3072])).

fof(f3072,plain,
    ( $false
    | ~ spl9_70
    | ~ spl9_248 ),
    inference(trivial_inequality_removal,[],[f3044])).

fof(f3044,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK2)) != sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_70
    | ~ spl9_248 ),
    inference(superposition,[],[f1008,f287])).

fof(f3009,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f3008])).

fof(f3008,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(subsumption_resolution,[],[f2951,f67])).

fof(f2951,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK1,sK1)),k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f111,f107,f107,f983,f78])).

fof(f983,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_242 ),
    inference(avatar_component_clause,[],[f982])).

fof(f982,plain,
    ( spl9_242
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f3007,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f3006])).

fof(f3006,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(subsumption_resolution,[],[f2964,f107])).

fof(f2964,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f983,f78])).

fof(f3005,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f3004])).

fof(f3004,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(subsumption_resolution,[],[f2965,f107])).

fof(f2965,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f983,f78])).

fof(f3003,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f3002])).

fof(f3002,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(subsumption_resolution,[],[f2966,f111])).

fof(f2966,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f983,f78])).

fof(f3001,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f2967])).

fof(f2967,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f111,f107,f107,f67,f983,f78])).

fof(f3000,plain,
    ( ~ spl9_68
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f2936])).

fof(f2936,plain,
    ( $false
    | ~ spl9_68
    | ~ spl9_242 ),
    inference(unit_resulting_resolution,[],[f283,f983])).

fof(f2999,plain,
    ( ~ spl9_68
    | ~ spl9_242 ),
    inference(avatar_contradiction_clause,[],[f2998])).

fof(f2998,plain,
    ( $false
    | ~ spl9_68
    | ~ spl9_242 ),
    inference(trivial_inequality_removal,[],[f2981])).

fof(f2981,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK1)) != sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_68
    | ~ spl9_242 ),
    inference(superposition,[],[f983,f283])).

fof(f2935,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2934])).

fof(f2934,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(subsumption_resolution,[],[f2869,f67])).

fof(f2869,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK0,sK2)),k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f103,f111,f103,f958,f78])).

fof(f958,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_236 ),
    inference(avatar_component_clause,[],[f957])).

fof(f957,plain,
    ( spl9_236
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_236])])).

fof(f2933,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2932])).

fof(f2932,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(subsumption_resolution,[],[f2890,f103])).

fof(f2890,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f958,f78])).

fof(f2931,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2930])).

fof(f2930,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(subsumption_resolution,[],[f2891,f111])).

fof(f2891,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f958,f78])).

fof(f2929,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2928])).

fof(f2928,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(subsumption_resolution,[],[f2892,f103])).

fof(f2892,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f958,f78])).

fof(f2927,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2893])).

fof(f2893,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f103,f111,f103,f67,f958,f78])).

fof(f2926,plain,
    ( ~ spl9_66
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2862])).

fof(f2862,plain,
    ( $false
    | ~ spl9_66
    | ~ spl9_236 ),
    inference(unit_resulting_resolution,[],[f275,f958])).

fof(f2925,plain,
    ( ~ spl9_66
    | ~ spl9_236 ),
    inference(avatar_contradiction_clause,[],[f2924])).

fof(f2924,plain,
    ( $false
    | ~ spl9_66
    | ~ spl9_236 ),
    inference(trivial_inequality_removal,[],[f2901])).

fof(f2901,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK2)) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_66
    | ~ spl9_236 ),
    inference(superposition,[],[f958,f275])).

fof(f2861,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2860])).

fof(f2860,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(subsumption_resolution,[],[f2796,f67])).

fof(f2796,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK0,sK2)),k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f107,f111,f103,f933,f78])).

fof(f933,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_230 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl9_230
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_230])])).

fof(f2859,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2858])).

fof(f2858,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(subsumption_resolution,[],[f2816,f103])).

fof(f2816,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f933,f78])).

fof(f2857,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2856])).

fof(f2856,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(subsumption_resolution,[],[f2817,f111])).

fof(f2817,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f933,f78])).

fof(f2855,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2854])).

fof(f2854,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(subsumption_resolution,[],[f2818,f107])).

fof(f2818,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f933,f78])).

fof(f2853,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2819])).

fof(f2819,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f107,f111,f103,f67,f933,f78])).

fof(f2852,plain,
    ( ~ spl9_64
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2788])).

fof(f2788,plain,
    ( $false
    | ~ spl9_64
    | ~ spl9_230 ),
    inference(unit_resulting_resolution,[],[f271,f933])).

fof(f2851,plain,
    ( ~ spl9_64
    | ~ spl9_230 ),
    inference(avatar_contradiction_clause,[],[f2850])).

fof(f2850,plain,
    ( $false
    | ~ spl9_64
    | ~ spl9_230 ),
    inference(trivial_inequality_removal,[],[f2830])).

fof(f2830,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK2)) != sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_64
    | ~ spl9_230 ),
    inference(superposition,[],[f933,f271])).

fof(f2787,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2786])).

fof(f2786,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(subsumption_resolution,[],[f2723,f67])).

fof(f2723,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK0,sK2)),k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f111,f111,f103,f908,f78])).

fof(f908,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_224 ),
    inference(avatar_component_clause,[],[f907])).

fof(f907,plain,
    ( spl9_224
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_224])])).

fof(f2785,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2784])).

fof(f2784,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(subsumption_resolution,[],[f2742,f103])).

fof(f2742,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f908,f78])).

fof(f2783,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2782])).

fof(f2782,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(subsumption_resolution,[],[f2743,f111])).

fof(f2743,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f908,f78])).

fof(f2781,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2780])).

fof(f2780,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(subsumption_resolution,[],[f2744,f111])).

fof(f2744,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f908,f78])).

fof(f2779,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2745])).

fof(f2745,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f111,f111,f103,f67,f908,f78])).

fof(f2778,plain,
    ( ~ spl9_62
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2714])).

fof(f2714,plain,
    ( $false
    | ~ spl9_62
    | ~ spl9_224 ),
    inference(unit_resulting_resolution,[],[f267,f908])).

fof(f2777,plain,
    ( ~ spl9_62
    | ~ spl9_224 ),
    inference(avatar_contradiction_clause,[],[f2776])).

fof(f2776,plain,
    ( $false
    | ~ spl9_62
    | ~ spl9_224 ),
    inference(trivial_inequality_removal,[],[f2749])).

fof(f2749,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK2)) != sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_62
    | ~ spl9_224 ),
    inference(superposition,[],[f908,f267])).

fof(f2713,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2712])).

fof(f2712,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(subsumption_resolution,[],[f2656,f67])).

fof(f2656,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK0,sK1)),k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f103,f111,f107,f883,f78])).

fof(f883,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_218 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl9_218
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).

fof(f2711,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2710])).

fof(f2710,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(subsumption_resolution,[],[f2668,f107])).

fof(f2668,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f883,f78])).

fof(f2709,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2708])).

fof(f2708,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(subsumption_resolution,[],[f2669,f111])).

fof(f2669,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f883,f78])).

fof(f2707,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2706])).

fof(f2706,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(subsumption_resolution,[],[f2670,f103])).

fof(f2670,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f883,f78])).

fof(f2705,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2671])).

fof(f2671,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f103,f111,f107,f67,f883,f78])).

fof(f2704,plain,
    ( ~ spl9_60
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2640])).

fof(f2640,plain,
    ( $false
    | ~ spl9_60
    | ~ spl9_218 ),
    inference(unit_resulting_resolution,[],[f263,f883])).

fof(f2703,plain,
    ( ~ spl9_60
    | ~ spl9_218 ),
    inference(avatar_contradiction_clause,[],[f2702])).

fof(f2702,plain,
    ( $false
    | ~ spl9_60
    | ~ spl9_218 ),
    inference(trivial_inequality_removal,[],[f2691])).

fof(f2691,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK1)) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_60
    | ~ spl9_218 ),
    inference(superposition,[],[f883,f263])).

fof(f2639,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2638])).

fof(f2638,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f2583,f67])).

fof(f2583,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK0,sK1)),k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f107,f111,f107,f858,f78])).

fof(f858,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_212 ),
    inference(avatar_component_clause,[],[f857])).

fof(f857,plain,
    ( spl9_212
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f2637,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2636])).

fof(f2636,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f2594,f107])).

fof(f2594,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f858,f78])).

fof(f2635,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2634])).

fof(f2634,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f2595,f111])).

fof(f2595,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f858,f78])).

fof(f2633,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2632])).

fof(f2632,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(subsumption_resolution,[],[f2596,f107])).

fof(f2596,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f858,f78])).

fof(f2631,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2597])).

fof(f2597,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f107,f111,f107,f67,f858,f78])).

fof(f2630,plain,
    ( ~ spl9_58
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2566])).

fof(f2566,plain,
    ( $false
    | ~ spl9_58
    | ~ spl9_212 ),
    inference(unit_resulting_resolution,[],[f259,f858])).

fof(f2629,plain,
    ( ~ spl9_58
    | ~ spl9_212 ),
    inference(avatar_contradiction_clause,[],[f2628])).

fof(f2628,plain,
    ( $false
    | ~ spl9_58
    | ~ spl9_212 ),
    inference(trivial_inequality_removal,[],[f2616])).

fof(f2616,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK1)) != sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_58
    | ~ spl9_212 ),
    inference(superposition,[],[f858,f259])).

fof(f2565,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2564])).

fof(f2564,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(subsumption_resolution,[],[f2510,f67])).

fof(f2510,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK0,sK1)),k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f111,f111,f107,f833,f78])).

fof(f833,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_206 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl9_206
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_206])])).

fof(f2563,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2562])).

fof(f2562,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(subsumption_resolution,[],[f2520,f107])).

fof(f2520,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f833,f78])).

fof(f2561,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2560])).

fof(f2560,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(subsumption_resolution,[],[f2521,f111])).

fof(f2521,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f833,f78])).

fof(f2559,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2558])).

fof(f2558,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(subsumption_resolution,[],[f2522,f111])).

fof(f2522,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f833,f78])).

fof(f2557,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2523])).

fof(f2523,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f111,f111,f107,f67,f833,f78])).

fof(f2556,plain,
    ( ~ spl9_56
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2492])).

fof(f2492,plain,
    ( $false
    | ~ spl9_56
    | ~ spl9_206 ),
    inference(unit_resulting_resolution,[],[f255,f833])).

fof(f2555,plain,
    ( ~ spl9_56
    | ~ spl9_206 ),
    inference(avatar_contradiction_clause,[],[f2554])).

fof(f2554,plain,
    ( $false
    | ~ spl9_56
    | ~ spl9_206 ),
    inference(trivial_inequality_removal,[],[f2541])).

fof(f2541,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK1)) != sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_56
    | ~ spl9_206 ),
    inference(superposition,[],[f833,f255])).

fof(f2491,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2490])).

fof(f2490,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f2437,f67])).

fof(f2437,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK2,sK0)),k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f103,f103,f111,f808,f78])).

fof(f808,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_200 ),
    inference(avatar_component_clause,[],[f807])).

fof(f807,plain,
    ( spl9_200
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_200])])).

fof(f2489,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2488])).

fof(f2488,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f2446,f111])).

fof(f2446,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f808,f78])).

fof(f2487,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2486])).

fof(f2486,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f2447,f103])).

fof(f2447,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f808,f78])).

fof(f2485,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2484])).

fof(f2484,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f2448,f103])).

fof(f2448,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f808,f78])).

fof(f2483,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2449])).

fof(f2449,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f103,f103,f111,f67,f808,f78])).

fof(f2482,plain,
    ( ~ spl9_54
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2418])).

fof(f2418,plain,
    ( $false
    | ~ spl9_54
    | ~ spl9_200 ),
    inference(unit_resulting_resolution,[],[f248,f808])).

fof(f2481,plain,
    ( ~ spl9_54
    | ~ spl9_200 ),
    inference(avatar_contradiction_clause,[],[f2480])).

fof(f2480,plain,
    ( $false
    | ~ spl9_54
    | ~ spl9_200 ),
    inference(trivial_inequality_removal,[],[f2478])).

fof(f2478,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK0)) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_54
    | ~ spl9_200 ),
    inference(superposition,[],[f808,f248])).

fof(f2417,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2416])).

fof(f2416,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(subsumption_resolution,[],[f2364,f67])).

fof(f2364,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK2,sK0)),k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f107,f103,f111,f783,f78])).

fof(f783,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_194 ),
    inference(avatar_component_clause,[],[f782])).

fof(f782,plain,
    ( spl9_194
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).

fof(f2415,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2414])).

fof(f2414,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(subsumption_resolution,[],[f2372,f111])).

fof(f2372,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f783,f78])).

fof(f2413,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2412])).

fof(f2412,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(subsumption_resolution,[],[f2373,f103])).

fof(f2373,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f783,f78])).

fof(f2411,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2410])).

fof(f2410,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(subsumption_resolution,[],[f2374,f107])).

fof(f2374,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f783,f78])).

fof(f2409,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2375])).

fof(f2375,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f107,f103,f111,f67,f783,f78])).

fof(f2408,plain,
    ( ~ spl9_52
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2344])).

fof(f2344,plain,
    ( $false
    | ~ spl9_52
    | ~ spl9_194 ),
    inference(unit_resulting_resolution,[],[f244,f783])).

fof(f2407,plain,
    ( ~ spl9_52
    | ~ spl9_194 ),
    inference(avatar_contradiction_clause,[],[f2406])).

fof(f2406,plain,
    ( $false
    | ~ spl9_52
    | ~ spl9_194 ),
    inference(trivial_inequality_removal,[],[f2403])).

fof(f2403,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK0)) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_52
    | ~ spl9_194 ),
    inference(superposition,[],[f783,f244])).

fof(f2343,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2342])).

fof(f2342,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(subsumption_resolution,[],[f2291,f67])).

fof(f2291,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK2,sK0)),k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f111,f103,f111,f758,f78])).

fof(f758,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_188 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl9_188
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_188])])).

fof(f2341,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2340])).

fof(f2340,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(subsumption_resolution,[],[f2298,f111])).

fof(f2298,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f758,f78])).

fof(f2339,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2338])).

fof(f2338,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(subsumption_resolution,[],[f2299,f103])).

fof(f2299,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f758,f78])).

fof(f2337,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2336])).

fof(f2336,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(subsumption_resolution,[],[f2300,f111])).

fof(f2300,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f758,f78])).

fof(f2335,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2301])).

fof(f2301,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f111,f103,f111,f67,f758,f78])).

fof(f2334,plain,
    ( ~ spl9_50
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2270])).

fof(f2270,plain,
    ( $false
    | ~ spl9_50
    | ~ spl9_188 ),
    inference(unit_resulting_resolution,[],[f240,f758])).

fof(f2333,plain,
    ( ~ spl9_50
    | ~ spl9_188 ),
    inference(avatar_contradiction_clause,[],[f2332])).

fof(f2332,plain,
    ( $false
    | ~ spl9_50
    | ~ spl9_188 ),
    inference(trivial_inequality_removal,[],[f2328])).

fof(f2328,plain,
    ( sK8(k3_zfmisc_1(sK0,sK2,sK0)) != sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_50
    | ~ spl9_188 ),
    inference(superposition,[],[f758,f240])).

fof(f2269,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2268])).

fof(f2268,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(subsumption_resolution,[],[f2218,f67])).

fof(f2218,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK1,sK0)),k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f103,f107,f111,f733,f78])).

fof(f733,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_182 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl9_182
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f2267,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2266])).

fof(f2266,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(subsumption_resolution,[],[f2224,f111])).

fof(f2224,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f733,f78])).

fof(f2265,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2264])).

fof(f2264,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(subsumption_resolution,[],[f2225,f107])).

fof(f2225,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f733,f78])).

fof(f2263,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2262])).

fof(f2262,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(subsumption_resolution,[],[f2226,f103])).

fof(f2226,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f733,f78])).

fof(f2261,plain,
    ( spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2227])).

fof(f2227,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f103,f107,f111,f67,f733,f78])).

fof(f2260,plain,
    ( ~ spl9_48
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2196])).

fof(f2196,plain,
    ( $false
    | ~ spl9_48
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f236,f733])).

fof(f2259,plain,
    ( ~ spl9_48
    | ~ spl9_182 ),
    inference(avatar_contradiction_clause,[],[f2258])).

fof(f2258,plain,
    ( $false
    | ~ spl9_48
    | ~ spl9_182 ),
    inference(trivial_inequality_removal,[],[f2253])).

fof(f2253,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK0)) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_48
    | ~ spl9_182 ),
    inference(superposition,[],[f733,f236])).

fof(f2195,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2194])).

fof(f2194,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(subsumption_resolution,[],[f2145,f67])).

fof(f2145,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK1,sK0)),k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f107,f107,f111,f708,f78])).

fof(f708,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_176 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl9_176
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_176])])).

fof(f2193,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2192])).

fof(f2192,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(subsumption_resolution,[],[f2150,f111])).

fof(f2150,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f708,f78])).

fof(f2191,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2190])).

fof(f2190,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(subsumption_resolution,[],[f2151,f107])).

fof(f2151,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f708,f78])).

fof(f2189,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2188])).

fof(f2188,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(subsumption_resolution,[],[f2152,f107])).

fof(f2152,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f708,f78])).

fof(f2187,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2153])).

fof(f2153,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f107,f107,f111,f67,f708,f78])).

fof(f2186,plain,
    ( ~ spl9_46
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2122])).

fof(f2122,plain,
    ( $false
    | ~ spl9_46
    | ~ spl9_176 ),
    inference(unit_resulting_resolution,[],[f232,f708])).

fof(f2185,plain,
    ( ~ spl9_46
    | ~ spl9_176 ),
    inference(avatar_contradiction_clause,[],[f2184])).

fof(f2184,plain,
    ( $false
    | ~ spl9_46
    | ~ spl9_176 ),
    inference(trivial_inequality_removal,[],[f2178])).

fof(f2178,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK0)) != sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_46
    | ~ spl9_176 ),
    inference(superposition,[],[f708,f232])).

fof(f2121,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2120])).

fof(f2120,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(subsumption_resolution,[],[f2072,f67])).

fof(f2072,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK1,sK0)),k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f111,f107,f111,f683,f78])).

fof(f683,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_170 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl9_170
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).

fof(f2119,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2118])).

fof(f2118,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(subsumption_resolution,[],[f2076,f111])).

fof(f2076,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f683,f78])).

fof(f2117,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2116])).

fof(f2116,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(subsumption_resolution,[],[f2077,f107])).

fof(f2077,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f683,f78])).

fof(f2115,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2114])).

fof(f2114,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(subsumption_resolution,[],[f2078,f111])).

fof(f2078,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f683,f78])).

fof(f2113,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2079])).

fof(f2079,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f111,f107,f111,f67,f683,f78])).

fof(f2112,plain,
    ( ~ spl9_44
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2048])).

fof(f2048,plain,
    ( $false
    | ~ spl9_44
    | ~ spl9_170 ),
    inference(unit_resulting_resolution,[],[f228,f683])).

fof(f2111,plain,
    ( ~ spl9_44
    | ~ spl9_170 ),
    inference(avatar_contradiction_clause,[],[f2110])).

fof(f2110,plain,
    ( $false
    | ~ spl9_44
    | ~ spl9_170 ),
    inference(trivial_inequality_removal,[],[f2103])).

fof(f2103,plain,
    ( sK8(k3_zfmisc_1(sK0,sK1,sK0)) != sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_44
    | ~ spl9_170 ),
    inference(superposition,[],[f683,f228])).

fof(f2046,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2045])).

fof(f2045,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(subsumption_resolution,[],[f1998,f67])).

fof(f1998,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK0,sK0)),k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f103,f111,f111,f649,f78])).

fof(f649,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f648])).

fof(f648,plain,
    ( spl9_162
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f2044,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2043])).

fof(f2043,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(subsumption_resolution,[],[f2001,f111])).

fof(f2001,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f649,f78])).

fof(f2042,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2041])).

fof(f2041,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(subsumption_resolution,[],[f2002,f111])).

fof(f2002,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f649,f78])).

fof(f2040,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2039])).

fof(f2039,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(subsumption_resolution,[],[f2003,f103])).

fof(f2003,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f649,f78])).

fof(f2038,plain,
    ( spl9_9
    | spl9_13
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2004])).

fof(f2004,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f103,f111,f111,f67,f649,f78])).

fof(f2037,plain,
    ( ~ spl9_42
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f1973])).

fof(f1973,plain,
    ( $false
    | ~ spl9_42
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f224,f649])).

fof(f2036,plain,
    ( ~ spl9_42
    | ~ spl9_162 ),
    inference(avatar_contradiction_clause,[],[f2035])).

fof(f2035,plain,
    ( $false
    | ~ spl9_42
    | ~ spl9_162 ),
    inference(trivial_inequality_removal,[],[f2027])).

fof(f2027,plain,
    ( sK8(k3_zfmisc_1(sK2,sK0,sK0)) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_42
    | ~ spl9_162 ),
    inference(superposition,[],[f649,f224])).

fof(f1972,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1971])).

fof(f1971,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1925,f67])).

fof(f1925,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK0,sK0)),k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f107,f111,f111,f624,f78])).

fof(f624,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl9_156
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f1970,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1969])).

fof(f1969,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1927,f111])).

fof(f1927,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f624,f78])).

fof(f1968,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1967])).

fof(f1967,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1928,f111])).

fof(f1928,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f624,f78])).

fof(f1966,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1965])).

fof(f1965,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1929,f107])).

fof(f1929,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f624,f78])).

fof(f1964,plain,
    ( spl9_11
    | spl9_13
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1930])).

fof(f1930,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f107,f111,f111,f67,f624,f78])).

fof(f1963,plain,
    ( ~ spl9_40
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1899])).

fof(f1899,plain,
    ( $false
    | ~ spl9_40
    | ~ spl9_156 ),
    inference(unit_resulting_resolution,[],[f220,f624])).

fof(f1962,plain,
    ( ~ spl9_40
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f1961])).

fof(f1961,plain,
    ( $false
    | ~ spl9_40
    | ~ spl9_156 ),
    inference(trivial_inequality_removal,[],[f1952])).

fof(f1952,plain,
    ( sK8(k3_zfmisc_1(sK1,sK0,sK0)) != sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_40
    | ~ spl9_156 ),
    inference(superposition,[],[f624,f220])).

fof(f1898,plain,
    ( spl9_13
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1897])).

fof(f1897,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f1852,f67])).

fof(f1852,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK0,sK0,sK0)),k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f111,f111,f111,f599,f78])).

fof(f599,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_150 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl9_150
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_150])])).

fof(f1896,plain,
    ( spl9_13
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1895])).

fof(f1895,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f1853,f111])).

fof(f1853,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f599,f78])).

fof(f1894,plain,
    ( spl9_13
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1893])).

fof(f1893,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f1854,f111])).

fof(f1854,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f599,f78])).

fof(f1892,plain,
    ( spl9_13
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f1855,f111])).

fof(f1855,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f599,f78])).

fof(f1890,plain,
    ( spl9_13
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1856])).

fof(f1856,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f111,f111,f111,f67,f599,f78])).

fof(f1889,plain,
    ( ~ spl9_38
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1825])).

fof(f1825,plain,
    ( $false
    | ~ spl9_38
    | ~ spl9_150 ),
    inference(unit_resulting_resolution,[],[f216,f599])).

fof(f1888,plain,
    ( ~ spl9_38
    | ~ spl9_150 ),
    inference(avatar_contradiction_clause,[],[f1887])).

fof(f1887,plain,
    ( $false
    | ~ spl9_38
    | ~ spl9_150 ),
    inference(trivial_inequality_removal,[],[f1877])).

fof(f1877,plain,
    ( sK8(k3_zfmisc_1(sK0,sK0,sK0)) != sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_38
    | ~ spl9_150 ),
    inference(superposition,[],[f599,f216])).

fof(f1824,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1823])).

fof(f1823,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f1753,f67])).

fof(f1753,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK2,sK2)),k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f107,f103,f103,f574,f78])).

fof(f574,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl9_144
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f1822,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1821])).

fof(f1821,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f1779,f103])).

fof(f1779,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f574,f78])).

fof(f1820,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f1780,f103])).

fof(f1780,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f574,f78])).

fof(f1818,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1817])).

fof(f1817,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(subsumption_resolution,[],[f1781,f107])).

fof(f1781,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f574,f78])).

fof(f1816,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1782])).

fof(f1782,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f107,f103,f103,f67,f574,f78])).

fof(f1815,plain,
    ( ~ spl9_34
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1751])).

fof(f1751,plain,
    ( $false
    | ~ spl9_34
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f180,f574])).

fof(f1814,plain,
    ( ~ spl9_34
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f1813])).

fof(f1813,plain,
    ( $false
    | ~ spl9_34
    | ~ spl9_144 ),
    inference(trivial_inequality_removal,[],[f1792])).

fof(f1792,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK2)) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_34
    | ~ spl9_144 ),
    inference(superposition,[],[f574,f180])).

fof(f1750,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1749])).

fof(f1749,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(subsumption_resolution,[],[f1681,f67])).

fof(f1681,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK1,sK2)),k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f103,f107,f103,f549,f78])).

fof(f549,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_138 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl9_138
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f1748,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1747])).

fof(f1747,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(subsumption_resolution,[],[f1705,f103])).

fof(f1705,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f549,f78])).

fof(f1746,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1745])).

fof(f1745,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(subsumption_resolution,[],[f1706,f107])).

fof(f1706,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f549,f78])).

fof(f1744,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1743])).

fof(f1743,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(subsumption_resolution,[],[f1707,f103])).

fof(f1707,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f549,f78])).

fof(f1742,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1708])).

fof(f1708,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f103,f107,f103,f67,f549,f78])).

fof(f1741,plain,
    ( ~ spl9_32
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1677])).

fof(f1677,plain,
    ( $false
    | ~ spl9_32
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f173,f549])).

fof(f1740,plain,
    ( ~ spl9_32
    | ~ spl9_138 ),
    inference(avatar_contradiction_clause,[],[f1739])).

fof(f1739,plain,
    ( $false
    | ~ spl9_32
    | ~ spl9_138 ),
    inference(trivial_inequality_removal,[],[f1715])).

fof(f1715,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK2)) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_32
    | ~ spl9_138 ),
    inference(superposition,[],[f549,f173])).

fof(f1676,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1675])).

fof(f1675,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(subsumption_resolution,[],[f1608,f67])).

fof(f1608,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK1,sK2)),k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f107,f107,f103,f515,f78])).

fof(f515,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_130 ),
    inference(avatar_component_clause,[],[f514])).

fof(f514,plain,
    ( spl9_130
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f1674,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1673])).

fof(f1673,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(subsumption_resolution,[],[f1631,f103])).

fof(f1631,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f515,f78])).

fof(f1672,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1671])).

fof(f1671,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(subsumption_resolution,[],[f1632,f107])).

fof(f1632,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f515,f78])).

fof(f1670,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(subsumption_resolution,[],[f1633,f107])).

fof(f1633,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f515,f78])).

fof(f1668,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1634])).

fof(f1634,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f107,f107,f103,f67,f515,f78])).

fof(f1667,plain,
    ( ~ spl9_30
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1603])).

fof(f1603,plain,
    ( $false
    | ~ spl9_30
    | ~ spl9_130 ),
    inference(unit_resulting_resolution,[],[f169,f515])).

fof(f1666,plain,
    ( ~ spl9_30
    | ~ spl9_130 ),
    inference(avatar_contradiction_clause,[],[f1665])).

fof(f1665,plain,
    ( $false
    | ~ spl9_30
    | ~ spl9_130 ),
    inference(trivial_inequality_removal,[],[f1643])).

fof(f1643,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK2)) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_30
    | ~ spl9_130 ),
    inference(superposition,[],[f515,f169])).

fof(f1602,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f1539,f67])).

fof(f1539,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK2,sK1)),k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f103,f103,f107,f490,f78])).

fof(f490,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl9_124
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f1600,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1599])).

fof(f1599,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f1557,f107])).

fof(f1557,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f490,f78])).

fof(f1598,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1597])).

fof(f1597,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f1558,f103])).

fof(f1558,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f490,f78])).

fof(f1596,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1595])).

fof(f1595,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f1559,f103])).

fof(f1559,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f490,f78])).

fof(f1594,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1560])).

fof(f1560,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f103,f103,f107,f67,f490,f78])).

fof(f1593,plain,
    ( ~ spl9_28
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1529])).

fof(f1529,plain,
    ( $false
    | ~ spl9_28
    | ~ spl9_124 ),
    inference(unit_resulting_resolution,[],[f163,f490])).

fof(f1592,plain,
    ( ~ spl9_28
    | ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f1591])).

fof(f1591,plain,
    ( $false
    | ~ spl9_28
    | ~ spl9_124 ),
    inference(trivial_inequality_removal,[],[f1576])).

fof(f1576,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK1)) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_28
    | ~ spl9_124 ),
    inference(superposition,[],[f490,f163])).

fof(f1528,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1527])).

fof(f1527,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(subsumption_resolution,[],[f1466,f67])).

fof(f1466,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK2,sK1)),k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f107,f103,f107,f465,f78])).

fof(f465,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_118 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl9_118
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f1526,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1525])).

fof(f1525,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(subsumption_resolution,[],[f1483,f107])).

fof(f1483,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f465,f78])).

fof(f1524,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1523])).

fof(f1523,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(subsumption_resolution,[],[f1484,f103])).

fof(f1484,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f465,f78])).

fof(f1522,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1521])).

fof(f1521,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(subsumption_resolution,[],[f1485,f107])).

fof(f1485,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f465,f78])).

fof(f1520,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1486])).

fof(f1486,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f107,f103,f107,f67,f465,f78])).

fof(f1519,plain,
    ( ~ spl9_26
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1455])).

fof(f1455,plain,
    ( $false
    | ~ spl9_26
    | ~ spl9_118 ),
    inference(unit_resulting_resolution,[],[f159,f465])).

fof(f1518,plain,
    ( ~ spl9_26
    | ~ spl9_118 ),
    inference(avatar_contradiction_clause,[],[f1517])).

fof(f1517,plain,
    ( $false
    | ~ spl9_26
    | ~ spl9_118 ),
    inference(trivial_inequality_removal,[],[f1501])).

fof(f1501,plain,
    ( sK8(k3_zfmisc_1(sK1,sK2,sK1)) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_26
    | ~ spl9_118 ),
    inference(superposition,[],[f465,f159])).

fof(f1454,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1453])).

fof(f1453,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(subsumption_resolution,[],[f1394,f67])).

fof(f1394,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK1,sK1)),k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f103,f107,f107,f440,f78])).

fof(f440,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_112 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl9_112
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f1452,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1451])).

fof(f1451,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(subsumption_resolution,[],[f1409,f107])).

fof(f1409,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f440,f78])).

fof(f1450,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1449])).

fof(f1449,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(subsumption_resolution,[],[f1410,f107])).

fof(f1410,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f440,f78])).

fof(f1448,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1447])).

fof(f1447,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(subsumption_resolution,[],[f1411,f103])).

fof(f1411,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f440,f78])).

fof(f1446,plain,
    ( spl9_9
    | spl9_11
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1412])).

fof(f1412,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f103,f107,f107,f67,f440,f78])).

fof(f1445,plain,
    ( ~ spl9_24
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1381])).

fof(f1381,plain,
    ( $false
    | ~ spl9_24
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f155,f440])).

fof(f1444,plain,
    ( ~ spl9_24
    | ~ spl9_112 ),
    inference(avatar_contradiction_clause,[],[f1443])).

fof(f1443,plain,
    ( $false
    | ~ spl9_24
    | ~ spl9_112 ),
    inference(trivial_inequality_removal,[],[f1425])).

fof(f1425,plain,
    ( sK8(k3_zfmisc_1(sK2,sK1,sK1)) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_24
    | ~ spl9_112 ),
    inference(superposition,[],[f440,f155])).

fof(f1380,plain,
    ( spl9_11
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1379])).

fof(f1379,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f1321,f67])).

fof(f1321,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK1,sK1,sK1)),k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f107,f107,f107,f415,f78])).

fof(f415,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl9_106
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f1378,plain,
    ( spl9_11
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1377])).

fof(f1377,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f1335,f107])).

fof(f1335,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f415,f78])).

fof(f1376,plain,
    ( spl9_11
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1375])).

fof(f1375,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f1336,f107])).

fof(f1336,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f415,f78])).

fof(f1374,plain,
    ( spl9_11
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1373])).

fof(f1373,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f1337,f107])).

fof(f1337,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f415,f78])).

fof(f1372,plain,
    ( spl9_11
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1338])).

fof(f1338,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f107,f107,f107,f67,f415,f78])).

fof(f1371,plain,
    ( ~ spl9_22
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | ~ spl9_22
    | ~ spl9_106 ),
    inference(unit_resulting_resolution,[],[f151,f415])).

fof(f1370,plain,
    ( ~ spl9_22
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f1369])).

fof(f1369,plain,
    ( $false
    | ~ spl9_22
    | ~ spl9_106 ),
    inference(trivial_inequality_removal,[],[f1350])).

fof(f1350,plain,
    ( sK8(k3_zfmisc_1(sK1,sK1,sK1)) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_22
    | ~ spl9_106 ),
    inference(superposition,[],[f415,f151])).

fof(f1306,plain,
    ( spl9_9
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1305])).

fof(f1305,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f1234,f67])).

fof(f1234,plain,
    ( ~ m1_subset_1(sK8(k3_zfmisc_1(sK2,sK2,sK2)),k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f103,f103,f103,f381,f78])).

fof(f381,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl9_98
  <=> ! [X3,X2] : k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f1304,plain,
    ( spl9_9
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1303])).

fof(f1303,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f1261,f103])).

fof(f1261,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f381,f78])).

fof(f1302,plain,
    ( spl9_9
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1301])).

fof(f1301,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f1262,f103])).

fof(f1262,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f381,f78])).

fof(f1300,plain,
    ( spl9_9
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1299])).

fof(f1299,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f1263,f103])).

fof(f1263,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f381,f78])).

fof(f1298,plain,
    ( spl9_9
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1264])).

fof(f1264,plain,
    ( $false
    | ~ spl9_9
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f103,f103,f103,f67,f381,f78])).

fof(f1297,plain,
    ( ~ spl9_16
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1233])).

fof(f1233,plain,
    ( $false
    | ~ spl9_16
    | ~ spl9_98 ),
    inference(unit_resulting_resolution,[],[f123,f381])).

fof(f1296,plain,
    ( ~ spl9_16
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f1295])).

fof(f1295,plain,
    ( $false
    | ~ spl9_16
    | ~ spl9_98 ),
    inference(trivial_inequality_removal,[],[f1270])).

fof(f1270,plain,
    ( sK8(k3_zfmisc_1(sK2,sK2,sK2)) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_16
    | ~ spl9_98 ),
    inference(superposition,[],[f381,f123])).

fof(f1229,plain,
    ( ~ spl9_271
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f1226,f340,f1093])).

fof(f1093,plain,
    ( spl9_271
  <=> ~ r2_hidden(sK2,k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_271])])).

fof(f340,plain,
    ( spl9_92
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f1226,plain,
    ( ~ r2_hidden(sK2,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f341,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',antisymmetry_r2_hidden)).

fof(f341,plain,
    ( r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK3),sK2)
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f340])).

fof(f1228,plain,
    ( ~ spl9_271
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f1227,f340,f1093])).

fof(f1227,plain,
    ( ~ r2_hidden(sK2,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f341,f68])).

fof(f1223,plain,
    ( ~ spl9_279
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f1217,f1101,f1220])).

fof(f1220,plain,
    ( spl9_279
  <=> ~ r2_hidden(sK2,k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_279])])).

fof(f1101,plain,
    ( spl9_272
  <=> r2_hidden(k2_mcart_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f1217,plain,
    ( ~ r2_hidden(sK2,k2_mcart_1(sK3))
    | ~ spl9_272 ),
    inference(unit_resulting_resolution,[],[f1102,f68])).

fof(f1102,plain,
    ( r2_hidden(k2_mcart_1(sK3),sK2)
    | ~ spl9_272 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1222,plain,
    ( ~ spl9_279
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f1218,f1101,f1220])).

fof(f1218,plain,
    ( ~ r2_hidden(sK2,k2_mcart_1(sK3))
    | ~ spl9_272 ),
    inference(unit_resulting_resolution,[],[f1102,f68])).

fof(f1214,plain,
    ( spl9_94
    | spl9_4
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f1213,f303,f365,f355])).

fof(f365,plain,
    ( spl9_4
  <=> k2_mcart_1(sK3) = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1213,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK3) = k7_mcart_1(sK0,sK1,sK2,sK3)
        | k4_tarski(X8,X9) != sK3 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f1205,f304])).

fof(f1205,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK3
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = k7_mcart_1(sK0,sK1,sK2,sK3) )
    | ~ spl9_76 ),
    inference(superposition,[],[f86,f304])).

fof(f1210,plain,
    ( spl9_94
    | spl9_96
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f1209,f303,f358,f355])).

fof(f1209,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
        | k4_tarski(X2,X3) != sK3 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f1201,f304])).

fof(f1201,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK3
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) )
    | ~ spl9_76 ),
    inference(superposition,[],[f82,f304])).

fof(f1196,plain,
    ( spl9_94
    | spl9_96
    | ~ spl9_274 ),
    inference(avatar_split_clause,[],[f1195,f1105,f358,f355])).

fof(f1195,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
        | k4_tarski(X2,X3) != sK3 )
    | ~ spl9_274 ),
    inference(forward_demodulation,[],[f1187,f1106])).

fof(f1187,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK3
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) )
    | ~ spl9_274 ),
    inference(superposition,[],[f82,f1106])).

fof(f1184,plain,
    ( spl9_92
    | spl9_15
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f1183,f315,f118,f340])).

fof(f118,plain,
    ( spl9_15
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f315,plain,
    ( spl9_82
  <=> m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f1183,plain,
    ( r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK3),sK2)
    | ~ spl9_15
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f119,f316,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',t2_subset)).

fof(f316,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK3),sK2)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f315])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1182,plain,
    ( spl9_272
    | spl9_15
    | ~ spl9_276 ),
    inference(avatar_split_clause,[],[f1181,f1109,f118,f1101])).

fof(f1109,plain,
    ( spl9_276
  <=> m1_subset_1(k2_mcart_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_276])])).

fof(f1181,plain,
    ( r2_hidden(k2_mcart_1(sK3),sK2)
    | ~ spl9_15
    | ~ spl9_276 ),
    inference(unit_resulting_resolution,[],[f119,f1110,f70])).

fof(f1110,plain,
    ( m1_subset_1(k2_mcart_1(sK3),sK2)
    | ~ spl9_276 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1180,plain,
    ( ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f1117,f99])).

fof(f99,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_6
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1117,plain,
    ( ~ m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f111,f107,f103,f356,f78])).

fof(f356,plain,
    ( ! [X2,X3] : k4_tarski(X2,X3) != sK3
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f355])).

fof(f1178,plain,
    ( ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f1177])).

fof(f1177,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f1139,f103])).

fof(f1139,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f111,f107,f99,f356,f78])).

fof(f1176,plain,
    ( ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f1175])).

fof(f1175,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f1140,f107])).

fof(f1140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f111,f103,f99,f356,f78])).

fof(f1174,plain,
    ( ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f1173])).

fof(f1173,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f1141,f111])).

fof(f1141,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f107,f103,f99,f356,f78])).

fof(f1172,plain,
    ( ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13
    | ~ spl9_94 ),
    inference(avatar_contradiction_clause,[],[f1142])).

fof(f1142,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_94 ),
    inference(unit_resulting_resolution,[],[f111,f107,f103,f99,f356,f78])).

fof(f1111,plain,
    ( spl9_276
    | ~ spl9_4
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f1099,f315,f365,f1109])).

fof(f1099,plain,
    ( m1_subset_1(k2_mcart_1(sK3),sK2)
    | ~ spl9_4
    | ~ spl9_82 ),
    inference(backward_demodulation,[],[f366,f316])).

fof(f366,plain,
    ( k2_mcart_1(sK3) = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f365])).

fof(f1107,plain,
    ( spl9_274
    | ~ spl9_4
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f1098,f303,f365,f1105])).

fof(f1098,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k2_mcart_1(sK3)) = sK3
    | ~ spl9_4
    | ~ spl9_76 ),
    inference(backward_demodulation,[],[f366,f304])).

fof(f1103,plain,
    ( spl9_272
    | ~ spl9_4
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f1097,f340,f365,f1101])).

fof(f1097,plain,
    ( r2_hidden(k2_mcart_1(sK3),sK2)
    | ~ spl9_4
    | ~ spl9_92 ),
    inference(backward_demodulation,[],[f366,f341])).

fof(f1096,plain,
    ( ~ spl9_271
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f1090,f340,f1093])).

fof(f1090,plain,
    ( ~ r2_hidden(sK2,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f341,f68])).

fof(f1095,plain,
    ( ~ spl9_271
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f1091,f340,f1093])).

fof(f1091,plain,
    ( ~ r2_hidden(sK2,k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f341,f68])).

fof(f1087,plain,
    ( ~ spl9_269
    | ~ spl9_90 ),
    inference(avatar_split_clause,[],[f1081,f335,f1084])).

fof(f1084,plain,
    ( spl9_269
  <=> ~ r2_hidden(sK1,k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_269])])).

fof(f335,plain,
    ( spl9_90
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f1081,plain,
    ( ~ r2_hidden(sK1,k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_90 ),
    inference(unit_resulting_resolution,[],[f336,f68])).

fof(f336,plain,
    ( r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),sK1)
    | ~ spl9_90 ),
    inference(avatar_component_clause,[],[f335])).

fof(f1086,plain,
    ( ~ spl9_269
    | ~ spl9_90 ),
    inference(avatar_split_clause,[],[f1082,f335,f1084])).

fof(f1082,plain,
    ( ~ r2_hidden(sK1,k6_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_90 ),
    inference(unit_resulting_resolution,[],[f336,f68])).

fof(f1078,plain,
    ( ~ spl9_267
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f1072,f330,f1075])).

fof(f1075,plain,
    ( spl9_267
  <=> ~ r2_hidden(sK0,k5_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_267])])).

fof(f330,plain,
    ( spl9_88
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f1072,plain,
    ( ~ r2_hidden(sK0,k5_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_88 ),
    inference(unit_resulting_resolution,[],[f331,f68])).

fof(f331,plain,
    ( r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),sK0)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f330])).

fof(f1077,plain,
    ( ~ spl9_267
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f1073,f330,f1075])).

fof(f1073,plain,
    ( ~ r2_hidden(sK0,k5_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl9_88 ),
    inference(unit_resulting_resolution,[],[f331,f68])).

fof(f1069,plain,
    ( spl9_260
    | spl9_264
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f1065,f295,f1067,f1057])).

fof(f1065,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK2)) )
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f1051,f296])).

fof(f1051,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))) )
    | ~ spl9_74 ),
    inference(superposition,[],[f86,f296])).

fof(f1062,plain,
    ( spl9_260
    | spl9_262
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f1055,f295,f1060,f1057])).

fof(f1055,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK2))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK2)) )
    | ~ spl9_74 ),
    inference(forward_demodulation,[],[f1047,f296])).

fof(f1047,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))) )
    | ~ spl9_74 ),
    inference(superposition,[],[f82,f296])).

fof(f1044,plain,
    ( spl9_254
    | spl9_258
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f1040,f291,f1042,f1032])).

fof(f1040,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK1)) )
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f1026,f292])).

fof(f1026,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))) )
    | ~ spl9_72 ),
    inference(superposition,[],[f86,f292])).

fof(f1037,plain,
    ( spl9_254
    | spl9_256
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f1030,f291,f1035,f1032])).

fof(f1030,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK1))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK1)) )
    | ~ spl9_72 ),
    inference(forward_demodulation,[],[f1022,f292])).

fof(f1022,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))) )
    | ~ spl9_72 ),
    inference(superposition,[],[f82,f292])).

fof(f1019,plain,
    ( spl9_248
    | spl9_252
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f1015,f286,f1017,f1007])).

fof(f1015,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK2)) )
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f1001,f287])).

fof(f1001,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))) )
    | ~ spl9_70 ),
    inference(superposition,[],[f86,f287])).

fof(f1012,plain,
    ( spl9_248
    | spl9_250
    | ~ spl9_70 ),
    inference(avatar_split_clause,[],[f1005,f286,f1010,f1007])).

fof(f1005,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK2))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK2)) )
    | ~ spl9_70 ),
    inference(forward_demodulation,[],[f997,f287])).

fof(f997,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))) )
    | ~ spl9_70 ),
    inference(superposition,[],[f82,f287])).

fof(f994,plain,
    ( spl9_242
    | spl9_246
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f990,f282,f992,f982])).

fof(f990,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK1)) )
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f976,f283])).

fof(f976,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))) )
    | ~ spl9_68 ),
    inference(superposition,[],[f86,f283])).

fof(f987,plain,
    ( spl9_242
    | spl9_244
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f980,f282,f985,f982])).

fof(f980,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK1))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK1)) )
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f972,f283])).

fof(f972,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))) )
    | ~ spl9_68 ),
    inference(superposition,[],[f82,f283])).

fof(f969,plain,
    ( spl9_236
    | spl9_240
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f965,f274,f967,f957])).

fof(f965,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) )
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f951,f275])).

fof(f951,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))) )
    | ~ spl9_66 ),
    inference(superposition,[],[f86,f275])).

fof(f962,plain,
    ( spl9_236
    | spl9_238
    | ~ spl9_66 ),
    inference(avatar_split_clause,[],[f955,f274,f960,f957])).

fof(f955,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK2))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK2)) )
    | ~ spl9_66 ),
    inference(forward_demodulation,[],[f947,f275])).

fof(f947,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))) )
    | ~ spl9_66 ),
    inference(superposition,[],[f82,f275])).

fof(f944,plain,
    ( spl9_230
    | spl9_234
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f940,f270,f942,f932])).

fof(f940,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK2)) )
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f926,f271])).

fof(f926,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))) )
    | ~ spl9_64 ),
    inference(superposition,[],[f86,f271])).

fof(f937,plain,
    ( spl9_230
    | spl9_232
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f930,f270,f935,f932])).

fof(f930,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK2))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK2)) )
    | ~ spl9_64 ),
    inference(forward_demodulation,[],[f922,f271])).

fof(f922,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))) )
    | ~ spl9_64 ),
    inference(superposition,[],[f82,f271])).

fof(f919,plain,
    ( spl9_224
    | spl9_228
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f915,f266,f917,f907])).

fof(f915,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK2)) )
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f901,f267])).

fof(f901,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))) )
    | ~ spl9_62 ),
    inference(superposition,[],[f86,f267])).

fof(f912,plain,
    ( spl9_224
    | spl9_226
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f905,f266,f910,f907])).

fof(f905,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK2))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK2)) )
    | ~ spl9_62 ),
    inference(forward_demodulation,[],[f897,f267])).

fof(f897,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) )
    | ~ spl9_62 ),
    inference(superposition,[],[f82,f267])).

fof(f894,plain,
    ( spl9_218
    | spl9_222
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f890,f262,f892,f882])).

fof(f890,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) )
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f876,f263])).

fof(f876,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))) )
    | ~ spl9_60 ),
    inference(superposition,[],[f86,f263])).

fof(f887,plain,
    ( spl9_218
    | spl9_220
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f880,f262,f885,f882])).

fof(f880,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK1))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK1)) )
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f872,f263])).

fof(f872,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))) )
    | ~ spl9_60 ),
    inference(superposition,[],[f82,f263])).

fof(f869,plain,
    ( spl9_212
    | spl9_216
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f865,f258,f867,f857])).

fof(f865,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK1)) )
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f851,f259])).

fof(f851,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))) )
    | ~ spl9_58 ),
    inference(superposition,[],[f86,f259])).

fof(f862,plain,
    ( spl9_212
    | spl9_214
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f855,f258,f860,f857])).

fof(f855,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK1))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK1)) )
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f847,f259])).

fof(f847,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))) )
    | ~ spl9_58 ),
    inference(superposition,[],[f82,f259])).

fof(f844,plain,
    ( spl9_206
    | spl9_210
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f840,f254,f842,f832])).

fof(f840,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK1)) )
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f826,f255])).

fof(f826,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))) )
    | ~ spl9_56 ),
    inference(superposition,[],[f86,f255])).

fof(f837,plain,
    ( spl9_206
    | spl9_208
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f830,f254,f835,f832])).

fof(f830,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK1))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK1)) )
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f822,f255])).

fof(f822,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) )
    | ~ spl9_56 ),
    inference(superposition,[],[f82,f255])).

fof(f819,plain,
    ( spl9_200
    | spl9_204
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f815,f247,f817,f807])).

fof(f815,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) )
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f801,f248])).

fof(f801,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))) )
    | ~ spl9_54 ),
    inference(superposition,[],[f86,f248])).

fof(f812,plain,
    ( spl9_200
    | spl9_202
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f805,f247,f810,f807])).

fof(f805,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK0))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK0)) )
    | ~ spl9_54 ),
    inference(forward_demodulation,[],[f797,f248])).

fof(f797,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))) )
    | ~ spl9_54 ),
    inference(superposition,[],[f82,f248])).

fof(f794,plain,
    ( spl9_194
    | spl9_198
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f790,f243,f792,f782])).

fof(f790,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK0)) )
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f776,f244])).

fof(f776,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))) )
    | ~ spl9_52 ),
    inference(superposition,[],[f86,f244])).

fof(f787,plain,
    ( spl9_194
    | spl9_196
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f780,f243,f785,f782])).

fof(f780,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK0))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK0)) )
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f772,f244])).

fof(f772,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))) )
    | ~ spl9_52 ),
    inference(superposition,[],[f82,f244])).

fof(f769,plain,
    ( spl9_188
    | spl9_192
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f765,f239,f767,f757])).

fof(f765,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK0)) )
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f751,f240])).

fof(f751,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK2,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))) )
    | ~ spl9_50 ),
    inference(superposition,[],[f86,f240])).

fof(f762,plain,
    ( spl9_188
    | spl9_190
    | ~ spl9_50 ),
    inference(avatar_split_clause,[],[f755,f239,f760,f757])).

fof(f755,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK2,sK0))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK0)) )
    | ~ spl9_50 ),
    inference(forward_demodulation,[],[f747,f240])).

fof(f747,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK2,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) )
    | ~ spl9_50 ),
    inference(superposition,[],[f82,f240])).

fof(f744,plain,
    ( spl9_182
    | spl9_186
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f740,f235,f742,f732])).

fof(f740,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) )
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f726,f236])).

fof(f726,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))) )
    | ~ spl9_48 ),
    inference(superposition,[],[f86,f236])).

fof(f737,plain,
    ( spl9_182
    | spl9_184
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f730,f235,f735,f732])).

fof(f730,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK0))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK0)) )
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f722,f236])).

fof(f722,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))) )
    | ~ spl9_48 ),
    inference(superposition,[],[f82,f236])).

fof(f719,plain,
    ( spl9_176
    | spl9_180
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f715,f231,f717,f707])).

fof(f715,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK0)) )
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f701,f232])).

fof(f701,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))) )
    | ~ spl9_46 ),
    inference(superposition,[],[f86,f232])).

fof(f712,plain,
    ( spl9_176
    | spl9_178
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f705,f231,f710,f707])).

fof(f705,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK0))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK0)) )
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f697,f232])).

fof(f697,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))) )
    | ~ spl9_46 ),
    inference(superposition,[],[f82,f232])).

fof(f694,plain,
    ( spl9_170
    | spl9_174
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f690,f227,f692,f682])).

fof(f690,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK0)) )
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f676,f228])).

fof(f676,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK1,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))) )
    | ~ spl9_44 ),
    inference(superposition,[],[f86,f228])).

fof(f687,plain,
    ( spl9_170
    | spl9_172
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f680,f227,f685,f682])).

fof(f680,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK1,sK0))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK0)) )
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f672,f228])).

fof(f672,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK1,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) )
    | ~ spl9_44 ),
    inference(superposition,[],[f82,f228])).

fof(f669,plain,
    ( ~ spl9_169
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f663,f325,f666])).

fof(f666,plain,
    ( spl9_169
  <=> ~ r2_hidden(sK0,sK8(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_169])])).

fof(f325,plain,
    ( spl9_86
  <=> r2_hidden(sK8(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f663,plain,
    ( ~ r2_hidden(sK0,sK8(sK0))
    | ~ spl9_86 ),
    inference(unit_resulting_resolution,[],[f326,f68])).

fof(f326,plain,
    ( r2_hidden(sK8(sK0),sK0)
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f325])).

fof(f668,plain,
    ( ~ spl9_169
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f664,f325,f666])).

fof(f664,plain,
    ( ~ r2_hidden(sK0,sK8(sK0))
    | ~ spl9_86 ),
    inference(unit_resulting_resolution,[],[f326,f68])).

fof(f660,plain,
    ( spl9_162
    | spl9_166
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f656,f223,f658,f648])).

fof(f656,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) )
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f642,f224])).

fof(f642,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))) )
    | ~ spl9_42 ),
    inference(superposition,[],[f86,f224])).

fof(f653,plain,
    ( spl9_162
    | spl9_164
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f646,f223,f651,f648])).

fof(f646,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK0,sK0))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK0)) )
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f638,f224])).

fof(f638,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK0,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) )
    | ~ spl9_42 ),
    inference(superposition,[],[f82,f224])).

fof(f635,plain,
    ( spl9_156
    | spl9_160
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f631,f219,f633,f623])).

fof(f631,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK0)) )
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f617,f220])).

fof(f617,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK0,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))) )
    | ~ spl9_40 ),
    inference(superposition,[],[f86,f220])).

fof(f628,plain,
    ( spl9_156
    | spl9_158
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f621,f219,f626,f623])).

fof(f621,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK0,sK0))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK0)) )
    | ~ spl9_40 ),
    inference(forward_demodulation,[],[f613,f220])).

fof(f613,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK0,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) )
    | ~ spl9_40 ),
    inference(superposition,[],[f82,f220])).

fof(f610,plain,
    ( spl9_150
    | spl9_154
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f606,f215,f608,f598])).

fof(f606,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK0)) )
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f592,f216])).

fof(f592,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK0,sK0,sK0))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))) )
    | ~ spl9_38 ),
    inference(superposition,[],[f86,f216])).

fof(f603,plain,
    ( spl9_150
    | spl9_152
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f596,f215,f601,f598])).

fof(f596,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK0,sK0,sK0))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK0)) )
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f588,f216])).

fof(f588,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK0,sK0,sK0))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))))) = k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) )
    | ~ spl9_38 ),
    inference(superposition,[],[f82,f216])).

fof(f585,plain,
    ( spl9_144
    | spl9_148
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f581,f179,f583,f573])).

fof(f581,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) )
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f567,f180])).

fof(f567,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))) )
    | ~ spl9_34 ),
    inference(superposition,[],[f86,f180])).

fof(f578,plain,
    ( spl9_144
    | spl9_146
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f571,f179,f576,f573])).

fof(f571,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK2))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK2)) )
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f563,f180])).

fof(f563,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))) )
    | ~ spl9_34 ),
    inference(superposition,[],[f82,f180])).

fof(f560,plain,
    ( spl9_138
    | spl9_142
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f556,f172,f558,f548])).

fof(f556,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) )
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f542,f173])).

fof(f542,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))) )
    | ~ spl9_32 ),
    inference(superposition,[],[f86,f173])).

fof(f553,plain,
    ( spl9_138
    | spl9_140
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f546,f172,f551,f548])).

fof(f546,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK2))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK2)) )
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f538,f173])).

fof(f538,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))) )
    | ~ spl9_32 ),
    inference(superposition,[],[f82,f173])).

fof(f535,plain,
    ( ~ spl9_137
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f529,f320,f532])).

fof(f532,plain,
    ( spl9_137
  <=> ~ r2_hidden(sK1,sK8(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f320,plain,
    ( spl9_84
  <=> r2_hidden(sK8(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f529,plain,
    ( ~ r2_hidden(sK1,sK8(sK1))
    | ~ spl9_84 ),
    inference(unit_resulting_resolution,[],[f321,f68])).

fof(f321,plain,
    ( r2_hidden(sK8(sK1),sK1)
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f320])).

fof(f534,plain,
    ( ~ spl9_137
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f530,f320,f532])).

fof(f530,plain,
    ( ~ r2_hidden(sK1,sK8(sK1))
    | ~ spl9_84 ),
    inference(unit_resulting_resolution,[],[f321,f68])).

fof(f526,plain,
    ( spl9_130
    | spl9_134
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f522,f168,f524,f514])).

fof(f522,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) )
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f508,f169])).

fof(f508,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))) )
    | ~ spl9_30 ),
    inference(superposition,[],[f86,f169])).

fof(f519,plain,
    ( spl9_130
    | spl9_132
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f512,f168,f517,f514])).

fof(f512,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK2))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK2)) )
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f504,f169])).

fof(f504,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) )
    | ~ spl9_30 ),
    inference(superposition,[],[f82,f169])).

fof(f501,plain,
    ( spl9_124
    | spl9_128
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f497,f162,f499,f489])).

fof(f497,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) )
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f483,f163])).

fof(f483,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))) )
    | ~ spl9_28 ),
    inference(superposition,[],[f86,f163])).

fof(f494,plain,
    ( spl9_124
    | spl9_126
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f487,f162,f492,f489])).

fof(f487,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK1))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK1)) )
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f479,f163])).

fof(f479,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))) )
    | ~ spl9_28 ),
    inference(superposition,[],[f82,f163])).

fof(f476,plain,
    ( spl9_118
    | spl9_122
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f472,f158,f474,f464])).

fof(f472,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) )
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f458,f159])).

fof(f458,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))) )
    | ~ spl9_26 ),
    inference(superposition,[],[f86,f159])).

fof(f469,plain,
    ( spl9_118
    | spl9_120
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f462,f158,f467,f464])).

fof(f462,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK2,sK1))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK1)) )
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f454,f159])).

fof(f454,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK2,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) )
    | ~ spl9_26 ),
    inference(superposition,[],[f82,f159])).

fof(f451,plain,
    ( spl9_112
    | spl9_116
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f447,f154,f449,f439])).

fof(f447,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) )
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f433,f155])).

fof(f433,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))) )
    | ~ spl9_24 ),
    inference(superposition,[],[f86,f155])).

fof(f444,plain,
    ( spl9_112
    | spl9_114
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f437,f154,f442,f439])).

fof(f437,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK1,sK1))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK1)) )
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f429,f155])).

fof(f429,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK1,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) )
    | ~ spl9_24 ),
    inference(superposition,[],[f82,f155])).

fof(f426,plain,
    ( spl9_106
    | spl9_110
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f422,f150,f424,f414])).

fof(f422,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) )
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f408,f151])).

fof(f408,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))) )
    | ~ spl9_22 ),
    inference(superposition,[],[f86,f151])).

fof(f419,plain,
    ( spl9_106
    | spl9_108
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f412,f150,f417,f414])).

fof(f412,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK1,sK1,sK1))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK1)) )
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f404,f151])).

fof(f404,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK1,sK1,sK1))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))))) = k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) )
    | ~ spl9_22 ),
    inference(superposition,[],[f82,f151])).

fof(f401,plain,
    ( ~ spl9_105
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f395,f129,f398])).

fof(f398,plain,
    ( spl9_105
  <=> ~ r2_hidden(sK2,sK8(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f129,plain,
    ( spl9_18
  <=> r2_hidden(sK8(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f395,plain,
    ( ~ r2_hidden(sK2,sK8(sK2))
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f130,f68])).

fof(f130,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f400,plain,
    ( ~ spl9_105
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f396,f129,f398])).

fof(f396,plain,
    ( ~ r2_hidden(sK2,sK8(sK2))
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f130,f68])).

fof(f392,plain,
    ( spl9_98
    | spl9_102
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f388,f122,f390,f380])).

fof(f388,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))
        | k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) )
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f374,f123])).

fof(f374,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))) )
    | ~ spl9_16 ),
    inference(superposition,[],[f86,f123])).

fof(f385,plain,
    ( spl9_98
    | spl9_100
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f378,f122,f383,f380])).

fof(f378,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK8(k3_zfmisc_1(sK2,sK2,sK2))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))
        | k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK2)) )
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f370,f123])).

fof(f370,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK8(k3_zfmisc_1(sK2,sK2,sK2))
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))))) = k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) )
    | ~ spl9_16 ),
    inference(superposition,[],[f82,f123])).

fof(f367,plain,
    ( spl9_94
    | spl9_4
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f363,f303,f365,f355])).

fof(f363,plain,
    ( ! [X8,X9] :
        ( k2_mcart_1(sK3) = k7_mcart_1(sK0,sK1,sK2,sK3)
        | k4_tarski(X8,X9) != sK3 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f349,f304])).

fof(f349,plain,
    ( ! [X8,X9] :
        ( k4_tarski(X8,X9) != sK3
        | k2_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = k7_mcart_1(sK0,sK1,sK2,sK3) )
    | ~ spl9_76 ),
    inference(superposition,[],[f86,f304])).

fof(f360,plain,
    ( spl9_94
    | spl9_96
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f353,f303,f358,f355])).

fof(f353,plain,
    ( ! [X2,X3] :
        ( k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))
        | k4_tarski(X2,X3) != sK3 )
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f345,f304])).

fof(f345,plain,
    ( ! [X2,X3] :
        ( k4_tarski(X2,X3) != sK3
        | k1_mcart_1(k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) )
    | ~ spl9_76 ),
    inference(superposition,[],[f82,f304])).

fof(f342,plain,
    ( spl9_92
    | spl9_15
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f338,f315,f118,f340])).

fof(f338,plain,
    ( r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK3),sK2)
    | ~ spl9_15
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f119,f316,f70])).

fof(f337,plain,
    ( spl9_90
    | spl9_21
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f333,f311,f146,f335])).

fof(f146,plain,
    ( spl9_21
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f311,plain,
    ( spl9_80
  <=> m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f333,plain,
    ( r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK3),sK1)
    | ~ spl9_21
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f147,f312,f70])).

fof(f312,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK3),sK1)
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f311])).

fof(f147,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f146])).

fof(f332,plain,
    ( spl9_88
    | spl9_37
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f328,f307,f211,f330])).

fof(f211,plain,
    ( spl9_37
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f307,plain,
    ( spl9_78
  <=> m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f328,plain,
    ( r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK3),sK0)
    | ~ spl9_37
    | ~ spl9_78 ),
    inference(unit_resulting_resolution,[],[f212,f308,f70])).

fof(f308,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK0)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f307])).

fof(f212,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f211])).

fof(f327,plain,
    ( spl9_86
    | spl9_37 ),
    inference(avatar_split_clause,[],[f323,f211,f325])).

fof(f323,plain,
    ( r2_hidden(sK8(sK0),sK0)
    | ~ spl9_37 ),
    inference(unit_resulting_resolution,[],[f67,f212,f70])).

fof(f322,plain,
    ( spl9_84
    | spl9_21 ),
    inference(avatar_split_clause,[],[f318,f146,f320])).

fof(f318,plain,
    ( r2_hidden(sK8(sK1),sK1)
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f67,f147,f70])).

fof(f317,plain,
    ( spl9_82
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f298,f98,f315])).

fof(f298,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK3),sK2)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f99,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',dt_k7_mcart_1)).

fof(f313,plain,
    ( spl9_80
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f299,f98,f311])).

fof(f299,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK3),sK1)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f99,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',dt_k6_mcart_1)).

fof(f309,plain,
    ( spl9_78
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f300,f98,f307])).

fof(f300,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK3),sK0)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f99,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',dt_k5_mcart_1)).

fof(f305,plain,
    ( spl9_76
    | ~ spl9_6
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f301,f110,f106,f102,f98,f303])).

fof(f301,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) = sK3
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f107,f103,f99,f78])).

fof(f297,plain,
    ( spl9_74
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f182,f110,f102,f295])).

fof(f182,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2))),k6_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))),k7_mcart_1(sK0,sK2,sK2,sK8(k3_zfmisc_1(sK0,sK2,sK2)))) = sK8(k3_zfmisc_1(sK0,sK2,sK2))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f111,f78])).

fof(f293,plain,
    ( spl9_72
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f183,f110,f106,f102,f291])).

fof(f183,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1))),k6_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))),k7_mcart_1(sK0,sK2,sK1,sK8(k3_zfmisc_1(sK0,sK2,sK1)))) = sK8(k3_zfmisc_1(sK0,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f111,f78])).

fof(f289,plain,
    ( spl9_50
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f184,f110,f102,f239])).

fof(f184,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) = sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f111,f78])).

fof(f288,plain,
    ( spl9_70
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f185,f110,f106,f102,f286])).

fof(f185,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2))),k6_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))),k7_mcart_1(sK0,sK1,sK2,sK8(k3_zfmisc_1(sK0,sK1,sK2)))) = sK8(k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f111,f78])).

fof(f284,plain,
    ( spl9_68
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f186,f110,f106,f282])).

fof(f186,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1))),k6_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))),k7_mcart_1(sK0,sK1,sK1,sK8(k3_zfmisc_1(sK0,sK1,sK1)))) = sK8(k3_zfmisc_1(sK0,sK1,sK1))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f111,f78])).

fof(f280,plain,
    ( spl9_44
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f187,f110,f106,f227])).

fof(f187,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) = sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f111,f78])).

fof(f279,plain,
    ( spl9_62
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f188,f110,f102,f266])).

fof(f188,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) = sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f111,f78])).

fof(f278,plain,
    ( spl9_56
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f189,f110,f106,f254])).

fof(f189,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) = sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f111,f78])).

fof(f277,plain,
    ( spl9_38
    | spl9_13 ),
    inference(avatar_split_clause,[],[f190,f110,f215])).

fof(f190,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) = sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f111,f78])).

fof(f276,plain,
    ( spl9_66
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f191,f110,f102,f274])).

fof(f191,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2))),k6_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))),k7_mcart_1(sK2,sK0,sK2,sK8(k3_zfmisc_1(sK2,sK0,sK2)))) = sK8(k3_zfmisc_1(sK2,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f111,f78])).

fof(f272,plain,
    ( spl9_64
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f192,f110,f106,f102,f270])).

fof(f192,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2))),k6_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))),k7_mcart_1(sK1,sK0,sK2,sK8(k3_zfmisc_1(sK1,sK0,sK2)))) = sK8(k3_zfmisc_1(sK1,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f111,f78])).

fof(f268,plain,
    ( spl9_62
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f193,f110,f102,f266])).

fof(f193,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2))),k6_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))),k7_mcart_1(sK0,sK0,sK2,sK8(k3_zfmisc_1(sK0,sK0,sK2)))) = sK8(k3_zfmisc_1(sK0,sK0,sK2))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f111,f78])).

fof(f264,plain,
    ( spl9_60
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f194,f110,f106,f102,f262])).

fof(f194,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1))),k6_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))),k7_mcart_1(sK2,sK0,sK1,sK8(k3_zfmisc_1(sK2,sK0,sK1)))) = sK8(k3_zfmisc_1(sK2,sK0,sK1))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f111,f78])).

fof(f260,plain,
    ( spl9_58
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f195,f110,f106,f258])).

fof(f195,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1))),k6_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))),k7_mcart_1(sK1,sK0,sK1,sK8(k3_zfmisc_1(sK1,sK0,sK1)))) = sK8(k3_zfmisc_1(sK1,sK0,sK1))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f111,f78])).

fof(f256,plain,
    ( spl9_56
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f196,f110,f106,f254])).

fof(f196,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1))),k6_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))),k7_mcart_1(sK0,sK0,sK1,sK8(k3_zfmisc_1(sK0,sK0,sK1)))) = sK8(k3_zfmisc_1(sK0,sK0,sK1))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f111,f78])).

fof(f252,plain,
    ( spl9_42
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f197,f110,f102,f223])).

fof(f197,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) = sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f111,f78])).

fof(f251,plain,
    ( spl9_40
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f198,f110,f106,f219])).

fof(f198,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) = sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f111,f78])).

fof(f250,plain,
    ( spl9_38
    | spl9_13 ),
    inference(avatar_split_clause,[],[f199,f110,f215])).

fof(f199,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) = sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f111,f78])).

fof(f249,plain,
    ( spl9_54
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f200,f110,f102,f247])).

fof(f200,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0))),k6_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))),k7_mcart_1(sK2,sK2,sK0,sK8(k3_zfmisc_1(sK2,sK2,sK0)))) = sK8(k3_zfmisc_1(sK2,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f111,f78])).

fof(f245,plain,
    ( spl9_52
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f201,f110,f106,f102,f243])).

fof(f201,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0))),k6_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))),k7_mcart_1(sK1,sK2,sK0,sK8(k3_zfmisc_1(sK1,sK2,sK0)))) = sK8(k3_zfmisc_1(sK1,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f111,f78])).

fof(f241,plain,
    ( spl9_50
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f202,f110,f102,f239])).

fof(f202,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0))),k6_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))),k7_mcart_1(sK0,sK2,sK0,sK8(k3_zfmisc_1(sK0,sK2,sK0)))) = sK8(k3_zfmisc_1(sK0,sK2,sK0))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f103,f67,f111,f78])).

fof(f237,plain,
    ( spl9_48
    | spl9_9
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f203,f110,f106,f102,f235])).

fof(f203,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0))),k6_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))),k7_mcart_1(sK2,sK1,sK0,sK8(k3_zfmisc_1(sK2,sK1,sK0)))) = sK8(k3_zfmisc_1(sK2,sK1,sK0))
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f111,f78])).

fof(f233,plain,
    ( spl9_46
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f204,f110,f106,f231])).

fof(f204,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0))),k6_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))),k7_mcart_1(sK1,sK1,sK0,sK8(k3_zfmisc_1(sK1,sK1,sK0)))) = sK8(k3_zfmisc_1(sK1,sK1,sK0))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f111,f78])).

fof(f229,plain,
    ( spl9_44
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f205,f110,f106,f227])).

fof(f205,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0))),k6_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))),k7_mcart_1(sK0,sK1,sK0,sK8(k3_zfmisc_1(sK0,sK1,sK0)))) = sK8(k3_zfmisc_1(sK0,sK1,sK0))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f107,f67,f111,f78])).

fof(f225,plain,
    ( spl9_42
    | spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f206,f110,f102,f223])).

fof(f206,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0))),k6_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))),k7_mcart_1(sK2,sK0,sK0,sK8(k3_zfmisc_1(sK2,sK0,sK0)))) = sK8(k3_zfmisc_1(sK2,sK0,sK0))
    | ~ spl9_9
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f103,f111,f67,f111,f78])).

fof(f221,plain,
    ( spl9_40
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f207,f110,f106,f219])).

fof(f207,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0))),k6_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))),k7_mcart_1(sK1,sK0,sK0,sK8(k3_zfmisc_1(sK1,sK0,sK0)))) = sK8(k3_zfmisc_1(sK1,sK0,sK0))
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f107,f111,f67,f111,f78])).

fof(f217,plain,
    ( spl9_38
    | spl9_13 ),
    inference(avatar_split_clause,[],[f208,f110,f215])).

fof(f208,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0))),k6_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))),k7_mcart_1(sK0,sK0,sK0,sK8(k3_zfmisc_1(sK0,sK0,sK0)))) = sK8(k3_zfmisc_1(sK0,sK0,sK0))
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f111,f67,f111,f78])).

fof(f213,plain,
    ( ~ spl9_37
    | spl9_13 ),
    inference(avatar_split_clause,[],[f209,f110,f211])).

fof(f209,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_13 ),
    inference(unit_resulting_resolution,[],[f111,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',t6_boole)).

fof(f181,plain,
    ( spl9_34
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f132,f106,f102,f179])).

fof(f132,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2))),k6_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))),k7_mcart_1(sK1,sK2,sK2,sK8(k3_zfmisc_1(sK1,sK2,sK2)))) = sK8(k3_zfmisc_1(sK1,sK2,sK2))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f107,f78])).

fof(f177,plain,
    ( spl9_26
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f133,f106,f102,f158])).

fof(f133,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) = sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f107,f78])).

fof(f176,plain,
    ( spl9_30
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f134,f106,f102,f168])).

fof(f134,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) = sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f107,f78])).

fof(f175,plain,
    ( spl9_22
    | spl9_11 ),
    inference(avatar_split_clause,[],[f135,f106,f150])).

fof(f135,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) = sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f107,f78])).

fof(f174,plain,
    ( spl9_32
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f136,f106,f102,f172])).

fof(f136,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2))),k6_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))),k7_mcart_1(sK2,sK1,sK2,sK8(k3_zfmisc_1(sK2,sK1,sK2)))) = sK8(k3_zfmisc_1(sK2,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f107,f78])).

fof(f170,plain,
    ( spl9_30
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f137,f106,f102,f168])).

fof(f137,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2))),k6_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))),k7_mcart_1(sK1,sK1,sK2,sK8(k3_zfmisc_1(sK1,sK1,sK2)))) = sK8(k3_zfmisc_1(sK1,sK1,sK2))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f107,f78])).

fof(f166,plain,
    ( spl9_24
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f138,f106,f102,f154])).

fof(f138,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) = sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f107,f78])).

fof(f165,plain,
    ( spl9_22
    | spl9_11 ),
    inference(avatar_split_clause,[],[f139,f106,f150])).

fof(f139,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) = sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f107,f78])).

fof(f164,plain,
    ( spl9_28
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f140,f106,f102,f162])).

fof(f140,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1))),k6_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))),k7_mcart_1(sK2,sK2,sK1,sK8(k3_zfmisc_1(sK2,sK2,sK1)))) = sK8(k3_zfmisc_1(sK2,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f107,f78])).

fof(f160,plain,
    ( spl9_26
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f141,f106,f102,f158])).

fof(f141,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1))),k6_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))),k7_mcart_1(sK1,sK2,sK1,sK8(k3_zfmisc_1(sK1,sK2,sK1)))) = sK8(k3_zfmisc_1(sK1,sK2,sK1))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f103,f67,f107,f78])).

fof(f156,plain,
    ( spl9_24
    | spl9_9
    | spl9_11 ),
    inference(avatar_split_clause,[],[f142,f106,f102,f154])).

fof(f142,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1))),k6_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))),k7_mcart_1(sK2,sK1,sK1,sK8(k3_zfmisc_1(sK2,sK1,sK1)))) = sK8(k3_zfmisc_1(sK2,sK1,sK1))
    | ~ spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f103,f107,f67,f107,f78])).

fof(f152,plain,
    ( spl9_22
    | spl9_11 ),
    inference(avatar_split_clause,[],[f143,f106,f150])).

fof(f143,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1))),k6_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))),k7_mcart_1(sK1,sK1,sK1,sK8(k3_zfmisc_1(sK1,sK1,sK1)))) = sK8(k3_zfmisc_1(sK1,sK1,sK1))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f107,f67,f107,f78])).

fof(f148,plain,
    ( ~ spl9_21
    | spl9_11 ),
    inference(avatar_split_clause,[],[f144,f106,f146])).

fof(f144,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f107,f60])).

fof(f131,plain,
    ( spl9_18
    | spl9_15 ),
    inference(avatar_split_clause,[],[f127,f118,f129])).

fof(f127,plain,
    ( r2_hidden(sK8(sK2),sK2)
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f67,f119,f70])).

fof(f126,plain,
    ( spl9_16
    | spl9_9 ),
    inference(avatar_split_clause,[],[f113,f102,f122])).

fof(f113,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) = sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f103,f78])).

fof(f125,plain,
    ( spl9_16
    | spl9_9 ),
    inference(avatar_split_clause,[],[f114,f102,f122])).

fof(f114,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) = sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f103,f78])).

fof(f124,plain,
    ( spl9_16
    | spl9_9 ),
    inference(avatar_split_clause,[],[f115,f102,f122])).

fof(f115,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2))),k6_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))),k7_mcart_1(sK2,sK2,sK2,sK8(k3_zfmisc_1(sK2,sK2,sK2)))) = sK8(k3_zfmisc_1(sK2,sK2,sK2))
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f103,f103,f67,f103,f78])).

fof(f120,plain,
    ( ~ spl9_15
    | spl9_9 ),
    inference(avatar_split_clause,[],[f116,f102,f118])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f103,f60])).

fof(f112,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k2_mcart_1(sK3) != k7_mcart_1(sK0,sK1,sK2,sK3)
      | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
      | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) )
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
              | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
              | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(sK0,sK1,sK2,X3)
            | k6_mcart_1(sK0,sK1,sK2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(sK0,sK1,sK2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(sK0,sK1,sK2)) )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
            | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( k2_mcart_1(sK3) != k7_mcart_1(X0,X1,X2,sK3)
          | k6_mcart_1(X0,X1,X2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
          | k5_mcart_1(X0,X1,X2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) )
        & m1_subset_1(sK3,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k2_mcart_1(X3) != k7_mcart_1(X0,X1,X2,X3)
            | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                  & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                  & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t50_mcart_1.p',t50_mcart_1)).

fof(f108,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f55,f106])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f56,f102])).

fof(f56,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f57,f98])).

fof(f57,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f58,f94,f91,f88])).

fof(f91,plain,
    ( spl9_3
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f94,plain,
    ( spl9_5
  <=> k2_mcart_1(sK3) != k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f58,plain,
    ( k2_mcart_1(sK3) != k7_mcart_1(sK0,sK1,sK2,sK3)
    | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------

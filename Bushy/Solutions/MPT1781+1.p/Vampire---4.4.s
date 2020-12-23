%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t96_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:24 EDT 2019

% Result     : Theorem 0.93s
% Output     : Refutation 0.93s
% Verified   : 
% Statistics : Number of formulae       : 2388 (17457 expanded)
%              Number of leaves         :  578 (6142 expanded)
%              Depth                    :   34
%              Number of atoms          : 9073 (47032 expanded)
%              Number of equality atoms :  865 (3311 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :   19 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7087,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f150,f157,f164,f171,f178,f185,f192,f199,f206,f213,f222,f229,f240,f248,f264,f290,f303,f312,f326,f335,f347,f354,f361,f368,f376,f384,f392,f400,f415,f426,f433,f444,f454,f460,f474,f484,f491,f502,f508,f527,f534,f541,f558,f565,f572,f580,f588,f600,f608,f635,f648,f661,f668,f687,f694,f701,f708,f715,f722,f729,f731,f732,f751,f754,f765,f772,f773,f775,f777,f789,f795,f816,f823,f838,f845,f852,f860,f873,f877,f887,f900,f907,f909,f927,f940,f947,f954,f967,f981,f982,f989,f1030,f1043,f1056,f1069,f1082,f1095,f1102,f1142,f1149,f1156,f1163,f1170,f1172,f1185,f1197,f1219,f1226,f1233,f1240,f1247,f1254,f1262,f1270,f1283,f1290,f1297,f1300,f1308,f1320,f1349,f1380,f1382,f1397,f1404,f1433,f1440,f1447,f1454,f1461,f1468,f1475,f1482,f1489,f1496,f1503,f1510,f1518,f1526,f1534,f1542,f1549,f1554,f1558,f1566,f1615,f1622,f1629,f1636,f1643,f1650,f1657,f1664,f1671,f1678,f1685,f1692,f1699,f1707,f1715,f1723,f1731,f1738,f1743,f1747,f1755,f1790,f1797,f1804,f1811,f1818,f1825,f1832,f1839,f1846,f1853,f1860,f1867,f1874,f1881,f1889,f1897,f1905,f1913,f1920,f1925,f1938,f1952,f1971,f1975,f1983,f2014,f2015,f2028,f2057,f2060,f2063,f2069,f2072,f2097,f2106,f2119,f2132,f2171,f2179,f2187,f2196,f2208,f2215,f2222,f2234,f2240,f2247,f2255,f2256,f2302,f2310,f2322,f2329,f2335,f2398,f2405,f2412,f2434,f2436,f2459,f2467,f2475,f2489,f2497,f2504,f2512,f2541,f2543,f2558,f2564,f2565,f2588,f2598,f2607,f2629,f2651,f2661,f2672,f2683,f2686,f2690,f2728,f2737,f2750,f2763,f2771,f2779,f2798,f2805,f2812,f2824,f2831,f2838,f2840,f2846,f2847,f2858,f2882,f2889,f2896,f2905,f2911,f2912,f2919,f2933,f2935,f2937,f2939,f2946,f2980,f2987,f3011,f3038,f3051,f3055,f3059,f3060,f3068,f3080,f3087,f3094,f3096,f3103,f3104,f3105,f3112,f3114,f3127,f3128,f3129,f3130,f3140,f3144,f3177,f3190,f3197,f3210,f3223,f3253,f3255,f3268,f3304,f3317,f3340,f3347,f3354,f3361,f3369,f3382,f3383,f3384,f3385,f3395,f3402,f3443,f3451,f3464,f3473,f3486,f3493,f3500,f3501,f3505,f3509,f3513,f3523,f3525,f3545,f3546,f3569,f3577,f3582,f3588,f3593,f3613,f3677,f3685,f3698,f3712,f3719,f3726,f3733,f3740,f3788,f3814,f3827,f3831,f3848,f3861,f3868,f3875,f3882,f3884,f3898,f3899,f3900,f3901,f3902,f3904,f3936,f3938,f4050,f4054,f4056,f4210,f4218,f4236,f4246,f4250,f4258,f4272,f4279,f4300,f4308,f4321,f4328,f4349,f4358,f4366,f4379,f4386,f4578,f4581,f4591,f4632,f4639,f4648,f4656,f4669,f4676,f4687,f4865,f4875,f4884,f4896,f4908,f4920,f4957,f4961,f4965,f5010,f5011,f5012,f5058,f5071,f5075,f5088,f5089,f5096,f5103,f5110,f5117,f5124,f5131,f5138,f5155,f5162,f5169,f5176,f5183,f5190,f5197,f5204,f5229,f5253,f5268,f5269,f5270,f5271,f5272,f5273,f5274,f5281,f5291,f5297,f5298,f5310,f5317,f5324,f5327,f5334,f5338,f5339,f5352,f5359,f5366,f5367,f5397,f5422,f5431,f5444,f5451,f5458,f5476,f5484,f5491,f5498,f5511,f5519,f5529,f5536,f5549,f5556,f5641,f5651,f5661,f5675,f5684,f5685,f5686,f5706,f5713,f5720,f5727,f5734,f5741,f5748,f5755,f5800,f5807,f5814,f5821,f5828,f5835,f5842,f5849,f5861,f5862,f5869,f5888,f5929,f5936,f5943,f5950,f5957,f5974,f5975,f5976,f6021,f6029,f6083,f6159,f6178,f6217,f6249,f6257,f6293,f6322,f6343,f6436,f6481,f6498,f6500,f6535,f6704,f6711,f6718,f6890,f6927,f6939,f6952,f6959,f6960,f6971,f6975,f7052,f7086])).

fof(f7086,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | spl10_11
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(avatar_contradiction_clause,[],[f7085])).

fof(f7085,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7084,f177])).

fof(f177,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl10_11
  <=> ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f7084,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(forward_demodulation,[],[f7083,f872])).

fof(f872,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl10_156 ),
    inference(avatar_component_clause,[],[f871])).

fof(f871,plain,
    ( spl10_156
  <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_156])])).

fof(f7083,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7082,f184])).

fof(f184,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f7082,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7081,f191])).

fof(f191,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl10_14
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f7081,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7080,f198])).

fof(f198,plain,
    ( v1_funct_1(sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl10_16
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f7080,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7079,f2035])).

fof(f2035,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_394 ),
    inference(avatar_component_clause,[],[f2034])).

fof(f2034,plain,
    ( spl10_394
  <=> m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_394])])).

fof(f7079,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7078,f2041])).

fof(f2041,plain,
    ( v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_396 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f2040,plain,
    ( spl10_396
  <=> v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_396])])).

fof(f7078,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_398
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7077,f2047])).

fof(f2047,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl10_398 ),
    inference(avatar_component_clause,[],[f2046])).

fof(f2046,plain,
    ( spl10_398
  <=> v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_398])])).

fof(f7077,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7076,f163])).

fof(f163,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f7076,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7075,f170])).

fof(f170,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl10_9
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f7075,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7074,f156])).

fof(f156,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl10_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f7074,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7073,f142])).

fof(f142,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f7073,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_2
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7072,f149])).

fof(f149,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f7072,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_800
    | ~ spl10_938 ),
    inference(subsumption_resolution,[],[f7071,f5228])).

fof(f5228,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_800 ),
    inference(avatar_component_clause,[],[f5227])).

fof(f5227,plain,
    ( spl10_800
  <=> k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_800])])).

fof(f7071,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_938 ),
    inference(duplicate_literal_removal,[],[f7067])).

fof(f7067,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) != sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1),sK2)
    | ~ spl10_938 ),
    inference(superposition,[],[f117,f7051])).

fof(f7051,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_938 ),
    inference(avatar_component_clause,[],[f7050])).

fof(f7050,plain,
    ( spl10_938
  <=> k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_938])])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,sK6(X0,X1,X2,X3,X4)) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK6(X0,X1,X2,X3,X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k1_funct_1(X4,X5) != k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t59_tmap_1)).

fof(f7052,plain,
    ( spl10_938
    | ~ spl10_838
    | ~ spl10_846 ),
    inference(avatar_split_clause,[],[f7045,f5547,f5509,f7050])).

fof(f5509,plain,
    ( spl10_838
  <=> k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_838])])).

fof(f5547,plain,
    ( spl10_846
  <=> k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_846])])).

fof(f7045,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_838
    | ~ spl10_846 ),
    inference(forward_demodulation,[],[f5510,f5548])).

fof(f5548,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_846 ),
    inference(avatar_component_clause,[],[f5547])).

fof(f5510,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_838 ),
    inference(avatar_component_clause,[],[f5509])).

fof(f6975,plain,
    ( spl10_936
    | ~ spl10_22
    | spl10_209
    | ~ spl10_930 ),
    inference(avatar_split_clause,[],[f6974,f6937,f1151,f220,f6969])).

fof(f6969,plain,
    ( spl10_936
  <=> k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_936])])).

fof(f220,plain,
    ( spl10_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f1151,plain,
    ( spl10_209
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_209])])).

fof(f6937,plain,
    ( spl10_930
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_930])])).

fof(f6974,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_930 ),
    inference(subsumption_resolution,[],[f6973,f221])).

fof(f221,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f6973,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_209
    | ~ spl10_930 ),
    inference(subsumption_resolution,[],[f6963,f1152])).

fof(f1152,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_209 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f6963,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_930 ),
    inference(resolution,[],[f6938,f3424])).

fof(f3424,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X8,u1_struct_0(X7))
      | v1_xboole_0(u1_struct_0(X7))
      | k1_funct_1(k3_struct_0(X7),X8) = k3_funct_2(u1_struct_0(X7),u1_struct_0(X7),k3_struct_0(X7),X8)
      | ~ l1_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f3423,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_k3_struct_0)).

fof(f3423,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_2(k3_struct_0(X7),u1_struct_0(X7),u1_struct_0(X7))
      | v1_xboole_0(u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | k1_funct_1(k3_struct_0(X7),X8) = k3_funct_2(u1_struct_0(X7),u1_struct_0(X7),k3_struct_0(X7),X8)
      | ~ l1_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f3407,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f3407,plain,(
    ! [X8,X7] :
      ( ~ v1_funct_1(k3_struct_0(X7))
      | ~ v1_funct_2(k3_struct_0(X7),u1_struct_0(X7),u1_struct_0(X7))
      | v1_xboole_0(u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | k1_funct_1(k3_struct_0(X7),X8) = k3_funct_2(u1_struct_0(X7),u1_struct_0(X7),k3_struct_0(X7),X8)
      | ~ l1_struct_0(X7) ) ),
    inference(resolution,[],[f125,f120])).

fof(f120,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',redefinition_k3_funct_2)).

fof(f6938,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ spl10_930 ),
    inference(avatar_component_clause,[],[f6937])).

fof(f6971,plain,
    ( spl10_936
    | ~ spl10_632
    | ~ spl10_930 ),
    inference(avatar_split_clause,[],[f6961,f6937,f3503,f6969])).

fof(f3503,plain,
    ( spl10_632
  <=> ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_funct_1(k3_struct_0(sK0),X9) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_632])])).

fof(f6961,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ spl10_632
    | ~ spl10_930 ),
    inference(resolution,[],[f6938,f3504])).

fof(f3504,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_funct_1(k3_struct_0(sK0),X9) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X9) )
    | ~ spl10_632 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f6960,plain,
    ( spl10_930
    | ~ spl10_928 ),
    inference(avatar_split_clause,[],[f6942,f6925,f6937])).

fof(f6925,plain,
    ( spl10_928
  <=> r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_928])])).

fof(f6942,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ spl10_928 ),
    inference(resolution,[],[f6926,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t1_subset)).

fof(f6926,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ spl10_928 ),
    inference(avatar_component_clause,[],[f6925])).

fof(f6959,plain,
    ( ~ spl10_935
    | ~ spl10_928 ),
    inference(avatar_split_clause,[],[f6941,f6925,f6957])).

fof(f6957,plain,
    ( spl10_935
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_935])])).

fof(f6941,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ spl10_928 ),
    inference(resolution,[],[f6926,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',antisymmetry_r2_hidden)).

fof(f6952,plain,
    ( spl10_932
    | ~ spl10_52
    | ~ spl10_928 ),
    inference(avatar_split_clause,[],[f6945,f6925,f345,f6950])).

fof(f6950,plain,
    ( spl10_932
  <=> k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_932])])).

fof(f345,plain,
    ( spl10_52
  <=> k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f6945,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ spl10_52
    | ~ spl10_928 ),
    inference(forward_demodulation,[],[f6940,f346])).

fof(f346,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f345])).

fof(f6940,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))))
    | ~ spl10_928 ),
    inference(resolution,[],[f6926,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t35_funct_1)).

fof(f6939,plain,
    ( spl10_930
    | spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(avatar_split_clause,[],[f6932,f5056,f2681,f2670,f2627,f1428,f6937])).

fof(f1428,plain,
    ( spl10_267
  <=> ~ v1_xboole_0(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_267])])).

fof(f2627,plain,
    ( spl10_482
  <=> v1_funct_1(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_482])])).

fof(f2670,plain,
    ( spl10_492
  <=> m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_492])])).

fof(f2681,plain,
    ( spl10_494
  <=> v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_494])])).

fof(f5056,plain,
    ( spl10_762
  <=> k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_762])])).

fof(f6932,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6931,f1429])).

fof(f1429,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_267 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f6931,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6930,f107])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',existence_m1_subset_1)).

fof(f6930,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6929,f2671])).

fof(f2671,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_492 ),
    inference(avatar_component_clause,[],[f2670])).

fof(f6929,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6928,f2682])).

fof(f2682,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl10_494 ),
    inference(avatar_component_clause,[],[f2681])).

fof(f6928,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6914,f2628])).

fof(f2628,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_482 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f6914,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_762 ),
    inference(superposition,[],[f126,f5057])).

fof(f5057,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))
    | ~ spl10_762 ),
    inference(avatar_component_clause,[],[f5056])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_k3_funct_2)).

fof(f6927,plain,
    ( spl10_928
    | spl10_209
    | spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(avatar_split_clause,[],[f6920,f5056,f2681,f2670,f2627,f1428,f1151,f6925])).

fof(f6920,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6919,f2628])).

fof(f6919,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_209
    | ~ spl10_267
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6918,f1152])).

fof(f6918,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_267
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6917,f1429])).

fof(f6917,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6916,f107])).

fof(f6916,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6915,f2671])).

fof(f6915,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_494
    | ~ spl10_762 ),
    inference(subsumption_resolution,[],[f6913,f2682])).

fof(f6913,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_762 ),
    inference(superposition,[],[f3318,f5057])).

fof(f3318,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X1,X2,X0,X3),X2)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f126,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t2_subset)).

fof(f6890,plain,
    ( spl10_926
    | ~ spl10_118
    | ~ spl10_162
    | spl10_803 ),
    inference(avatar_split_clause,[],[f6889,f5276,f905,f646,f6716])).

fof(f6716,plain,
    ( spl10_926
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_926])])).

fof(f646,plain,
    ( spl10_118
  <=> v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f905,plain,
    ( spl10_162
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f5276,plain,
    ( spl10_803
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_803])])).

fof(f6889,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))
    | ~ spl10_118
    | ~ spl10_162
    | ~ spl10_803 ),
    inference(subsumption_resolution,[],[f6866,f906])).

fof(f906,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_162 ),
    inference(avatar_component_clause,[],[f905])).

fof(f6866,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))
    | ~ spl10_118
    | ~ spl10_803 ),
    inference(superposition,[],[f5277,f4144])).

fof(f4144,plain,
    ( ! [X0] :
        ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0))))))))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(resolution,[],[f3631,f445])).

fof(f445,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) ) ),
    inference(resolution,[],[f128,f251])).

fof(f251,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f104,f107])).

fof(f3631,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f2990,f404])).

fof(f404,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f403,f270])).

fof(f270,plain,(
    ! [X2] :
      ( ~ sP9(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f251,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f101,f134_D])).

fof(f134,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f134_D])).

fof(f134_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t5_subset)).

fof(f403,plain,(
    ! [X0] :
      ( sP9(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f134,f107])).

fof(f2990,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f1001,f403])).

fof(f1001,plain,
    ( ! [X1] :
        ( ~ sP9(X1)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f888,f612])).

fof(f612,plain,(
    ! [X3] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X3)))
      | ~ sP9(X3) ) ),
    inference(resolution,[],[f547,f135])).

fof(f547,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(subsumption_resolution,[],[f543,f404])).

fof(f543,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | r2_hidden(sK3(sK3(k1_zfmisc_1(X0))),X0) ) ),
    inference(resolution,[],[f401,f104])).

fof(f401,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK3(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK3(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f292,f251])).

fof(f292,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK3(k1_zfmisc_1(X2)))
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f102,f107])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t4_subset)).

fof(f888,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f779,f403])).

fof(f779,plain,
    ( ! [X1] :
        ( ~ sP9(X1)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(X1)) )
    | ~ spl10_118 ),
    inference(resolution,[],[f756,f612])).

fof(f756,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK3(k1_zfmisc_1(sK2)) = X1 )
    | ~ spl10_118 ),
    inference(resolution,[],[f647,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t8_boole)).

fof(f647,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_118 ),
    inference(avatar_component_clause,[],[f646])).

fof(f5277,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))))))
    | ~ spl10_803 ),
    inference(avatar_component_clause,[],[f5276])).

fof(f6718,plain,
    ( spl10_926
    | ~ spl10_118
    | spl10_771 ),
    inference(avatar_split_clause,[],[f6649,f5091,f646,f6716])).

fof(f5091,plain,
    ( spl10_771
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_771])])).

fof(f6649,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))
    | ~ spl10_118
    | ~ spl10_771 ),
    inference(trivial_inequality_removal,[],[f6609])).

fof(f6609,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))
    | ~ spl10_118
    | ~ spl10_771 ),
    inference(superposition,[],[f5092,f4144])).

fof(f5092,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))))
    | ~ spl10_771 ),
    inference(avatar_component_clause,[],[f5091])).

fof(f6711,plain,
    ( spl10_924
    | ~ spl10_118
    | spl10_873 ),
    inference(avatar_split_clause,[],[f6650,f5750,f646,f6709])).

fof(f6709,plain,
    ( spl10_924
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_924])])).

fof(f5750,plain,
    ( spl10_873
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_873])])).

fof(f6650,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))
    | ~ spl10_118
    | ~ spl10_873 ),
    inference(trivial_inequality_removal,[],[f6608])).

fof(f6608,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))
    | ~ spl10_118
    | ~ spl10_873 ),
    inference(superposition,[],[f5751,f4144])).

fof(f5751,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))))
    | ~ spl10_873 ),
    inference(avatar_component_clause,[],[f5750])).

fof(f6704,plain,
    ( spl10_922
    | ~ spl10_118
    | spl10_799 ),
    inference(avatar_split_clause,[],[f6651,f5199,f646,f6702])).

fof(f6702,plain,
    ( spl10_922
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_922])])).

fof(f5199,plain,
    ( spl10_799
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_799])])).

fof(f6651,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))
    | ~ spl10_118
    | ~ spl10_799 ),
    inference(trivial_inequality_removal,[],[f6607])).

fof(f6607,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))
    | ~ spl10_118
    | ~ spl10_799 ),
    inference(superposition,[],[f5200,f4144])).

fof(f5200,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))))))))
    | ~ spl10_799 ),
    inference(avatar_component_clause,[],[f5199])).

fof(f6535,plain,
    ( spl10_920
    | ~ spl10_800
    | ~ spl10_844 ),
    inference(avatar_split_clause,[],[f6528,f5534,f5227,f6533])).

fof(f6533,plain,
    ( spl10_920
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_920])])).

fof(f5534,plain,
    ( spl10_844
  <=> k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_844])])).

fof(f6528,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_800
    | ~ spl10_844 ),
    inference(forward_demodulation,[],[f5535,f5228])).

fof(f5535,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_844 ),
    inference(avatar_component_clause,[],[f5534])).

fof(f6500,plain,
    ( spl10_766
    | spl10_765
    | ~ spl10_768 ),
    inference(avatar_split_clause,[],[f6499,f5073,f5060,f5069])).

fof(f5069,plain,
    ( spl10_766
  <=> k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_766])])).

fof(f5060,plain,
    ( spl10_765
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_765])])).

fof(f5073,plain,
    ( spl10_768
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_768])])).

fof(f6499,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | ~ spl10_765
    | ~ spl10_768 ),
    inference(subsumption_resolution,[],[f6492,f5061])).

fof(f5061,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_765 ),
    inference(avatar_component_clause,[],[f5060])).

fof(f6492,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_768 ),
    inference(resolution,[],[f5074,f401])).

fof(f5074,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) )
    | ~ spl10_768 ),
    inference(avatar_component_clause,[],[f5073])).

fof(f6498,plain,
    ( spl10_762
    | ~ spl10_768 ),
    inference(avatar_split_clause,[],[f6491,f5073,f5056])).

fof(f6491,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))
    | ~ spl10_768 ),
    inference(resolution,[],[f5074,f107])).

fof(f6481,plain,
    ( ~ spl10_919
    | ~ spl10_140
    | spl10_691 ),
    inference(avatar_split_clause,[],[f6474,f4213,f787,f6479])).

fof(f6479,plain,
    ( spl10_919
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_919])])).

fof(f787,plain,
    ( spl10_140
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f4213,plain,
    ( spl10_691
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_691])])).

fof(f6474,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_140
    | ~ spl10_691 ),
    inference(forward_demodulation,[],[f4214,f788])).

fof(f788,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_140 ),
    inference(avatar_component_clause,[],[f787])).

fof(f4214,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_691 ),
    inference(avatar_component_clause,[],[f4213])).

fof(f6436,plain,
    ( ~ spl10_917
    | ~ spl10_140
    | spl10_851 ),
    inference(avatar_split_clause,[],[f6429,f5636,f787,f6434])).

fof(f6434,plain,
    ( spl10_917
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_917])])).

fof(f5636,plain,
    ( spl10_851
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_851])])).

fof(f6429,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))))
    | ~ spl10_140
    | ~ spl10_851 ),
    inference(forward_demodulation,[],[f5637,f788])).

fof(f5637,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_851 ),
    inference(avatar_component_clause,[],[f5636])).

fof(f6343,plain,
    ( spl10_908
    | ~ spl10_118
    | ~ spl10_162
    | spl10_871 ),
    inference(avatar_split_clause,[],[f6342,f5743,f905,f646,f6215])).

fof(f6215,plain,
    ( spl10_908
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_908])])).

fof(f5743,plain,
    ( spl10_871
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_871])])).

fof(f6342,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_118
    | ~ spl10_162
    | ~ spl10_871 ),
    inference(subsumption_resolution,[],[f6329,f906])).

fof(f6329,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_118
    | ~ spl10_871 ),
    inference(superposition,[],[f5744,f3629])).

fof(f3629,plain,
    ( ! [X0] :
        ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0))))))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(resolution,[],[f2990,f445])).

fof(f5744,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))
    | ~ spl10_871 ),
    inference(avatar_component_clause,[],[f5743])).

fof(f6322,plain,
    ( spl10_804
    | ~ spl10_118
    | ~ spl10_162
    | spl10_773 ),
    inference(avatar_split_clause,[],[f6321,f5098,f905,f646,f5289])).

fof(f5289,plain,
    ( spl10_804
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_804])])).

fof(f5098,plain,
    ( spl10_773
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_773])])).

fof(f6321,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_118
    | ~ spl10_162
    | ~ spl10_773 ),
    inference(subsumption_resolution,[],[f6308,f906])).

fof(f6308,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_118
    | ~ spl10_773 ),
    inference(superposition,[],[f5099,f3629])).

fof(f5099,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))
    | ~ spl10_773 ),
    inference(avatar_component_clause,[],[f5098])).

fof(f6293,plain,
    ( ~ spl10_915
    | ~ spl10_140
    | spl10_621 ),
    inference(avatar_split_clause,[],[f6286,f3446,f787,f6291])).

fof(f6291,plain,
    ( spl10_915
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_915])])).

fof(f3446,plain,
    ( spl10_621
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_621])])).

fof(f6286,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_140
    | ~ spl10_621 ),
    inference(forward_demodulation,[],[f3447,f788])).

fof(f3447,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_621 ),
    inference(avatar_component_clause,[],[f3446])).

fof(f6257,plain,
    ( ~ spl10_913
    | ~ spl10_140
    | spl10_707 ),
    inference(avatar_split_clause,[],[f6250,f4316,f787,f6255])).

fof(f6255,plain,
    ( spl10_913
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_913])])).

fof(f4316,plain,
    ( spl10_707
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_707])])).

fof(f6250,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))))
    | ~ spl10_140
    | ~ spl10_707 ),
    inference(forward_demodulation,[],[f4317,f788])).

fof(f4317,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_707 ),
    inference(avatar_component_clause,[],[f4316])).

fof(f6249,plain,
    ( ~ spl10_911
    | ~ spl10_140
    | spl10_855 ),
    inference(avatar_split_clause,[],[f6242,f5656,f787,f6247])).

fof(f6247,plain,
    ( spl10_911
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_911])])).

fof(f5656,plain,
    ( spl10_855
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_855])])).

fof(f6242,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_140
    | ~ spl10_855 ),
    inference(forward_demodulation,[],[f5657,f788])).

fof(f5657,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_855 ),
    inference(avatar_component_clause,[],[f5656])).

fof(f6217,plain,
    ( spl10_908
    | ~ spl10_118
    | spl10_869 ),
    inference(avatar_split_clause,[],[f6205,f5736,f646,f6215])).

fof(f5736,plain,
    ( spl10_869
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_869])])).

fof(f6205,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_118
    | ~ spl10_869 ),
    inference(trivial_inequality_removal,[],[f6202])).

fof(f6202,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_118
    | ~ spl10_869 ),
    inference(superposition,[],[f5737,f3629])).

fof(f5737,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))
    | ~ spl10_869 ),
    inference(avatar_component_clause,[],[f5736])).

fof(f6178,plain,
    ( spl10_804
    | ~ spl10_118
    | spl10_775 ),
    inference(avatar_split_clause,[],[f6172,f5105,f646,f5289])).

fof(f5105,plain,
    ( spl10_775
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_775])])).

fof(f6172,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_118
    | ~ spl10_775 ),
    inference(trivial_inequality_removal,[],[f6169])).

fof(f6169,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_118
    | ~ spl10_775 ),
    inference(superposition,[],[f5106,f3629])).

fof(f5106,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))
    | ~ spl10_775 ),
    inference(avatar_component_clause,[],[f5105])).

fof(f6159,plain,
    ( spl10_906
    | ~ spl10_118
    | spl10_795 ),
    inference(avatar_split_clause,[],[f6152,f5185,f646,f6157])).

fof(f6157,plain,
    ( spl10_906
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_906])])).

fof(f5185,plain,
    ( spl10_795
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_795])])).

fof(f6152,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl10_118
    | ~ spl10_795 ),
    inference(trivial_inequality_removal,[],[f6149])).

fof(f6149,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK2))
    | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl10_118
    | ~ spl10_795 ),
    inference(superposition,[],[f5186,f3629])).

fof(f5186,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))))
    | ~ spl10_795 ),
    inference(avatar_component_clause,[],[f5185])).

fof(f6083,plain,
    ( ~ spl10_905
    | ~ spl10_140
    | spl10_699 ),
    inference(avatar_split_clause,[],[f6076,f4267,f787,f6081])).

fof(f6081,plain,
    ( spl10_905
  <=> k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_905])])).

fof(f4267,plain,
    ( spl10_699
  <=> k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_699])])).

fof(f6076,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_140
    | ~ spl10_699 ),
    inference(forward_demodulation,[],[f4268,f788])).

fof(f4268,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_699 ),
    inference(avatar_component_clause,[],[f4267])).

fof(f6029,plain,
    ( ~ spl10_903
    | ~ spl10_140
    | spl10_705 ),
    inference(avatar_split_clause,[],[f6022,f4303,f787,f6027])).

fof(f6027,plain,
    ( spl10_903
  <=> ~ r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_903])])).

fof(f4303,plain,
    ( spl10_705
  <=> ~ r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_705])])).

fof(f6022,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))),u1_struct_0(sK0))
    | ~ spl10_140
    | ~ spl10_705 ),
    inference(forward_demodulation,[],[f4304,f788])).

fof(f4304,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_705 ),
    inference(avatar_component_clause,[],[f4303])).

fof(f6021,plain,
    ( ~ spl10_901
    | ~ spl10_140
    | spl10_695 ),
    inference(avatar_split_clause,[],[f6014,f4231,f787,f6019])).

fof(f6019,plain,
    ( spl10_901
  <=> ~ m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_901])])).

fof(f4231,plain,
    ( spl10_695
  <=> ~ m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_695])])).

fof(f6014,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))),u1_struct_0(sK0))
    | ~ spl10_140
    | ~ spl10_695 ),
    inference(forward_demodulation,[],[f4232,f788])).

fof(f4232,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_695 ),
    inference(avatar_component_clause,[],[f4231])).

fof(f5976,plain,
    ( spl10_862
    | spl10_888
    | ~ spl10_118
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f5926,f787,f646,f5859,f5718])).

fof(f5718,plain,
    ( spl10_862
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_862])])).

fof(f5859,plain,
    ( spl10_888
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_888])])).

fof(f5926,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_118
    | ~ spl10_140 ),
    inference(superposition,[],[f1000,f788])).

fof(f1000,plain,
    ( ! [X0] :
        ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(resolution,[],[f888,f445])).

fof(f5975,plain,
    ( spl10_860
    | spl10_888
    | ~ spl10_118
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f5925,f787,f646,f5859,f5711])).

fof(f5711,plain,
    ( spl10_860
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_860])])).

fof(f5925,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_118
    | ~ spl10_140 ),
    inference(superposition,[],[f889,f788])).

fof(f889,plain,
    ( ! [X0] :
        ( k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(X0)) )
    | ~ spl10_118 ),
    inference(resolution,[],[f780,f445])).

fof(f780,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(X2)) )
    | ~ spl10_118 ),
    inference(resolution,[],[f756,f404])).

fof(f5974,plain,
    ( spl10_888
    | ~ spl10_118
    | ~ spl10_140
    | spl10_859 ),
    inference(avatar_split_clause,[],[f5973,f5701,f787,f646,f5859])).

fof(f5701,plain,
    ( spl10_859
  <=> k1_zfmisc_1(u1_struct_0(sK1)) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_859])])).

fof(f5973,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_140
    | ~ spl10_859 ),
    inference(subsumption_resolution,[],[f5924,f5702])).

fof(f5702,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_859 ),
    inference(avatar_component_clause,[],[f5701])).

fof(f5924,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_140 ),
    inference(superposition,[],[f778,f788])).

fof(f778,plain,
    ( ! [X0] :
        ( k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0)
        | sK3(k1_zfmisc_1(sK2)) = X0 )
    | ~ spl10_118 ),
    inference(resolution,[],[f756,f445])).

fof(f5957,plain,
    ( ~ spl10_899
    | ~ spl10_140
    | spl10_709 ),
    inference(avatar_split_clause,[],[f5897,f4326,f787,f5955])).

fof(f5955,plain,
    ( spl10_899
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_899])])).

fof(f4326,plain,
    ( spl10_709
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_709])])).

fof(f5897,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))))
    | ~ spl10_140
    | ~ spl10_709 ),
    inference(backward_demodulation,[],[f788,f4327])).

fof(f4327,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_709 ),
    inference(avatar_component_clause,[],[f4326])).

fof(f5950,plain,
    ( ~ spl10_897
    | ~ spl10_140
    | spl10_701 ),
    inference(avatar_split_clause,[],[f5896,f4277,f787,f5948])).

fof(f5948,plain,
    ( spl10_897
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_897])])).

fof(f4277,plain,
    ( spl10_701
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_701])])).

fof(f5896,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_140
    | ~ spl10_701 ),
    inference(backward_demodulation,[],[f788,f4278])).

fof(f4278,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_701 ),
    inference(avatar_component_clause,[],[f4277])).

fof(f5943,plain,
    ( ~ spl10_895
    | ~ spl10_140
    | spl10_697 ),
    inference(avatar_split_clause,[],[f5895,f4253,f787,f5941])).

fof(f5941,plain,
    ( spl10_895
  <=> ~ r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_895])])).

fof(f4253,plain,
    ( spl10_697
  <=> ~ r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_697])])).

fof(f5895,plain,
    ( ~ r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK1))
    | ~ spl10_140
    | ~ spl10_697 ),
    inference(backward_demodulation,[],[f788,f4254])).

fof(f4254,plain,
    ( ~ r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_697 ),
    inference(avatar_component_clause,[],[f4253])).

fof(f5936,plain,
    ( ~ spl10_893
    | ~ spl10_140
    | spl10_693 ),
    inference(avatar_split_clause,[],[f5894,f4228,f787,f5934])).

fof(f5934,plain,
    ( spl10_893
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_893])])).

fof(f4228,plain,
    ( spl10_693
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_693])])).

fof(f5894,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK1))
    | ~ spl10_140
    | ~ spl10_693 ),
    inference(backward_demodulation,[],[f788,f4229])).

fof(f4229,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_693 ),
    inference(avatar_component_clause,[],[f4228])).

fof(f5929,plain,
    ( spl10_888
    | ~ spl10_140
    | ~ spl10_154 ),
    inference(avatar_split_clause,[],[f5893,f858,f787,f5859])).

fof(f858,plain,
    ( spl10_154
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(u1_struct_0(sK1)))) = sK3(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f5893,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_140
    | ~ spl10_154 ),
    inference(backward_demodulation,[],[f788,f859])).

fof(f859,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(u1_struct_0(sK1)))) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_154 ),
    inference(avatar_component_clause,[],[f858])).

fof(f5888,plain,
    ( spl10_140
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5886,f646,f633,f787])).

fof(f633,plain,
    ( spl10_114
  <=> v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f5886,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f5790,f647])).

fof(f5790,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK3(k1_zfmisc_1(u1_struct_0(sK1))) = X0 )
    | ~ spl10_114 ),
    inference(resolution,[],[f634,f122])).

fof(f634,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_114 ),
    inference(avatar_component_clause,[],[f633])).

fof(f5869,plain,
    ( ~ spl10_891
    | ~ spl10_150 ),
    inference(avatar_split_clause,[],[f5853,f843,f5867])).

fof(f5867,plain,
    ( spl10_891
  <=> ~ sP9(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_891])])).

fof(f843,plain,
    ( spl10_150
  <=> r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_150])])).

fof(f5853,plain,
    ( ~ sP9(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_150 ),
    inference(resolution,[],[f844,f135])).

fof(f844,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_150 ),
    inference(avatar_component_clause,[],[f843])).

fof(f5862,plain,
    ( spl10_152
    | ~ spl10_150 ),
    inference(avatar_split_clause,[],[f5852,f843,f850])).

fof(f850,plain,
    ( spl10_152
  <=> m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_152])])).

fof(f5852,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_150 ),
    inference(resolution,[],[f844,f105])).

fof(f5861,plain,
    ( spl10_888
    | ~ spl10_150 ),
    inference(avatar_split_clause,[],[f5850,f843,f5859])).

fof(f5850,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_150 ),
    inference(resolution,[],[f844,f128])).

fof(f5849,plain,
    ( spl10_886
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5799,f646,f633,f5847])).

fof(f5847,plain,
    ( spl10_886
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_886])])).

fof(f5799,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f4487])).

fof(f4487,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f4138,f404])).

fof(f4138,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))))))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f3630,f403])).

fof(f3630,plain,
    ( ! [X1] :
        ( ~ sP9(X1)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f2990,f612])).

fof(f5842,plain,
    ( spl10_884
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5798,f646,f633,f5840])).

fof(f5840,plain,
    ( spl10_884
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_884])])).

fof(f5798,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f4138])).

fof(f5835,plain,
    ( spl10_882
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5797,f646,f633,f5833])).

fof(f5833,plain,
    ( spl10_882
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_882])])).

fof(f5797,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f3631])).

fof(f5828,plain,
    ( spl10_880
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5796,f646,f633,f5826])).

fof(f5826,plain,
    ( spl10_880
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_880])])).

fof(f5796,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f2990])).

fof(f5821,plain,
    ( spl10_878
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5795,f646,f633,f5819])).

fof(f5819,plain,
    ( spl10_878
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_878])])).

fof(f5795,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f1002])).

fof(f1002,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f888,f404])).

fof(f5814,plain,
    ( spl10_876
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5794,f646,f633,f5812])).

fof(f5812,plain,
    ( spl10_876
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_876])])).

fof(f5794,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f888])).

fof(f5807,plain,
    ( spl10_874
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5793,f646,f633,f5805])).

fof(f5805,plain,
    ( spl10_874
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_874])])).

fof(f5793,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f780])).

fof(f5800,plain,
    ( spl10_140
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5792,f646,f633,f787])).

fof(f5792,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f634,f756])).

fof(f5755,plain,
    ( spl10_872
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5699,f830,f646,f5753])).

fof(f5753,plain,
    ( spl10_872
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_872])])).

fof(f830,plain,
    ( spl10_146
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f5699,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f4487])).

fof(f831,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_146 ),
    inference(avatar_component_clause,[],[f830])).

fof(f5748,plain,
    ( spl10_870
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5698,f830,f646,f5746])).

fof(f5746,plain,
    ( spl10_870
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_870])])).

fof(f5698,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f4138])).

fof(f5741,plain,
    ( spl10_868
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5697,f830,f646,f5739])).

fof(f5739,plain,
    ( spl10_868
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_868])])).

fof(f5697,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f3631])).

fof(f5734,plain,
    ( spl10_866
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5696,f830,f646,f5732])).

fof(f5732,plain,
    ( spl10_866
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_866])])).

fof(f5696,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f2990])).

fof(f5727,plain,
    ( spl10_864
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5695,f830,f646,f5725])).

fof(f5725,plain,
    ( spl10_864
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_864])])).

fof(f5695,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f1002])).

fof(f5720,plain,
    ( spl10_862
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5694,f830,f646,f5718])).

fof(f5694,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f888])).

fof(f5713,plain,
    ( spl10_860
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5693,f830,f646,f5711])).

fof(f5693,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f780])).

fof(f5706,plain,
    ( spl10_858
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f5692,f830,f646,f5704])).

fof(f5704,plain,
    ( spl10_858
  <=> k1_zfmisc_1(u1_struct_0(sK1)) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_858])])).

fof(f5692,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_146 ),
    inference(resolution,[],[f831,f756])).

fof(f5686,plain,
    ( spl10_114
    | spl10_620
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39 ),
    inference(avatar_split_clause,[],[f3435,f285,f197,f190,f183,f3449,f633])).

fof(f3449,plain,
    ( spl10_620
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_620])])).

fof(f285,plain,
    ( spl10_39
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f3435,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(resolution,[],[f3432,f401])).

fof(f3432,plain,
    ( ! [X21] :
        ( ~ m1_subset_1(X21,u1_struct_0(sK1))
        | k1_funct_1(sK2,X21) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X21) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f3431,f286])).

fof(f286,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f285])).

fof(f3431,plain,
    ( ! [X21] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X21,u1_struct_0(sK1))
        | k1_funct_1(sK2,X21) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X21) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3430,f191])).

fof(f3430,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X21,u1_struct_0(sK1))
        | k1_funct_1(sK2,X21) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X21) )
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3411,f198])).

fof(f3411,plain,
    ( ! [X21] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X21,u1_struct_0(sK1))
        | k1_funct_1(sK2,X21) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X21) )
    | ~ spl10_12 ),
    inference(resolution,[],[f125,f184])).

fof(f5685,plain,
    ( spl10_114
    | spl10_690
    | spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f4201,f2194,f2169,f2055,f285,f4216,f633])).

fof(f4216,plain,
    ( spl10_690
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_690])])).

fof(f2055,plain,
    ( spl10_400
  <=> v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_400])])).

fof(f2169,plain,
    ( spl10_414
  <=> m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_414])])).

fof(f2194,plain,
    ( spl10_420
  <=> v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_420])])).

fof(f4201,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(resolution,[],[f3419,f401])).

fof(f3419,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X5) )
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3418,f286])).

fof(f3418,plain,
    ( ! [X5] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X5) )
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3417,f2056])).

fof(f2056,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_400 ),
    inference(avatar_component_clause,[],[f2055])).

fof(f3417,plain,
    ( ! [X5] :
        ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X5) )
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3405,f2195])).

fof(f2195,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ spl10_420 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f3405,plain,
    ( ! [X5] :
        ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X5) )
    | ~ spl10_414 ),
    inference(resolution,[],[f125,f2170])).

fof(f2170,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_414 ),
    inference(avatar_component_clause,[],[f2169])).

fof(f5684,plain,
    ( spl10_856
    | ~ spl10_28
    | spl10_39
    | ~ spl10_836 ),
    inference(avatar_split_clause,[],[f5677,f5496,f285,f246,f5682])).

fof(f5682,plain,
    ( spl10_856
  <=> k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_856])])).

fof(f246,plain,
    ( spl10_28
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f5496,plain,
    ( spl10_836
  <=> m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_836])])).

fof(f5677,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_28
    | ~ spl10_39
    | ~ spl10_836 ),
    inference(subsumption_resolution,[],[f5676,f247])).

fof(f247,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f5676,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl10_39
    | ~ spl10_836 ),
    inference(subsumption_resolution,[],[f5628,f286])).

fof(f5628,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl10_836 ),
    inference(resolution,[],[f3424,f5497])).

fof(f5497,plain,
    ( m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_836 ),
    inference(avatar_component_clause,[],[f5496])).

fof(f5675,plain,
    ( spl10_838
    | ~ spl10_22
    | spl10_209
    | ~ spl10_822 ),
    inference(avatar_split_clause,[],[f5674,f5420,f1151,f220,f5509])).

fof(f5420,plain,
    ( spl10_822
  <=> m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_822])])).

fof(f5674,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_822 ),
    inference(subsumption_resolution,[],[f5673,f221])).

fof(f5673,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl10_209
    | ~ spl10_822 ),
    inference(subsumption_resolution,[],[f5627,f1152])).

fof(f5627,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ l1_struct_0(sK0)
    | ~ spl10_822 ),
    inference(resolution,[],[f3424,f5421])).

fof(f5421,plain,
    ( m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_822 ),
    inference(avatar_component_clause,[],[f5420])).

fof(f5661,plain,
    ( spl10_854
    | ~ spl10_28
    | spl10_39
    | ~ spl10_692
    | ~ spl10_698 ),
    inference(avatar_split_clause,[],[f5654,f4270,f4225,f285,f246,f5659])).

fof(f5659,plain,
    ( spl10_854
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_854])])).

fof(f4225,plain,
    ( spl10_692
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_692])])).

fof(f4270,plain,
    ( spl10_698
  <=> k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_698])])).

fof(f5654,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_28
    | ~ spl10_39
    | ~ spl10_692
    | ~ spl10_698 ),
    inference(forward_demodulation,[],[f5653,f4271])).

fof(f4271,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_698 ),
    inference(avatar_component_clause,[],[f4270])).

fof(f5653,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_28
    | ~ spl10_39
    | ~ spl10_692 ),
    inference(subsumption_resolution,[],[f5652,f247])).

fof(f5652,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_39
    | ~ spl10_692 ),
    inference(subsumption_resolution,[],[f5618,f286])).

fof(f5618,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_692 ),
    inference(resolution,[],[f3424,f4226])).

fof(f4226,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_692 ),
    inference(avatar_component_clause,[],[f4225])).

fof(f5651,plain,
    ( spl10_852
    | ~ spl10_22
    | spl10_209
    | ~ spl10_710
    | ~ spl10_716 ),
    inference(avatar_split_clause,[],[f5644,f4377,f4347,f1151,f220,f5649])).

fof(f5649,plain,
    ( spl10_852
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_852])])).

fof(f4347,plain,
    ( spl10_710
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_710])])).

fof(f4377,plain,
    ( spl10_716
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_716])])).

fof(f5644,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_710
    | ~ spl10_716 ),
    inference(forward_demodulation,[],[f5643,f4378])).

fof(f4378,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_716 ),
    inference(avatar_component_clause,[],[f4377])).

fof(f5643,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_710 ),
    inference(subsumption_resolution,[],[f5642,f221])).

fof(f5642,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_209
    | ~ spl10_710 ),
    inference(subsumption_resolution,[],[f5616,f1152])).

fof(f5616,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_710 ),
    inference(resolution,[],[f3424,f4348])).

fof(f4348,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_710 ),
    inference(avatar_component_clause,[],[f4347])).

fof(f5641,plain,
    ( spl10_850
    | ~ spl10_22
    | spl10_209
    | ~ spl10_694
    | ~ spl10_706 ),
    inference(avatar_split_clause,[],[f5634,f4319,f4234,f1151,f220,f5639])).

fof(f5639,plain,
    ( spl10_850
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_850])])).

fof(f4234,plain,
    ( spl10_694
  <=> m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_694])])).

fof(f4319,plain,
    ( spl10_706
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_706])])).

fof(f5634,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_694
    | ~ spl10_706 ),
    inference(forward_demodulation,[],[f5633,f4320])).

fof(f4320,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_706 ),
    inference(avatar_component_clause,[],[f4319])).

fof(f5633,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_22
    | ~ spl10_209
    | ~ spl10_694 ),
    inference(subsumption_resolution,[],[f5632,f221])).

fof(f5632,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_209
    | ~ spl10_694 ),
    inference(subsumption_resolution,[],[f5615,f1152])).

fof(f5615,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ l1_struct_0(sK0)
    | ~ spl10_694 ),
    inference(resolution,[],[f3424,f4235])).

fof(f4235,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_694 ),
    inference(avatar_component_clause,[],[f4234])).

fof(f5556,plain,
    ( ~ spl10_849
    | ~ spl10_840 ),
    inference(avatar_split_clause,[],[f5538,f5517,f5554])).

fof(f5554,plain,
    ( spl10_849
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_849])])).

fof(f5517,plain,
    ( spl10_840
  <=> r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_840])])).

fof(f5538,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_840 ),
    inference(resolution,[],[f5518,f106])).

fof(f5518,plain,
    ( r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_840 ),
    inference(avatar_component_clause,[],[f5517])).

fof(f5549,plain,
    ( spl10_846
    | ~ spl10_52
    | ~ spl10_840 ),
    inference(avatar_split_clause,[],[f5542,f5517,f345,f5547])).

fof(f5542,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_52
    | ~ spl10_840 ),
    inference(forward_demodulation,[],[f5537,f346])).

fof(f5537,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK0)),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_840 ),
    inference(resolution,[],[f5518,f128])).

fof(f5536,plain,
    ( spl10_844
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39
    | ~ spl10_836 ),
    inference(avatar_split_clause,[],[f5521,f5496,f285,f197,f190,f183,f5534])).

fof(f5521,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39
    | ~ spl10_836 ),
    inference(resolution,[],[f5497,f3432])).

fof(f5529,plain,
    ( spl10_842
    | spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_836 ),
    inference(avatar_split_clause,[],[f5520,f5496,f2194,f2169,f2055,f285,f5527])).

fof(f5527,plain,
    ( spl10_842
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_842])])).

fof(f5520,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_836 ),
    inference(resolution,[],[f5497,f3419])).

fof(f5519,plain,
    ( spl10_840
    | spl10_209
    | ~ spl10_822 ),
    inference(avatar_split_clause,[],[f5512,f5420,f1151,f5517])).

fof(f5512,plain,
    ( r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_822 ),
    inference(subsumption_resolution,[],[f5504,f1152])).

fof(f5504,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_822 ),
    inference(resolution,[],[f5421,f104])).

fof(f5511,plain,
    ( spl10_838
    | ~ spl10_632
    | ~ spl10_822 ),
    inference(avatar_split_clause,[],[f5503,f5420,f3503,f5509])).

fof(f5503,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_632
    | ~ spl10_822 ),
    inference(resolution,[],[f5421,f3504])).

fof(f5498,plain,
    ( spl10_836
    | ~ spl10_818 ),
    inference(avatar_split_clause,[],[f5473,f5389,f5496])).

fof(f5389,plain,
    ( spl10_818
  <=> r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_818])])).

fof(f5473,plain,
    ( m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_818 ),
    inference(resolution,[],[f5390,f105])).

fof(f5390,plain,
    ( r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_818 ),
    inference(avatar_component_clause,[],[f5389])).

fof(f5491,plain,
    ( ~ spl10_835
    | ~ spl10_818 ),
    inference(avatar_split_clause,[],[f5472,f5389,f5489])).

fof(f5489,plain,
    ( spl10_835
  <=> ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_835])])).

fof(f5472,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2))
    | ~ spl10_818 ),
    inference(resolution,[],[f5390,f106])).

fof(f5484,plain,
    ( spl10_832
    | ~ spl10_54
    | ~ spl10_818 ),
    inference(avatar_split_clause,[],[f5477,f5389,f352,f5482])).

fof(f5482,plain,
    ( spl10_832
  <=> k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_832])])).

fof(f352,plain,
    ( spl10_54
  <=> k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f5477,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_54
    | ~ spl10_818 ),
    inference(forward_demodulation,[],[f5471,f353])).

fof(f353,plain,
    ( k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f352])).

fof(f5471,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK1)),sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_818 ),
    inference(resolution,[],[f5390,f128])).

fof(f5476,plain,
    ( spl10_800
    | ~ spl10_823
    | ~ spl10_818 ),
    inference(avatar_split_clause,[],[f5470,f5389,f5417,f5227])).

fof(f5417,plain,
    ( spl10_823
  <=> ~ m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_823])])).

fof(f5470,plain,
    ( ~ m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_818 ),
    inference(resolution,[],[f5390,f83])).

fof(f83,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_struct_0(sK1))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_funct_1(sK2,X3) = X3 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',t96_tmap_1)).

fof(f5458,plain,
    ( ~ spl10_831
    | ~ spl10_824 ),
    inference(avatar_split_clause,[],[f5434,f5429,f5456])).

fof(f5456,plain,
    ( spl10_831
  <=> ~ r2_hidden(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_831])])).

fof(f5429,plain,
    ( spl10_824
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_824])])).

fof(f5434,plain,
    ( ~ r2_hidden(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | ~ spl10_824 ),
    inference(resolution,[],[f5430,f106])).

fof(f5430,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | ~ spl10_824 ),
    inference(avatar_component_clause,[],[f5429])).

fof(f5451,plain,
    ( spl10_828
    | ~ spl10_824 ),
    inference(avatar_split_clause,[],[f5433,f5429,f5449])).

fof(f5449,plain,
    ( spl10_828
  <=> k1_funct_1(k6_relat_1(sK2),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_828])])).

fof(f5433,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_824 ),
    inference(resolution,[],[f5430,f128])).

fof(f5444,plain,
    ( spl10_826
    | ~ spl10_42
    | ~ spl10_824 ),
    inference(avatar_split_clause,[],[f5432,f5429,f301,f5442])).

fof(f5442,plain,
    ( spl10_826
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_826])])).

fof(f301,plain,
    ( spl10_42
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f5432,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_42
    | ~ spl10_824 ),
    inference(resolution,[],[f5430,f993])).

fof(f993,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_42 ),
    inference(resolution,[],[f302,f128])).

fof(f302,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f301])).

fof(f5431,plain,
    ( spl10_824
    | spl10_79
    | ~ spl10_810 ),
    inference(avatar_split_clause,[],[f5424,f5332,f463,f5429])).

fof(f463,plain,
    ( spl10_79
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f5332,plain,
    ( spl10_810
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_810])])).

fof(f5424,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | ~ spl10_79
    | ~ spl10_810 ),
    inference(subsumption_resolution,[],[f5423,f464])).

fof(f464,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f463])).

fof(f5423,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | ~ spl10_810 ),
    inference(resolution,[],[f5333,f104])).

fof(f5333,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | ~ spl10_810 ),
    inference(avatar_component_clause,[],[f5332])).

fof(f5422,plain,
    ( spl10_822
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420
    | spl10_821 ),
    inference(avatar_split_clause,[],[f5415,f5392,f2194,f2055,f2046,f2040,f2034,f871,f246,f220,f197,f190,f183,f169,f162,f155,f148,f141,f5420])).

fof(f5392,plain,
    ( spl10_821
  <=> k4_tmap_1(sK0,sK1) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_821])])).

fof(f5415,plain,
    ( m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420
    | ~ spl10_821 ),
    inference(subsumption_resolution,[],[f5414,f5393])).

fof(f5393,plain,
    ( k4_tmap_1(sK0,sK1) != sK2
    | ~ spl10_821 ),
    inference(avatar_component_clause,[],[f5392])).

fof(f5414,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420 ),
    inference(forward_demodulation,[],[f5413,f872])).

fof(f5413,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f5412,f2195])).

fof(f5412,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f5411,f872])).

fof(f5411,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5410,f163])).

fof(f5410,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5409,f142])).

fof(f5409,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5408,f149])).

fof(f5408,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5407,f156])).

fof(f5407,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5406,f2047])).

fof(f5406,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5405,f2041])).

fof(f5405,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5404,f2035])).

fof(f5404,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5399,f2056])).

fof(f5399,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156 ),
    inference(superposition,[],[f3244,f872])).

fof(f3244,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3243,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_l1_pre_topc)).

fof(f3243,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3242,f156])).

fof(f3242,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3241,f149])).

fof(f3241,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3240,f184])).

fof(f3240,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3239,f191])).

fof(f3239,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3238,f198])).

fof(f3238,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3237,f170])).

fof(f3237,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3227,f142])).

fof(f3227,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(duplicate_literal_removal,[],[f3225])).

fof(f3225,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2)
        | m1_subset_1(sK6(sK0,X3,sK1,X2,sK2),u1_struct_0(X3))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X3)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(resolution,[],[f2149,f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f2149,plain,
    ( ! [X2,X3] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X3,sK0,X2,sK1),sK2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ v1_funct_1(X2) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f2148,f247])).

fof(f2148,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X3,sK0,X2,sK1),sK2) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f2134,f221])).

fof(f2134,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X2,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X2,sK1))
        | k2_tmap_1(X3,sK0,X2,sK1) = sK2
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tmap_1(X3,sK0,X2,sK1),sK2) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f114,f975])).

fof(f975,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | sK2 = X3
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f974,f191])).

fof(f974,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | sK2 = X3
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2) )
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f969,f198])).

fof(f969,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | sK2 = X3
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f94,f184])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',redefinition_r2_funct_2)).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_k2_tmap_1)).

fof(f5397,plain,
    ( spl10_818
    | spl10_820
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f5384,f2194,f2055,f2046,f2040,f2034,f871,f246,f220,f197,f190,f183,f169,f162,f155,f148,f141,f5395,f5389])).

fof(f5395,plain,
    ( spl10_820
  <=> k4_tmap_1(sK0,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_820])])).

fof(f5384,plain,
    ( k4_tmap_1(sK0,sK1) = sK2
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420 ),
    inference(forward_demodulation,[],[f5383,f872])).

fof(f5383,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f5382,f2195])).

fof(f5382,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f5381,f872])).

fof(f5381,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5380,f163])).

fof(f5380,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5379,f142])).

fof(f5379,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5378,f149])).

fof(f5378,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5377,f156])).

fof(f5377,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5376,f2047])).

fof(f5376,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5375,f2041])).

fof(f5375,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5374,f2035])).

fof(f5374,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f5369,f2056])).

fof(f5369,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = sK2
    | ~ v1_funct_1(k3_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2),u1_struct_0(sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156 ),
    inference(superposition,[],[f3236,f872])).

fof(f3236,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3235,f124])).

fof(f3235,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3234,f156])).

fof(f3234,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3233,f184])).

fof(f3233,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3232,f191])).

fof(f3232,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3231,f198])).

fof(f3231,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3230,f170])).

fof(f3230,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3229,f142])).

fof(f3229,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_2
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3228,f149])).

fof(f3228,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(duplicate_literal_removal,[],[f3224])).

fof(f3224,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,sK1))
        | k2_tmap_1(X1,sK0,X0,sK1) = sK2
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,X1,sK1,X0,sK2),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(resolution,[],[f2149,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f5367,plain,
    ( spl10_298
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f5301,f1540,f1547])).

fof(f1547,plain,
    ( spl10_298
  <=> m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_298])])).

fof(f1540,plain,
    ( spl10_296
  <=> r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_296])])).

fof(f5301,plain,
    ( m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_296 ),
    inference(resolution,[],[f1541,f105])).

fof(f1541,plain,
    ( r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_296 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f5366,plain,
    ( ~ spl10_817
    | ~ spl10_290 ),
    inference(avatar_split_clause,[],[f5342,f1516,f5364])).

fof(f5364,plain,
    ( spl10_817
  <=> ~ r2_hidden(sK2,sK3(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_817])])).

fof(f1516,plain,
    ( spl10_290
  <=> r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_290])])).

fof(f5342,plain,
    ( ~ r2_hidden(sK2,sK3(u1_struct_0(sK4(sK0))))
    | ~ spl10_290 ),
    inference(resolution,[],[f1517,f106])).

fof(f1517,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_290 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f5359,plain,
    ( spl10_814
    | ~ spl10_290 ),
    inference(avatar_split_clause,[],[f5341,f1516,f5357])).

fof(f5357,plain,
    ( spl10_814
  <=> k1_funct_1(k6_relat_1(sK2),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_814])])).

fof(f5341,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | ~ spl10_290 ),
    inference(resolution,[],[f1517,f128])).

fof(f5352,plain,
    ( spl10_812
    | ~ spl10_42
    | ~ spl10_290 ),
    inference(avatar_split_clause,[],[f5340,f1516,f301,f5350])).

fof(f5350,plain,
    ( spl10_812
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_812])])).

fof(f5340,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | ~ spl10_42
    | ~ spl10_290 ),
    inference(resolution,[],[f1517,f993])).

fof(f5339,plain,
    ( spl10_290
    | spl10_79
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f5336,f1524,f463,f1516])).

fof(f1524,plain,
    ( spl10_292
  <=> m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_292])])).

fof(f5336,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_79
    | ~ spl10_292 ),
    inference(subsumption_resolution,[],[f5335,f464])).

fof(f5335,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_292 ),
    inference(resolution,[],[f1525,f104])).

fof(f1525,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_292 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f5338,plain,
    ( spl10_79
    | spl10_291
    | ~ spl10_292 ),
    inference(avatar_contradiction_clause,[],[f5337])).

fof(f5337,plain,
    ( $false
    | ~ spl10_79
    | ~ spl10_291
    | ~ spl10_292 ),
    inference(subsumption_resolution,[],[f5336,f1514])).

fof(f1514,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_291 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f1513,plain,
    ( spl10_291
  <=> ~ r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_291])])).

fof(f5334,plain,
    ( spl10_810
    | ~ spl10_298
    | spl10_765 ),
    inference(avatar_split_clause,[],[f5325,f5060,f1547,f5332])).

fof(f5325,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | ~ spl10_298
    | ~ spl10_765 ),
    inference(subsumption_resolution,[],[f5319,f5061])).

fof(f5319,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_298 ),
    inference(resolution,[],[f5293,f547])).

fof(f5293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK4(sK0)))
        | m1_subset_1(X0,sK2) )
    | ~ spl10_298 ),
    inference(resolution,[],[f1548,f102])).

fof(f1548,plain,
    ( m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_298 ),
    inference(avatar_component_clause,[],[f1547])).

fof(f5327,plain,
    ( spl10_292
    | spl10_267
    | ~ spl10_298 ),
    inference(avatar_split_clause,[],[f5326,f1547,f1428,f1524])).

fof(f5326,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_267
    | ~ spl10_298 ),
    inference(subsumption_resolution,[],[f5318,f1429])).

fof(f5318,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_298 ),
    inference(resolution,[],[f5293,f251])).

fof(f5324,plain,
    ( spl10_267
    | spl10_293
    | ~ spl10_298 ),
    inference(avatar_contradiction_clause,[],[f5323])).

fof(f5323,plain,
    ( $false
    | ~ spl10_267
    | ~ spl10_293
    | ~ spl10_298 ),
    inference(subsumption_resolution,[],[f5322,f1429])).

fof(f5322,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_293
    | ~ spl10_298 ),
    inference(subsumption_resolution,[],[f5318,f1522])).

fof(f1522,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_293 ),
    inference(avatar_component_clause,[],[f1521])).

fof(f1521,plain,
    ( spl10_293
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_293])])).

fof(f5317,plain,
    ( ~ spl10_809
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f5302,f1540,f5315])).

fof(f5315,plain,
    ( spl10_809
  <=> ~ sP9(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_809])])).

fof(f5302,plain,
    ( ~ sP9(k1_zfmisc_1(sK2))
    | ~ spl10_296 ),
    inference(resolution,[],[f1541,f135])).

fof(f5310,plain,
    ( spl10_806
    | ~ spl10_296 ),
    inference(avatar_split_clause,[],[f5299,f1540,f5308])).

fof(f5308,plain,
    ( spl10_806
  <=> u1_struct_0(sK4(sK0)) = k1_funct_1(k6_relat_1(k1_zfmisc_1(sK2)),u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_806])])).

fof(f5299,plain,
    ( u1_struct_0(sK4(sK0)) = k1_funct_1(k6_relat_1(k1_zfmisc_1(sK2)),u1_struct_0(sK4(sK0)))
    | ~ spl10_296 ),
    inference(resolution,[],[f1541,f128])).

fof(f5298,plain,
    ( spl10_296
    | spl10_233
    | ~ spl10_298 ),
    inference(avatar_split_clause,[],[f5295,f1547,f1272,f1540])).

fof(f1272,plain,
    ( spl10_233
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_233])])).

fof(f5295,plain,
    ( r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_233
    | ~ spl10_298 ),
    inference(subsumption_resolution,[],[f5294,f1273])).

fof(f1273,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_233 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f5294,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_298 ),
    inference(resolution,[],[f1548,f104])).

fof(f5297,plain,
    ( spl10_233
    | spl10_297
    | ~ spl10_298 ),
    inference(avatar_contradiction_clause,[],[f5296])).

fof(f5296,plain,
    ( $false
    | ~ spl10_233
    | ~ spl10_297
    | ~ spl10_298 ),
    inference(subsumption_resolution,[],[f5295,f1538])).

fof(f1538,plain,
    ( ~ r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_297 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f1537,plain,
    ( spl10_297
  <=> ~ r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_297])])).

fof(f5291,plain,
    ( spl10_804
    | spl10_765 ),
    inference(avatar_split_clause,[],[f5284,f5060,f5289])).

fof(f5284,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_765 ),
    inference(resolution,[],[f5061,f445])).

fof(f5281,plain,
    ( spl10_802
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5267,f5063,f646,f5279])).

fof(f5279,plain,
    ( spl10_802
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_802])])).

fof(f5063,plain,
    ( spl10_764
  <=> v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_764])])).

fof(f5267,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f4487])).

fof(f5064,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_764 ),
    inference(avatar_component_clause,[],[f5063])).

fof(f5274,plain,
    ( spl10_770
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5266,f5063,f646,f5094])).

fof(f5094,plain,
    ( spl10_770
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_770])])).

fof(f5266,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f4138])).

fof(f5273,plain,
    ( spl10_772
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5265,f5063,f646,f5101])).

fof(f5101,plain,
    ( spl10_772
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_772])])).

fof(f5265,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f3631])).

fof(f5272,plain,
    ( spl10_774
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5264,f5063,f646,f5108])).

fof(f5108,plain,
    ( spl10_774
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_774])])).

fof(f5264,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f2990])).

fof(f5271,plain,
    ( spl10_776
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5263,f5063,f646,f5115])).

fof(f5115,plain,
    ( spl10_776
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_776])])).

fof(f5263,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f1002])).

fof(f5270,plain,
    ( spl10_778
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5262,f5063,f646,f5122])).

fof(f5122,plain,
    ( spl10_778
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_778])])).

fof(f5262,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f888])).

fof(f5269,plain,
    ( spl10_780
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5261,f5063,f646,f5129])).

fof(f5129,plain,
    ( spl10_780
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_780])])).

fof(f5261,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f780])).

fof(f5268,plain,
    ( spl10_782
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(avatar_split_clause,[],[f5260,f5063,f646,f5136])).

fof(f5136,plain,
    ( spl10_782
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_782])])).

fof(f5260,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_118
    | ~ spl10_764 ),
    inference(resolution,[],[f5064,f756])).

fof(f5253,plain,
    ( spl10_267
    | ~ spl10_276 ),
    inference(avatar_contradiction_clause,[],[f5252])).

fof(f5252,plain,
    ( $false
    | ~ spl10_267
    | ~ spl10_276 ),
    inference(subsumption_resolution,[],[f5243,f1429])).

fof(f5243,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_276 ),
    inference(resolution,[],[f1467,f270])).

fof(f1467,plain,
    ( sP9(u1_struct_0(sK4(sK0)))
    | ~ spl10_276 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1466,plain,
    ( spl10_276
  <=> sP9(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_276])])).

fof(f5229,plain,
    ( spl10_800
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | spl10_11
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(avatar_split_clause,[],[f5222,f2539,f2046,f2040,f2034,f871,f197,f190,f183,f176,f169,f162,f155,f148,f141,f5227])).

fof(f2539,plain,
    ( spl10_470
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_470])])).

fof(f5222,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(subsumption_resolution,[],[f5221,f198])).

fof(f5221,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(subsumption_resolution,[],[f5220,f191])).

fof(f5220,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_12
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(subsumption_resolution,[],[f5205,f184])).

fof(f5205,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_11
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(resolution,[],[f3018,f177])).

fof(f3018,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_470 ),
    inference(subsumption_resolution,[],[f3012,f2362])).

fof(f2362,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2361,f2035])).

fof(f2361,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2360,f2041])).

fof(f2360,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2359,f2047])).

fof(f2359,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2358,f163])).

fof(f2358,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2357,f170])).

fof(f2357,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2356,f149])).

fof(f2356,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2355,f156])).

fof(f2355,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2342,f142])).

fof(f2342,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_156 ),
    inference(duplicate_literal_removal,[],[f2341])).

fof(f2341,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_156 ),
    inference(superposition,[],[f115,f872])).

fof(f3012,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | k1_funct_1(sK2,sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0)) = sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0) )
    | ~ spl10_470 ),
    inference(resolution,[],[f2540,f83])).

fof(f2540,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) )
    | ~ spl10_470 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f5204,plain,
    ( spl10_798
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5148,f1275,f646,f5202])).

fof(f5202,plain,
    ( spl10_798
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_798])])).

fof(f1275,plain,
    ( spl10_232
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f5148,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))))))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f4487])).

fof(f1276,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_232 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f5197,plain,
    ( spl10_796
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5147,f1275,f646,f5195])).

fof(f5195,plain,
    ( spl10_796
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_796])])).

fof(f5147,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f4138])).

fof(f5190,plain,
    ( spl10_794
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5146,f1275,f646,f5188])).

fof(f5188,plain,
    ( spl10_794
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_794])])).

fof(f5146,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f3631])).

fof(f5183,plain,
    ( spl10_792
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5145,f1275,f646,f5181])).

fof(f5181,plain,
    ( spl10_792
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_792])])).

fof(f5145,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f2990])).

fof(f5176,plain,
    ( spl10_790
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5144,f1275,f646,f5174])).

fof(f5174,plain,
    ( spl10_790
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_790])])).

fof(f5144,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f1002])).

fof(f5169,plain,
    ( spl10_788
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5143,f1275,f646,f5167])).

fof(f5167,plain,
    ( spl10_788
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_788])])).

fof(f5143,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f888])).

fof(f5162,plain,
    ( spl10_786
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5142,f1275,f646,f5160])).

fof(f5160,plain,
    ( spl10_786
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_786])])).

fof(f5142,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(sK2)))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f780])).

fof(f5155,plain,
    ( spl10_784
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(avatar_split_clause,[],[f5141,f1275,f646,f5153])).

fof(f5153,plain,
    ( spl10_784
  <=> k1_zfmisc_1(sK2) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_784])])).

fof(f5141,plain,
    ( k1_zfmisc_1(sK2) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_232 ),
    inference(resolution,[],[f1276,f756])).

fof(f5138,plain,
    ( spl10_782
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5080,f1431,f646,f5136])).

fof(f1431,plain,
    ( spl10_266
  <=> v1_xboole_0(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f5080,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f780])).

fof(f1432,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_266 ),
    inference(avatar_component_clause,[],[f1431])).

fof(f5131,plain,
    ( spl10_780
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5081,f1431,f646,f5129])).

fof(f5081,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f888])).

fof(f5124,plain,
    ( spl10_778
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5082,f1431,f646,f5122])).

fof(f5082,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f1002])).

fof(f5117,plain,
    ( spl10_776
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5083,f1431,f646,f5115])).

fof(f5083,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f2990])).

fof(f5110,plain,
    ( spl10_774
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5084,f1431,f646,f5108])).

fof(f5084,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f3631])).

fof(f5103,plain,
    ( spl10_772
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5085,f1431,f646,f5101])).

fof(f5085,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f4138])).

fof(f5096,plain,
    ( spl10_770
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5086,f1431,f646,f5094])).

fof(f5086,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))))))))))))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f4487])).

fof(f5089,plain,
    ( spl10_182
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(avatar_split_clause,[],[f5079,f1431,f646,f1035])).

fof(f1035,plain,
    ( spl10_182
  <=> u1_struct_0(sK4(sK0)) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f5079,plain,
    ( u1_struct_0(sK4(sK0)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_266 ),
    inference(resolution,[],[f1432,f756])).

fof(f5088,plain,
    ( ~ spl10_118
    | spl10_183
    | ~ spl10_266 ),
    inference(avatar_contradiction_clause,[],[f5087])).

fof(f5087,plain,
    ( $false
    | ~ spl10_118
    | ~ spl10_183
    | ~ spl10_266 ),
    inference(subsumption_resolution,[],[f5079,f1033])).

fof(f1033,plain,
    ( u1_struct_0(sK4(sK0)) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_183 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl10_183
  <=> u1_struct_0(sK4(sK0)) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_183])])).

fof(f5075,plain,
    ( spl10_768
    | spl10_266
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f3421,f2681,f2670,f2627,f1431,f5073])).

fof(f3421,plain,
    ( ! [X6] :
        ( v1_xboole_0(u1_struct_0(sK4(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) )
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f3420,f2682])).

fof(f3420,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK4(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) )
    | ~ spl10_482
    | ~ spl10_492 ),
    inference(subsumption_resolution,[],[f3406,f2628])).

fof(f3406,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK4(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) )
    | ~ spl10_492 ),
    inference(resolution,[],[f125,f2671])).

fof(f5071,plain,
    ( spl10_764
    | spl10_766
    | spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f5048,f2681,f2670,f2627,f1428,f5069,f5063])).

fof(f5048,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))))
    | ~ spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(resolution,[],[f3422,f401])).

fof(f3422,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK4(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),X6) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X6) )
    | ~ spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f3421,f1429])).

fof(f5058,plain,
    ( spl10_762
    | spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f5047,f2681,f2670,f2627,f1428,f5056])).

fof(f5047,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = k3_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),sK3(u1_struct_0(sK4(sK0))))
    | ~ spl10_267
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(resolution,[],[f3422,f107])).

fof(f5012,plain,
    ( spl10_758
    | ~ spl10_761
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5002,f646,f5008,f4963])).

fof(f4963,plain,
    ( spl10_758
  <=> ! [X2] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))))))
        | k1_funct_1(k6_relat_1(X2),sK3(X2)) = sK3(X2)
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2))))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_758])])).

fof(f5008,plain,
    ( spl10_761
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_761])])).

fof(f5002,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),sK3(sK3(k1_zfmisc_1(sK2))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))))))
        | k1_funct_1(k6_relat_1(X2),sK3(X2)) = sK3(X2) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4939,f3629])).

fof(f4939,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3(k1_zfmisc_1(X4)),sK3(sK3(k1_zfmisc_1(sK2))))
        | k1_funct_1(k6_relat_1(X4),sK3(X4)) = sK3(X4)
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X4))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f4114,f106])).

fof(f4114,plain,
    ( ! [X5] :
        ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(X5)))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X5)))))
        | k1_funct_1(k6_relat_1(X5),sK3(X5)) = sK3(X5) )
    | ~ spl10_118 ),
    inference(superposition,[],[f547,f1000])).

fof(f5011,plain,
    ( spl10_756
    | ~ spl10_761
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5001,f646,f5008,f4959])).

fof(f4959,plain,
    ( spl10_756
  <=> ! [X1] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))))))
        | k1_funct_1(k6_relat_1(X1),sK3(X1)) = sK3(X1)
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_756])])).

fof(f5001,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),sK3(sK3(k1_zfmisc_1(sK2))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))))))
        | k1_funct_1(k6_relat_1(X1),sK3(X1)) = sK3(X1) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4939,f2994])).

fof(f2994,plain,
    ( ! [X0] :
        ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0))))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(resolution,[],[f1002,f445])).

fof(f5010,plain,
    ( spl10_752
    | ~ spl10_761
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f5000,f646,f5008,f4949])).

fof(f4949,plain,
    ( spl10_752
  <=> ! [X0] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0)
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(X0))),sK3(sK3(k1_zfmisc_1(X0)))) = sK3(sK3(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_752])])).

fof(f5000,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),sK3(sK3(k1_zfmisc_1(sK2))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(X0))),sK3(sK3(k1_zfmisc_1(X0)))) = sK3(sK3(k1_zfmisc_1(X0)))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))))))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4939,f1000])).

fof(f4965,plain,
    ( spl10_758
    | spl10_754
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f4946,f646,f4955,f4963])).

fof(f4955,plain,
    ( spl10_754
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_754])])).

fof(f4946,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2)))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2))))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X2)))))))
        | k1_funct_1(k6_relat_1(X2),sK3(X2)) = sK3(X2) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4114,f3629])).

fof(f4961,plain,
    ( spl10_756
    | spl10_754
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f4945,f646,f4955,f4959])).

fof(f4945,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2)))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1))))),sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))) = sK3(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))
        | k1_funct_1(k6_relat_1(X1),sK3(X1)) = sK3(X1) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4114,f2994])).

fof(f4957,plain,
    ( spl10_752
    | spl10_754
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f4944,f646,f4955,f4949])).

fof(f4944,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2)))
        | v1_xboole_0(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X0)))))))
        | k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(X0))),sK3(sK3(k1_zfmisc_1(X0)))) = sK3(sK3(k1_zfmisc_1(X0)))
        | k1_funct_1(k6_relat_1(X0),sK3(X0)) = sK3(X0) )
    | ~ spl10_118 ),
    inference(superposition,[],[f4114,f1000])).

fof(f4920,plain,
    ( ~ spl10_751
    | ~ spl10_748 ),
    inference(avatar_split_clause,[],[f4910,f4906,f4918])).

fof(f4918,plain,
    ( spl10_751
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK3(k4_tmap_1(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_751])])).

fof(f4906,plain,
    ( spl10_748
  <=> r2_hidden(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_748])])).

fof(f4910,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK3(k4_tmap_1(sK0,sK4(sK0))))
    | ~ spl10_748 ),
    inference(resolution,[],[f4907,f106])).

fof(f4907,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_748 ),
    inference(avatar_component_clause,[],[f4906])).

fof(f4908,plain,
    ( spl10_748
    | spl10_503
    | ~ spl10_742 ),
    inference(avatar_split_clause,[],[f4901,f4873,f2748,f4906])).

fof(f2748,plain,
    ( spl10_503
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_503])])).

fof(f4873,plain,
    ( spl10_742
  <=> m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_742])])).

fof(f4901,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_503
    | ~ spl10_742 ),
    inference(subsumption_resolution,[],[f4900,f2749])).

fof(f2749,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_503 ),
    inference(avatar_component_clause,[],[f2748])).

fof(f4900,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_742 ),
    inference(resolution,[],[f4874,f104])).

fof(f4874,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_742 ),
    inference(avatar_component_clause,[],[f4873])).

fof(f4896,plain,
    ( ~ spl10_747
    | ~ spl10_744 ),
    inference(avatar_split_clause,[],[f4886,f4882,f4894])).

fof(f4894,plain,
    ( spl10_747
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_747])])).

fof(f4882,plain,
    ( spl10_744
  <=> r2_hidden(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_744])])).

fof(f4886,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3(k4_tmap_1(sK0,sK1)))
    | ~ spl10_744 ),
    inference(resolution,[],[f4883,f106])).

fof(f4883,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_744 ),
    inference(avatar_component_clause,[],[f4882])).

fof(f4884,plain,
    ( spl10_744
    | spl10_41
    | ~ spl10_740 ),
    inference(avatar_split_clause,[],[f4877,f4863,f295,f4882])).

fof(f295,plain,
    ( spl10_41
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f4863,plain,
    ( spl10_740
  <=> m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_740])])).

fof(f4877,plain,
    ( r2_hidden(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_41
    | ~ spl10_740 ),
    inference(subsumption_resolution,[],[f4876,f296])).

fof(f296,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f295])).

fof(f4876,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | r2_hidden(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_740 ),
    inference(resolution,[],[f4864,f104])).

fof(f4864,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_740 ),
    inference(avatar_component_clause,[],[f4863])).

fof(f4875,plain,
    ( spl10_742
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_480
    | spl10_665 ),
    inference(avatar_split_clause,[],[f4868,f3803,f2618,f2046,f2040,f2034,f1936,f220,f4873])).

fof(f1936,plain,
    ( spl10_378
  <=> k4_tmap_1(sK0,sK4(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_378])])).

fof(f2618,plain,
    ( spl10_480
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_480])])).

fof(f3803,plain,
    ( spl10_665
  <=> ~ v1_xboole_0(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_665])])).

fof(f4868,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_480
    | ~ spl10_665 ),
    inference(subsumption_resolution,[],[f4867,f3804])).

fof(f3804,plain,
    ( ~ v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_665 ),
    inference(avatar_component_clause,[],[f3803])).

fof(f4867,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_480 ),
    inference(forward_demodulation,[],[f4866,f1937])).

fof(f1937,plain,
    ( k4_tmap_1(sK0,sK4(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0))
    | ~ spl10_378 ),
    inference(avatar_component_clause,[],[f1936])).

fof(f4866,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | v1_xboole_0(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_480 ),
    inference(subsumption_resolution,[],[f4855,f2619])).

fof(f2619,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl10_480 ),
    inference(avatar_component_clause,[],[f2618])).

fof(f4855,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK4(sK0))),k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ l1_struct_0(sK4(sK0))
    | v1_xboole_0(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0)))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(superposition,[],[f3796,f1937])).

fof(f3796,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))
        | ~ l1_struct_0(X0)
        | v1_xboole_0(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)) )
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(resolution,[],[f3772,f251])).

fof(f3772,plain,
    ( ! [X14,X15] :
        ( ~ r2_hidden(X15,k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X14))
        | ~ l1_struct_0(X14)
        | m1_subset_1(X15,k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK0))) )
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3771,f221])).

fof(f3771,plain,
    ( ! [X14,X15] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X14)
        | ~ r2_hidden(X15,k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X14))
        | m1_subset_1(X15,k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK0))) )
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3770,f2041])).

fof(f3770,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X14)
        | ~ r2_hidden(X15,k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X14))
        | m1_subset_1(X15,k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK0))) )
    | ~ spl10_394
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3753,f2047])).

fof(f3753,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X14)
        | ~ r2_hidden(X15,k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X14))
        | m1_subset_1(X15,k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK0))) )
    | ~ spl10_394 ),
    inference(duplicate_literal_removal,[],[f3746])).

fof(f3746,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X14)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(X15,k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X14))
        | m1_subset_1(X15,k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(sK0))) )
    | ~ spl10_394 ),
    inference(resolution,[],[f2141,f2035])).

fof(f2141,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X33),u1_struct_0(X31))
      | ~ l1_struct_0(X31)
      | ~ l1_struct_0(X34)
      | ~ l1_struct_0(X33)
      | ~ r2_hidden(X35,k2_tmap_1(X33,X31,X32,X34))
      | m1_subset_1(X35,k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X31))) ) ),
    inference(resolution,[],[f114,f102])).

fof(f4865,plain,
    ( spl10_740
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | spl10_595 ),
    inference(avatar_split_clause,[],[f4858,f3293,f2046,f2040,f2034,f871,f246,f220,f4863])).

fof(f3293,plain,
    ( spl10_595
  <=> ~ v1_xboole_0(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_595])])).

fof(f4858,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_595 ),
    inference(subsumption_resolution,[],[f4857,f3294])).

fof(f3294,plain,
    ( ~ v1_xboole_0(k4_tmap_1(sK0,sK1))
    | ~ spl10_595 ),
    inference(avatar_component_clause,[],[f3293])).

fof(f4857,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK1))
    | m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(forward_demodulation,[],[f4856,f872])).

fof(f4856,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_xboole_0(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f4854,f247])).

fof(f4854,plain,
    ( m1_subset_1(sK3(k4_tmap_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v1_xboole_0(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1))
    | ~ spl10_22
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(superposition,[],[f3796,f872])).

fof(f4687,plain,
    ( spl10_738
    | ~ spl10_650
    | ~ spl10_726 ),
    inference(avatar_split_clause,[],[f4680,f4630,f3696,f4685])).

fof(f4685,plain,
    ( spl10_738
  <=> k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_738])])).

fof(f3696,plain,
    ( spl10_650
  <=> k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_650])])).

fof(f4630,plain,
    ( spl10_726
  <=> k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_726])])).

fof(f4680,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_650
    | ~ spl10_726 ),
    inference(backward_demodulation,[],[f4631,f3697])).

fof(f3697,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl10_650 ),
    inference(avatar_component_clause,[],[f3696])).

fof(f4631,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_726 ),
    inference(avatar_component_clause,[],[f4630])).

fof(f4676,plain,
    ( ~ spl10_737
    | ~ spl10_732 ),
    inference(avatar_split_clause,[],[f4658,f4654,f4674])).

fof(f4674,plain,
    ( spl10_737
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_737])])).

fof(f4654,plain,
    ( spl10_732
  <=> r2_hidden(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_732])])).

fof(f4658,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl10_732 ),
    inference(resolution,[],[f4655,f106])).

fof(f4655,plain,
    ( r2_hidden(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ spl10_732 ),
    inference(avatar_component_clause,[],[f4654])).

fof(f4669,plain,
    ( spl10_734
    | ~ spl10_52
    | ~ spl10_732 ),
    inference(avatar_split_clause,[],[f4662,f4654,f345,f4667])).

fof(f4667,plain,
    ( spl10_734
  <=> k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_734])])).

fof(f4662,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl10_52
    | ~ spl10_732 ),
    inference(forward_demodulation,[],[f4657,f346])).

fof(f4657,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl10_732 ),
    inference(resolution,[],[f4655,f128])).

fof(f4656,plain,
    ( spl10_732
    | spl10_209
    | ~ spl10_722 ),
    inference(avatar_split_clause,[],[f4649,f4576,f1151,f4654])).

fof(f4576,plain,
    ( spl10_722
  <=> m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_722])])).

fof(f4649,plain,
    ( r2_hidden(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_722 ),
    inference(subsumption_resolution,[],[f4641,f1152])).

fof(f4641,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ spl10_722 ),
    inference(resolution,[],[f4577,f104])).

fof(f4577,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ spl10_722 ),
    inference(avatar_component_clause,[],[f4576])).

fof(f4648,plain,
    ( spl10_730
    | ~ spl10_632
    | ~ spl10_722 ),
    inference(avatar_split_clause,[],[f4640,f4576,f3503,f4646])).

fof(f4646,plain,
    ( spl10_730
  <=> k1_funct_1(k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_730])])).

fof(f4640,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))
    | ~ spl10_632
    | ~ spl10_722 ),
    inference(resolution,[],[f4577,f3504])).

fof(f4639,plain,
    ( ~ spl10_729
    | ~ spl10_724 ),
    inference(avatar_split_clause,[],[f4621,f4589,f4637])).

fof(f4637,plain,
    ( spl10_729
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_729])])).

fof(f4589,plain,
    ( spl10_724
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_724])])).

fof(f4621,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl10_724 ),
    inference(resolution,[],[f4590,f106])).

fof(f4590,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_724 ),
    inference(avatar_component_clause,[],[f4589])).

fof(f4632,plain,
    ( spl10_726
    | ~ spl10_52
    | ~ spl10_724 ),
    inference(avatar_split_clause,[],[f4625,f4589,f345,f4630])).

fof(f4625,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_52
    | ~ spl10_724 ),
    inference(forward_demodulation,[],[f4620,f346])).

fof(f4620,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK0)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_724 ),
    inference(resolution,[],[f4590,f128])).

fof(f4591,plain,
    ( spl10_724
    | spl10_209
    | ~ spl10_720 ),
    inference(avatar_split_clause,[],[f4584,f4567,f1151,f4589])).

fof(f4567,plain,
    ( spl10_720
  <=> m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_720])])).

fof(f4584,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_720 ),
    inference(subsumption_resolution,[],[f4583,f1152])).

fof(f4583,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_720 ),
    inference(resolution,[],[f4568,f104])).

fof(f4568,plain,
    ( m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_720 ),
    inference(avatar_component_clause,[],[f4567])).

fof(f4581,plain,
    ( spl10_649
    | spl10_721 ),
    inference(avatar_contradiction_clause,[],[f4580])).

fof(f4580,plain,
    ( $false
    | ~ spl10_649
    | ~ spl10_721 ),
    inference(subsumption_resolution,[],[f4579,f3688])).

fof(f3688,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_649 ),
    inference(avatar_component_clause,[],[f3687])).

fof(f3687,plain,
    ( spl10_649
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_649])])).

fof(f4579,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_721 ),
    inference(resolution,[],[f4571,f401])).

fof(f4571,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_721 ),
    inference(avatar_component_clause,[],[f4570])).

fof(f4570,plain,
    ( spl10_721
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_721])])).

fof(f4578,plain,
    ( ~ spl10_721
    | spl10_722
    | spl10_209
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_650 ),
    inference(avatar_split_clause,[],[f4565,f3696,f2046,f2040,f2034,f1151,f4576,f4570])).

fof(f4565,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_650 ),
    inference(subsumption_resolution,[],[f4564,f1152])).

fof(f4564,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_650 ),
    inference(subsumption_resolution,[],[f4563,f2035])).

fof(f4563,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_396
    | ~ spl10_398
    | ~ spl10_650 ),
    inference(subsumption_resolution,[],[f4562,f2041])).

fof(f4562,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_398
    | ~ spl10_650 ),
    inference(subsumption_resolution,[],[f4561,f2047])).

fof(f4561,plain,
    ( m1_subset_1(k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_650 ),
    inference(superposition,[],[f126,f3697])).

fof(f4386,plain,
    ( ~ spl10_719
    | ~ spl10_714 ),
    inference(avatar_split_clause,[],[f4368,f4364,f4384])).

fof(f4384,plain,
    ( spl10_719
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_719])])).

fof(f4364,plain,
    ( spl10_714
  <=> r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_714])])).

fof(f4368,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_714 ),
    inference(resolution,[],[f4365,f106])).

fof(f4365,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_714 ),
    inference(avatar_component_clause,[],[f4364])).

fof(f4379,plain,
    ( spl10_716
    | ~ spl10_52
    | ~ spl10_714 ),
    inference(avatar_split_clause,[],[f4372,f4364,f345,f4377])).

fof(f4372,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_52
    | ~ spl10_714 ),
    inference(forward_demodulation,[],[f4367,f346])).

fof(f4367,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_714 ),
    inference(resolution,[],[f4365,f128])).

fof(f4366,plain,
    ( spl10_714
    | spl10_209
    | ~ spl10_710 ),
    inference(avatar_split_clause,[],[f4359,f4347,f1151,f4364])).

fof(f4359,plain,
    ( r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_710 ),
    inference(subsumption_resolution,[],[f4351,f1152])).

fof(f4351,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_710 ),
    inference(resolution,[],[f4348,f104])).

fof(f4358,plain,
    ( spl10_712
    | ~ spl10_632
    | ~ spl10_710 ),
    inference(avatar_split_clause,[],[f4350,f4347,f3503,f4356])).

fof(f4356,plain,
    ( spl10_712
  <=> k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_712])])).

fof(f4350,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))))
    | ~ spl10_632
    | ~ spl10_710 ),
    inference(resolution,[],[f4348,f3504])).

fof(f4349,plain,
    ( spl10_710
    | spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(avatar_split_clause,[],[f4342,f4208,f2194,f2169,f2055,f285,f4347])).

fof(f4208,plain,
    ( spl10_688
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_688])])).

fof(f4342,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(subsumption_resolution,[],[f4341,f286])).

fof(f4341,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(subsumption_resolution,[],[f4340,f107])).

fof(f4340,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(subsumption_resolution,[],[f4339,f2170])).

fof(f4339,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_400
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(subsumption_resolution,[],[f4338,f2056])).

fof(f4338,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_420
    | ~ spl10_688 ),
    inference(subsumption_resolution,[],[f4337,f2195])).

fof(f4337,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_688 ),
    inference(superposition,[],[f126,f4209])).

fof(f4209,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))
    | ~ spl10_688 ),
    inference(avatar_component_clause,[],[f4208])).

fof(f4328,plain,
    ( ~ spl10_709
    | ~ spl10_704 ),
    inference(avatar_split_clause,[],[f4310,f4306,f4326])).

fof(f4306,plain,
    ( spl10_704
  <=> r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_704])])).

fof(f4310,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_704 ),
    inference(resolution,[],[f4307,f106])).

fof(f4307,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_704 ),
    inference(avatar_component_clause,[],[f4306])).

fof(f4321,plain,
    ( spl10_706
    | ~ spl10_52
    | ~ spl10_704 ),
    inference(avatar_split_clause,[],[f4314,f4306,f345,f4319])).

fof(f4314,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_52
    | ~ spl10_704 ),
    inference(forward_demodulation,[],[f4309,f346])).

fof(f4309,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_704 ),
    inference(resolution,[],[f4307,f128])).

fof(f4308,plain,
    ( spl10_704
    | spl10_209
    | ~ spl10_694 ),
    inference(avatar_split_clause,[],[f4301,f4234,f1151,f4306])).

fof(f4301,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_694 ),
    inference(subsumption_resolution,[],[f4293,f1152])).

fof(f4293,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl10_694 ),
    inference(resolution,[],[f4235,f104])).

fof(f4300,plain,
    ( spl10_702
    | ~ spl10_632
    | ~ spl10_694 ),
    inference(avatar_split_clause,[],[f4292,f4234,f3503,f4298])).

fof(f4298,plain,
    ( spl10_702
  <=> k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_702])])).

fof(f4292,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))))
    | ~ spl10_632
    | ~ spl10_694 ),
    inference(resolution,[],[f4235,f3504])).

fof(f4279,plain,
    ( ~ spl10_701
    | ~ spl10_696 ),
    inference(avatar_split_clause,[],[f4261,f4256,f4277])).

fof(f4256,plain,
    ( spl10_696
  <=> r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_696])])).

fof(f4261,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_696 ),
    inference(resolution,[],[f4257,f106])).

fof(f4257,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_696 ),
    inference(avatar_component_clause,[],[f4256])).

fof(f4272,plain,
    ( spl10_698
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(avatar_split_clause,[],[f4265,f4256,f352,f4270])).

fof(f4265,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_54
    | ~ spl10_696 ),
    inference(forward_demodulation,[],[f4260,f353])).

fof(f4260,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK1)),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_696 ),
    inference(resolution,[],[f4257,f128])).

fof(f4258,plain,
    ( spl10_696
    | spl10_39
    | ~ spl10_692 ),
    inference(avatar_split_clause,[],[f4251,f4225,f285,f4256])).

fof(f4251,plain,
    ( r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_39
    | ~ spl10_692 ),
    inference(subsumption_resolution,[],[f4249,f286])).

fof(f4249,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_692 ),
    inference(resolution,[],[f4226,f104])).

fof(f4250,plain,
    ( spl10_690
    | spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_692 ),
    inference(avatar_split_clause,[],[f4247,f4225,f2194,f2169,f2055,f285,f4216])).

fof(f4247,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420
    | ~ spl10_692 ),
    inference(resolution,[],[f4226,f3419])).

fof(f4246,plain,
    ( spl10_115
    | spl10_693 ),
    inference(avatar_contradiction_clause,[],[f4245])).

fof(f4245,plain,
    ( $false
    | ~ spl10_115
    | ~ spl10_693 ),
    inference(subsumption_resolution,[],[f4244,f631])).

fof(f631,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_115 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl10_115
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_115])])).

fof(f4244,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_693 ),
    inference(resolution,[],[f4229,f401])).

fof(f4236,plain,
    ( ~ spl10_693
    | spl10_694
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39
    | ~ spl10_620 ),
    inference(avatar_split_clause,[],[f4223,f3449,f285,f197,f190,f183,f4234,f4228])).

fof(f4223,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39
    | ~ spl10_620 ),
    inference(subsumption_resolution,[],[f4222,f286])).

fof(f4222,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_620 ),
    inference(subsumption_resolution,[],[f4221,f184])).

fof(f4221,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_620 ),
    inference(subsumption_resolution,[],[f4220,f191])).

fof(f4220,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16
    | ~ spl10_620 ),
    inference(subsumption_resolution,[],[f4219,f198])).

fof(f4219,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_620 ),
    inference(superposition,[],[f126,f3450])).

fof(f3450,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_620 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f4218,plain,
    ( spl10_690
    | spl10_39
    | spl10_115
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f4211,f2194,f2169,f2055,f630,f285,f4216])).

fof(f4211,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_39
    | ~ spl10_115
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f4201,f631])).

fof(f4210,plain,
    ( spl10_688
    | spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f4200,f2194,f2169,f2055,f285,f4208])).

fof(f4200,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK3(u1_struct_0(sK1)))
    | ~ spl10_39
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(resolution,[],[f3419,f107])).

fof(f4056,plain,
    ( spl10_670
    | spl10_669
    | ~ spl10_672 ),
    inference(avatar_split_clause,[],[f4055,f3829,f3816,f3825])).

fof(f3825,plain,
    ( spl10_670
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_670])])).

fof(f3816,plain,
    ( spl10_669
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_669])])).

fof(f3829,plain,
    ( spl10_672
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_672])])).

fof(f4055,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | ~ spl10_669
    | ~ spl10_672 ),
    inference(subsumption_resolution,[],[f4052,f3817])).

fof(f3817,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | ~ spl10_669 ),
    inference(avatar_component_clause,[],[f3816])).

fof(f4052,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | ~ spl10_672 ),
    inference(resolution,[],[f3961,f547])).

fof(f3961,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0)))
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_672 ),
    inference(resolution,[],[f3830,f128])).

fof(f3830,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0))) )
    | ~ spl10_672 ),
    inference(avatar_component_clause,[],[f3829])).

fof(f4054,plain,
    ( spl10_666
    | spl10_665
    | ~ spl10_672 ),
    inference(avatar_split_clause,[],[f4053,f3829,f3803,f3812])).

fof(f3812,plain,
    ( spl10_666
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_666])])).

fof(f4053,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_665
    | ~ spl10_672 ),
    inference(subsumption_resolution,[],[f4051,f3804])).

fof(f4051,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0)))
    | v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_672 ),
    inference(resolution,[],[f3961,f251])).

fof(f4050,plain,
    ( spl10_636
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | ~ spl10_156
    | spl10_209
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f4049,f2046,f2040,f2034,f1151,f871,f169,f162,f155,f148,f141,f3511])).

fof(f3511,plain,
    ( spl10_636
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_636])])).

fof(f4049,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_209
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f4048,f1152])).

fof(f4048,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f4047,f2035])).

fof(f4047,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f4046,f2041])).

fof(f4046,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f4045,f2047])).

fof(f4045,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f4044,f163])).

fof(f4044,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f4043,f170])).

fof(f4043,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f4042,f142])).

fof(f4042,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f4041,f149])).

fof(f4041,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f3996,f156])).

fof(f3996,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl10_156 ),
    inference(duplicate_literal_removal,[],[f3993])).

fof(f3993,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_156 ),
    inference(superposition,[],[f2340,f872])).

fof(f2340,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK6(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f115,f104])).

fof(f3938,plain,
    ( spl10_508
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3937,f2748,f2769])).

fof(f2769,plain,
    ( spl10_508
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_508])])).

fof(f3937,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_503 ),
    inference(resolution,[],[f2749,f445])).

fof(f3936,plain,
    ( spl10_686
    | spl10_669 ),
    inference(avatar_split_clause,[],[f3929,f3816,f3934])).

fof(f3934,plain,
    ( spl10_686
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_686])])).

fof(f3929,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | ~ spl10_669 ),
    inference(resolution,[],[f3817,f445])).

fof(f3904,plain,
    ( spl10_674
    | spl10_665 ),
    inference(avatar_split_clause,[],[f3903,f3803,f3846])).

fof(f3846,plain,
    ( spl10_674
  <=> k1_funct_1(k6_relat_1(k4_tmap_1(sK0,sK4(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_674])])).

fof(f3903,plain,
    ( k1_funct_1(k6_relat_1(k4_tmap_1(sK0,sK4(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_665 ),
    inference(resolution,[],[f3804,f445])).

fof(f3902,plain,
    ( spl10_676
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(avatar_split_clause,[],[f3891,f3806,f646,f3859])).

fof(f3859,plain,
    ( spl10_676
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_676])])).

fof(f3806,plain,
    ( spl10_664
  <=> v1_xboole_0(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_664])])).

fof(f3891,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))))))
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(resolution,[],[f3807,f2990])).

fof(f3807,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_664 ),
    inference(avatar_component_clause,[],[f3806])).

fof(f3901,plain,
    ( spl10_678
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(avatar_split_clause,[],[f3890,f3806,f646,f3866])).

fof(f3866,plain,
    ( spl10_678
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_678])])).

fof(f3890,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))))
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(resolution,[],[f3807,f1002])).

fof(f3900,plain,
    ( spl10_680
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(avatar_split_clause,[],[f3889,f3806,f646,f3873])).

fof(f3873,plain,
    ( spl10_680
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_680])])).

fof(f3889,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(resolution,[],[f3807,f888])).

fof(f3899,plain,
    ( spl10_682
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(avatar_split_clause,[],[f3888,f3806,f646,f3880])).

fof(f3880,plain,
    ( spl10_682
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_682])])).

fof(f3888,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(resolution,[],[f3807,f780])).

fof(f3898,plain,
    ( spl10_684
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(avatar_split_clause,[],[f3887,f3806,f646,f3896])).

fof(f3896,plain,
    ( spl10_684
  <=> k4_tmap_1(sK0,sK4(sK0)) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_684])])).

fof(f3887,plain,
    ( k4_tmap_1(sK0,sK4(sK0)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_664 ),
    inference(resolution,[],[f3807,f756])).

fof(f3884,plain,
    ( ~ spl10_500
    | spl10_665 ),
    inference(avatar_contradiction_clause,[],[f3883])).

fof(f3883,plain,
    ( $false
    | ~ spl10_500
    | ~ spl10_665 ),
    inference(subsumption_resolution,[],[f3854,f3804])).

fof(f3854,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_500 ),
    inference(resolution,[],[f2743,f270])).

fof(f2743,plain,
    ( sP9(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_500 ),
    inference(avatar_component_clause,[],[f2742])).

fof(f2742,plain,
    ( spl10_500
  <=> sP9(k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_500])])).

fof(f3882,plain,
    ( spl10_682
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(avatar_split_clause,[],[f3852,f2742,f646,f3880])).

fof(f3852,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(resolution,[],[f2743,f779])).

fof(f3875,plain,
    ( spl10_680
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(avatar_split_clause,[],[f3851,f2742,f646,f3873])).

fof(f3851,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(resolution,[],[f2743,f891])).

fof(f891,plain,
    ( ! [X1] :
        ( ~ sP9(X1)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f780,f612])).

fof(f3868,plain,
    ( spl10_678
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(avatar_split_clause,[],[f3850,f2742,f646,f3866])).

fof(f3850,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))))
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(resolution,[],[f2743,f1001])).

fof(f3861,plain,
    ( spl10_676
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(avatar_split_clause,[],[f3849,f2742,f646,f3859])).

fof(f3849,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))))))))
    | ~ spl10_118
    | ~ spl10_500 ),
    inference(resolution,[],[f2743,f2995])).

fof(f2995,plain,
    ( ! [X1] :
        ( ~ sP9(X1)
        | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(X1)))))))) )
    | ~ spl10_118 ),
    inference(resolution,[],[f1002,f612])).

fof(f3848,plain,
    ( spl10_674
    | spl10_665 ),
    inference(avatar_split_clause,[],[f3841,f3803,f3846])).

fof(f3841,plain,
    ( k1_funct_1(k6_relat_1(k4_tmap_1(sK0,sK4(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_665 ),
    inference(resolution,[],[f3804,f445])).

fof(f3831,plain,
    ( spl10_502
    | spl10_672
    | ~ spl10_492 ),
    inference(avatar_split_clause,[],[f3020,f2670,f3829,f2745])).

fof(f2745,plain,
    ( spl10_502
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_502])])).

fof(f3020,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) )
    | ~ spl10_492 ),
    inference(resolution,[],[f2710,f104])).

fof(f2710,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k4_tmap_1(sK0,sK4(sK0))) )
    | ~ spl10_492 ),
    inference(resolution,[],[f2671,f102])).

fof(f3827,plain,
    ( spl10_668
    | spl10_670
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3801,f2748,f2670,f3825,f3819])).

fof(f3819,plain,
    ( spl10_668
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_668])])).

fof(f3801,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK4(sK0)))))
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3159,f547])).

fof(f3159,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0)))
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f128])).

fof(f3021,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k4_tmap_1(sK0,sK4(sK0))) )
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(subsumption_resolution,[],[f3020,f2749])).

fof(f3814,plain,
    ( spl10_664
    | spl10_666
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3800,f2748,f2670,f3812,f3806])).

fof(f3800,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK4(sK0)))) = sK3(k4_tmap_1(sK0,sK4(sK0)))
    | v1_xboole_0(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3159,f251])).

fof(f3788,plain,
    ( spl10_662
    | spl10_649 ),
    inference(avatar_split_clause,[],[f3781,f3687,f3786])).

fof(f3786,plain,
    ( spl10_662
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_662])])).

fof(f3781,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_649 ),
    inference(resolution,[],[f3688,f445])).

fof(f3740,plain,
    ( spl10_660
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(avatar_split_clause,[],[f3705,f3690,f646,f3738])).

fof(f3738,plain,
    ( spl10_660
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_660])])).

fof(f3690,plain,
    ( spl10_648
  <=> v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_648])])).

fof(f3705,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))))))))
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(resolution,[],[f3691,f2990])).

fof(f3691,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_648 ),
    inference(avatar_component_clause,[],[f3690])).

fof(f3733,plain,
    ( spl10_658
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(avatar_split_clause,[],[f3704,f3690,f646,f3731])).

fof(f3731,plain,
    ( spl10_658
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_658])])).

fof(f3704,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))))))
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(resolution,[],[f3691,f1002])).

fof(f3726,plain,
    ( spl10_656
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(avatar_split_clause,[],[f3703,f3690,f646,f3724])).

fof(f3724,plain,
    ( spl10_656
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_656])])).

fof(f3703,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))))
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(resolution,[],[f3691,f888])).

fof(f3719,plain,
    ( spl10_654
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(avatar_split_clause,[],[f3702,f3690,f646,f3717])).

fof(f3717,plain,
    ( spl10_654
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_654])])).

fof(f3702,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(resolution,[],[f3691,f780])).

fof(f3712,plain,
    ( spl10_652
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(avatar_split_clause,[],[f3701,f3690,f646,f3710])).

fof(f3710,plain,
    ( spl10_652
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_652])])).

fof(f3701,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_118
    | ~ spl10_648 ),
    inference(resolution,[],[f3691,f756])).

fof(f3698,plain,
    ( spl10_648
    | spl10_650
    | ~ spl10_632 ),
    inference(avatar_split_clause,[],[f3667,f3503,f3696,f3690])).

fof(f3667,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0))))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK0)))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_632 ),
    inference(resolution,[],[f3504,f401])).

fof(f3685,plain,
    ( spl10_646
    | ~ spl10_180
    | ~ spl10_632 ),
    inference(avatar_split_clause,[],[f3678,f3503,f1028,f3683])).

fof(f3683,plain,
    ( spl10_646
  <=> k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_646])])).

fof(f1028,plain,
    ( spl10_180
  <=> k1_funct_1(k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f3678,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | ~ spl10_180
    | ~ spl10_632 ),
    inference(forward_demodulation,[],[f3666,f1029])).

fof(f1029,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | ~ spl10_180 ),
    inference(avatar_component_clause,[],[f1028])).

fof(f3666,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl10_632 ),
    inference(resolution,[],[f3504,f107])).

fof(f3677,plain,
    ( spl10_644
    | ~ spl10_622
    | ~ spl10_626
    | ~ spl10_632 ),
    inference(avatar_split_clause,[],[f3670,f3503,f3484,f3462,f3675])).

fof(f3675,plain,
    ( spl10_644
  <=> k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_644])])).

fof(f3462,plain,
    ( spl10_622
  <=> m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_622])])).

fof(f3484,plain,
    ( spl10_626
  <=> k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_626])])).

fof(f3670,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_622
    | ~ spl10_626
    | ~ spl10_632 ),
    inference(forward_demodulation,[],[f3664,f3485])).

fof(f3485,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_626 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3664,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1)))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_622
    | ~ spl10_632 ),
    inference(resolution,[],[f3504,f3463])).

fof(f3463,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_622 ),
    inference(avatar_component_clause,[],[f3462])).

fof(f3613,plain,
    ( spl10_642
    | spl10_534
    | ~ spl10_118
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f3606,f2245,f646,f2903,f3611])).

fof(f3611,plain,
    ( spl10_642
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_642])])).

fof(f2903,plain,
    ( spl10_534
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_534])])).

fof(f2245,plain,
    ( spl10_430
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_430])])).

fof(f3606,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))
    | ~ spl10_118
    | ~ spl10_430 ),
    inference(superposition,[],[f889,f2246])).

fof(f2246,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_430 ),
    inference(avatar_component_clause,[],[f2245])).

fof(f3593,plain,
    ( spl10_638
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f3592,f246,f220,f197,f190,f183,f3564])).

fof(f3564,plain,
    ( spl10_638
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_638])])).

fof(f3592,plain,
    ( ! [X21] :
        ( ~ l1_struct_0(X21)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X21)) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f3591,f247])).

fof(f3591,plain,
    ( ! [X21] :
        ( ~ l1_struct_0(X21)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X21)) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f3590,f221])).

fof(f3590,plain,
    ( ! [X21] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X21)) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3589,f191])).

fof(f3589,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X21)) )
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f3555,f198])).

fof(f3555,plain,
    ( ! [X21] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X21)) )
    | ~ spl10_12 ),
    inference(resolution,[],[f2159,f184])).

fof(f2159,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X23))))
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X23))
      | ~ l1_struct_0(X23)
      | ~ l1_struct_0(X26)
      | ~ l1_struct_0(X25)
      | ~ sP8(u1_struct_0(X23),u1_struct_0(X26)) ) ),
    inference(subsumption_resolution,[],[f2158,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f2158,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ l1_struct_0(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X23))))
      | ~ l1_struct_0(X26)
      | ~ l1_struct_0(X25)
      | ~ v1_funct_2(k2_tmap_1(X25,X23,X24,X26),u1_struct_0(X26),u1_struct_0(X23))
      | ~ sP8(u1_struct_0(X23),u1_struct_0(X26)) ) ),
    inference(subsumption_resolution,[],[f2139,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f2139,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ l1_struct_0(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X25),u1_struct_0(X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X23))))
      | ~ l1_struct_0(X26)
      | ~ l1_struct_0(X25)
      | ~ v1_funct_2(k2_tmap_1(X25,X23,X24,X26),u1_struct_0(X26),u1_struct_0(X23))
      | ~ v1_funct_1(k2_tmap_1(X25,X23,X24,X26))
      | ~ sP8(u1_struct_0(X23),u1_struct_0(X26)) ) ),
    inference(resolution,[],[f114,f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ sP8(X1,X0) ) ),
    inference(general_splitting,[],[f96,f132_D])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2)
      | sP8(X1,X0) ) ),
    inference(cnf_transformation,[],[f132_D])).

fof(f132_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_funct_1(X2)
          | ~ v1_funct_2(X2,X0,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_funct_2(X0,X1,X2,X2) )
    <=> ~ sP8(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',reflexivity_r2_funct_2)).

fof(f3588,plain,
    ( spl10_638
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f3587,f2046,f2040,f2034,f220,f3564])).

fof(f3587,plain,
    ( ! [X9] :
        ( ~ l1_struct_0(X9)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X9)) )
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3586,f221])).

fof(f3586,plain,
    ( ! [X9] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X9)) )
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3585,f2041])).

fof(f3585,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X9)) )
    | ~ spl10_394
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3559,f2047])).

fof(f3559,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X9)) )
    | ~ spl10_394 ),
    inference(duplicate_literal_removal,[],[f3552])).

fof(f3552,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X9)
        | ~ l1_struct_0(sK0)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X9)) )
    | ~ spl10_394 ),
    inference(resolution,[],[f2159,f2035])).

fof(f3582,plain,
    ( spl10_638
    | ~ spl10_22
    | ~ spl10_480
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f3581,f2681,f2670,f2627,f2618,f220,f3564])).

fof(f3581,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(X6)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X6)) )
    | ~ spl10_22
    | ~ spl10_480
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f3580,f2619])).

fof(f3580,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(X6)
        | ~ l1_struct_0(sK4(sK0))
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X6)) )
    | ~ spl10_22
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f3579,f221])).

fof(f3579,plain,
    ( ! [X6] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(sK4(sK0))
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X6)) )
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f3578,f2682])).

fof(f3578,plain,
    ( ! [X6] :
        ( ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(sK4(sK0))
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X6)) )
    | ~ spl10_482
    | ~ spl10_492 ),
    inference(subsumption_resolution,[],[f3550,f2628])).

fof(f3550,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(sK4(sK0))
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X6)) )
    | ~ spl10_492 ),
    inference(resolution,[],[f2159,f2671])).

fof(f3577,plain,
    ( spl10_638
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f3576,f2194,f2169,f2055,f246,f220,f3564])).

fof(f3576,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3575,f247])).

fof(f3575,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(X5)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_22
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3574,f221])).

fof(f3574,plain,
    ( ! [X5] :
        ( ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3573,f2056])).

fof(f3573,plain,
    ( ! [X5] :
        ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f3549,f2195])).

fof(f3549,plain,
    ( ! [X5] :
        ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(sK1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X5)) )
    | ~ spl10_414 ),
    inference(resolution,[],[f2159,f2170])).

fof(f3569,plain,
    ( spl10_638
    | spl10_640
    | ~ spl10_22
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f3562,f2245,f220,f3567,f3564])).

fof(f3567,plain,
    ( spl10_640
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2)))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_640])])).

fof(f3562,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(X1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X1))
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_22
    | ~ spl10_430 ),
    inference(subsumption_resolution,[],[f3561,f221])).

fof(f3561,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X1)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X1))
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_430 ),
    inference(duplicate_literal_removal,[],[f3547])).

fof(f3547,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK0)
        | ~ sP8(u1_struct_0(sK0),u1_struct_0(X1))
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_430 ),
    inference(resolution,[],[f2159,f2864])).

fof(f2864,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_430 ),
    inference(superposition,[],[f292,f2246])).

fof(f3546,plain,
    ( ~ spl10_629
    | ~ spl10_624 ),
    inference(avatar_split_clause,[],[f3540,f3471,f3491])).

fof(f3491,plain,
    ( spl10_629
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_629])])).

fof(f3471,plain,
    ( spl10_624
  <=> r2_hidden(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_624])])).

fof(f3540,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_624 ),
    inference(resolution,[],[f3472,f106])).

fof(f3472,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_624 ),
    inference(avatar_component_clause,[],[f3471])).

fof(f3545,plain,
    ( spl10_626
    | ~ spl10_52
    | ~ spl10_624 ),
    inference(avatar_split_clause,[],[f3544,f3471,f345,f3484])).

fof(f3544,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_52
    | ~ spl10_624 ),
    inference(forward_demodulation,[],[f3539,f346])).

fof(f3539,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_624 ),
    inference(resolution,[],[f3472,f128])).

fof(f3525,plain,
    ( ~ spl10_118
    | spl10_179
    | ~ spl10_208 ),
    inference(avatar_contradiction_clause,[],[f3524])).

fof(f3524,plain,
    ( $false
    | ~ spl10_118
    | ~ spl10_179
    | ~ spl10_208 ),
    inference(subsumption_resolution,[],[f3518,f1020])).

fof(f1020,plain,
    ( u1_struct_0(sK0) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_179 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1019,plain,
    ( spl10_179
  <=> u1_struct_0(sK0) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_179])])).

fof(f3518,plain,
    ( u1_struct_0(sK0) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_208 ),
    inference(resolution,[],[f1155,f756])).

fof(f1155,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_208 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1154,plain,
    ( spl10_208
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_208])])).

fof(f3523,plain,
    ( spl10_5
    | ~ spl10_22
    | ~ spl10_208 ),
    inference(avatar_contradiction_clause,[],[f3522])).

fof(f3522,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_208 ),
    inference(subsumption_resolution,[],[f3521,f156])).

fof(f3521,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_22
    | ~ spl10_208 ),
    inference(subsumption_resolution,[],[f3514,f221])).

fof(f3514,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_208 ),
    inference(resolution,[],[f1155,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',fc2_struct_0)).

fof(f3513,plain,
    ( spl10_208
    | spl10_636
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2988,f2046,f2040,f2034,f871,f169,f162,f155,f148,f141,f3511,f1154])).

fof(f2988,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK0)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(resolution,[],[f2362,f104])).

fof(f3509,plain,
    ( spl10_208
    | spl10_634
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f3403,f2245,f3507,f1154])).

fof(f3507,plain,
    ( spl10_634
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2)))
        | k1_funct_1(X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_634])])).

fof(f3403,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_funct_1(X0,X1) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X0,X1)
        | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_430 ),
    inference(resolution,[],[f125,f2864])).

fof(f3505,plain,
    ( spl10_632
    | spl10_208
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f3426,f2046,f2040,f2034,f1154,f3503])).

fof(f3426,plain,
    ( ! [X9] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_funct_1(k3_struct_0(sK0),X9) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X9) )
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3425,f2041])).

fof(f3425,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_funct_1(k3_struct_0(sK0),X9) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X9) )
    | ~ spl10_394
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f3408,f2047])).

fof(f3408,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_funct_1(k3_struct_0(sK0),X9) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X9) )
    | ~ spl10_394 ),
    inference(resolution,[],[f125,f2035])).

fof(f3501,plain,
    ( spl10_624
    | spl10_208
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f3465,f3462,f1154,f3471])).

fof(f3465,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_622 ),
    inference(resolution,[],[f3463,f104])).

fof(f3500,plain,
    ( ~ spl10_631
    | ~ spl10_624 ),
    inference(avatar_split_clause,[],[f3477,f3471,f3498])).

fof(f3498,plain,
    ( spl10_631
  <=> ~ sP9(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_631])])).

fof(f3477,plain,
    ( ~ sP9(u1_struct_0(sK0))
    | ~ spl10_624 ),
    inference(resolution,[],[f3472,f135])).

fof(f3493,plain,
    ( ~ spl10_629
    | ~ spl10_624 ),
    inference(avatar_split_clause,[],[f3475,f3471,f3491])).

fof(f3475,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_624 ),
    inference(resolution,[],[f3472,f106])).

fof(f3486,plain,
    ( spl10_626
    | ~ spl10_52
    | ~ spl10_624 ),
    inference(avatar_split_clause,[],[f3479,f3471,f345,f3484])).

fof(f3479,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_52
    | ~ spl10_624 ),
    inference(forward_demodulation,[],[f3474,f346])).

fof(f3474,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k1_funct_1(k6_relat_1(u1_struct_0(sK0)),k1_funct_1(sK2,sK3(u1_struct_0(sK1))))
    | ~ spl10_624 ),
    inference(resolution,[],[f3472,f128])).

fof(f3473,plain,
    ( spl10_624
    | spl10_209
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f3466,f3462,f1151,f3471])).

fof(f3466,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_209
    | ~ spl10_622 ),
    inference(subsumption_resolution,[],[f3465,f1152])).

fof(f3464,plain,
    ( spl10_622
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39
    | ~ spl10_618 ),
    inference(avatar_split_clause,[],[f3457,f3441,f285,f197,f190,f183,f3462])).

fof(f3441,plain,
    ( spl10_618
  <=> k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_618])])).

fof(f3457,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39
    | ~ spl10_618 ),
    inference(subsumption_resolution,[],[f3456,f286])).

fof(f3456,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_618 ),
    inference(subsumption_resolution,[],[f3455,f107])).

fof(f3455,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_618 ),
    inference(subsumption_resolution,[],[f3454,f184])).

fof(f3454,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_618 ),
    inference(subsumption_resolution,[],[f3453,f191])).

fof(f3453,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_16
    | ~ spl10_618 ),
    inference(subsumption_resolution,[],[f3452,f198])).

fof(f3452,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK3(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_618 ),
    inference(superposition,[],[f126,f3442])).

fof(f3442,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1)))
    | ~ spl10_618 ),
    inference(avatar_component_clause,[],[f3441])).

fof(f3451,plain,
    ( spl10_620
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39
    | spl10_115 ),
    inference(avatar_split_clause,[],[f3444,f630,f285,f197,f190,f183,f3449])).

fof(f3444,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39
    | ~ spl10_115 ),
    inference(subsumption_resolution,[],[f3435,f631])).

fof(f3443,plain,
    ( spl10_618
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | spl10_39 ),
    inference(avatar_split_clause,[],[f3434,f285,f197,f190,f183,f3441])).

fof(f3434,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(u1_struct_0(sK1)))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16
    | ~ spl10_39 ),
    inference(resolution,[],[f3432,f107])).

fof(f3402,plain,
    ( spl10_616
    | spl10_599 ),
    inference(avatar_split_clause,[],[f3388,f3306,f3400])).

fof(f3400,plain,
    ( spl10_616
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_616])])).

fof(f3306,plain,
    ( spl10_599
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_599])])).

fof(f3388,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | ~ spl10_599 ),
    inference(resolution,[],[f3307,f445])).

fof(f3307,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | ~ spl10_599 ),
    inference(avatar_component_clause,[],[f3306])).

fof(f3395,plain,
    ( ~ spl10_615
    | spl10_599 ),
    inference(avatar_split_clause,[],[f3386,f3306,f3393])).

fof(f3393,plain,
    ( spl10_615
  <=> ~ sP9(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_615])])).

fof(f3386,plain,
    ( ~ sP9(k4_tmap_1(sK0,sK1))
    | ~ spl10_599 ),
    inference(resolution,[],[f3307,f612])).

fof(f3385,plain,
    ( spl10_606
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(avatar_split_clause,[],[f3373,f3309,f646,f3352])).

fof(f3352,plain,
    ( spl10_606
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_606])])).

fof(f3309,plain,
    ( spl10_598
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_598])])).

fof(f3373,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(resolution,[],[f3310,f756])).

fof(f3310,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | ~ spl10_598 ),
    inference(avatar_component_clause,[],[f3309])).

fof(f3384,plain,
    ( spl10_604
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(avatar_split_clause,[],[f3372,f3309,f646,f3345])).

fof(f3345,plain,
    ( spl10_604
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_604])])).

fof(f3372,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(resolution,[],[f3310,f780])).

fof(f3383,plain,
    ( spl10_602
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(avatar_split_clause,[],[f3371,f3309,f646,f3338])).

fof(f3338,plain,
    ( spl10_602
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_602])])).

fof(f3371,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))))
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(resolution,[],[f3310,f888])).

fof(f3382,plain,
    ( spl10_612
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(avatar_split_clause,[],[f3370,f3309,f646,f3380])).

fof(f3380,plain,
    ( spl10_612
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_612])])).

fof(f3370,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))))))
    | ~ spl10_118
    | ~ spl10_598 ),
    inference(resolution,[],[f3310,f1002])).

fof(f3369,plain,
    ( spl10_610
    | spl10_595 ),
    inference(avatar_split_clause,[],[f3362,f3293,f3367])).

fof(f3367,plain,
    ( spl10_610
  <=> k1_funct_1(k6_relat_1(k4_tmap_1(sK0,sK1)),sK3(k4_tmap_1(sK0,sK1))) = sK3(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_610])])).

fof(f3362,plain,
    ( k1_funct_1(k6_relat_1(k4_tmap_1(sK0,sK1)),sK3(k4_tmap_1(sK0,sK1))) = sK3(k4_tmap_1(sK0,sK1))
    | ~ spl10_595 ),
    inference(resolution,[],[f3294,f445])).

fof(f3361,plain,
    ( spl10_608
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(avatar_split_clause,[],[f3331,f3296,f646,f3359])).

fof(f3359,plain,
    ( spl10_608
  <=> k4_tmap_1(sK0,sK1) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_608])])).

fof(f3296,plain,
    ( spl10_594
  <=> v1_xboole_0(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_594])])).

fof(f3331,plain,
    ( k4_tmap_1(sK0,sK1) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(resolution,[],[f3297,f756])).

fof(f3297,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK1))
    | ~ spl10_594 ),
    inference(avatar_component_clause,[],[f3296])).

fof(f3354,plain,
    ( spl10_606
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(avatar_split_clause,[],[f3330,f3296,f646,f3352])).

fof(f3330,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(resolution,[],[f3297,f780])).

fof(f3347,plain,
    ( spl10_604
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(avatar_split_clause,[],[f3329,f3296,f646,f3345])).

fof(f3329,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(resolution,[],[f3297,f888])).

fof(f3340,plain,
    ( spl10_602
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(avatar_split_clause,[],[f3328,f3296,f646,f3338])).

fof(f3328,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))))
    | ~ spl10_118
    | ~ spl10_594 ),
    inference(resolution,[],[f3297,f1002])).

fof(f3317,plain,
    ( spl10_598
    | spl10_600
    | spl10_41
    | ~ spl10_414 ),
    inference(avatar_split_clause,[],[f3291,f2169,f295,f3315,f3309])).

fof(f3315,plain,
    ( spl10_600
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_600])])).

fof(f3291,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) = sK3(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(resolution,[],[f2780,f547])).

fof(f2780,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(resolution,[],[f2703,f128])).

fof(f2703,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k4_tmap_1(sK0,sK1)) )
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(subsumption_resolution,[],[f2702,f296])).

fof(f2702,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_tmap_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) )
    | ~ spl10_414 ),
    inference(resolution,[],[f2284,f104])).

fof(f2284,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k4_tmap_1(sK0,sK1)) )
    | ~ spl10_414 ),
    inference(resolution,[],[f2170,f102])).

fof(f3304,plain,
    ( spl10_594
    | spl10_596
    | spl10_41
    | ~ spl10_414 ),
    inference(avatar_split_clause,[],[f3290,f2169,f295,f3302,f3296])).

fof(f3302,plain,
    ( spl10_596
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK1))) = sK3(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_596])])).

fof(f3290,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(k4_tmap_1(sK0,sK1))) = sK3(k4_tmap_1(sK0,sK1))
    | v1_xboole_0(k4_tmap_1(sK0,sK1))
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(resolution,[],[f2780,f251])).

fof(f3268,plain,
    ( ~ spl10_593
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3261,f2748,f2670,f3266])).

fof(f3266,plain,
    ( spl10_593
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_593])])).

fof(f3261,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(duplicate_literal_removal,[],[f3259])).

fof(f3259,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3160,f3021])).

fof(f3160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,k4_tmap_1(sK0,sK4(sK0))) )
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f106])).

fof(f3255,plain,
    ( spl10_554
    | spl10_553
    | ~ spl10_558 ),
    inference(avatar_split_clause,[],[f3254,f3057,f3040,f3049])).

fof(f3049,plain,
    ( spl10_554
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_554])])).

fof(f3040,plain,
    ( spl10_553
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_553])])).

fof(f3057,plain,
    ( spl10_558
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_struct_0(sK0))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_558])])).

fof(f3254,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_553
    | ~ spl10_558 ),
    inference(subsumption_resolution,[],[f3251,f3041])).

fof(f3041,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_553 ),
    inference(avatar_component_clause,[],[f3040])).

fof(f3251,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_558 ),
    inference(resolution,[],[f3145,f547])).

fof(f3145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_struct_0(sK0))
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_558 ),
    inference(resolution,[],[f3058,f128])).

fof(f3058,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_struct_0(sK0)) )
    | ~ spl10_558 ),
    inference(avatar_component_clause,[],[f3057])).

fof(f3253,plain,
    ( spl10_550
    | spl10_549
    | ~ spl10_558 ),
    inference(avatar_split_clause,[],[f3252,f3057,f3027,f3036])).

fof(f3036,plain,
    ( spl10_550
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_550])])).

fof(f3027,plain,
    ( spl10_549
  <=> ~ v1_xboole_0(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_549])])).

fof(f3252,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0))
    | ~ spl10_549
    | ~ spl10_558 ),
    inference(subsumption_resolution,[],[f3250,f3028])).

fof(f3028,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK0))
    | ~ spl10_549 ),
    inference(avatar_component_clause,[],[f3027])).

fof(f3250,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0))
    | v1_xboole_0(k3_struct_0(sK0))
    | ~ spl10_558 ),
    inference(resolution,[],[f3145,f251])).

fof(f3223,plain,
    ( ~ spl10_589
    | ~ spl10_591
    | spl10_413
    | ~ spl10_430
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3167,f2748,f2670,f2245,f2127,f3221,f3215])).

fof(f3215,plain,
    ( spl10_589
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_589])])).

fof(f3221,plain,
    ( spl10_591
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_591])])).

fof(f2127,plain,
    ( spl10_413
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_413])])).

fof(f3167,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k4_tmap_1(sK0,sK4(sK0)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_413
    | ~ spl10_430
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f2961])).

fof(f2961,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X1)
        | ~ r2_hidden(X1,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_413
    | ~ spl10_430 ),
    inference(resolution,[],[f2959,f106])).

fof(f2959,plain,
    ( ! [X11] :
        ( r2_hidden(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ r2_hidden(X11,sK3(k1_zfmisc_1(sK2))) )
    | ~ spl10_413
    | ~ spl10_430 ),
    inference(subsumption_resolution,[],[f2956,f2128])).

fof(f2128,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_413 ),
    inference(avatar_component_clause,[],[f2127])).

fof(f2956,plain,
    ( ! [X11] :
        ( ~ r2_hidden(X11,sK3(k1_zfmisc_1(sK2)))
        | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | r2_hidden(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | ~ spl10_430 ),
    inference(resolution,[],[f2864,f104])).

fof(f3210,plain,
    ( ~ spl10_585
    | ~ spl10_587
    | ~ spl10_492
    | spl10_503
    | ~ spl10_558 ),
    inference(avatar_split_clause,[],[f3166,f3057,f2748,f2670,f3208,f3202])).

fof(f3202,plain,
    ( spl10_585
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_585])])).

fof(f3208,plain,
    ( spl10_587
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_587])])).

fof(f3166,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl10_492
    | ~ spl10_503
    | ~ spl10_558 ),
    inference(resolution,[],[f3021,f3146])).

fof(f3146,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,k3_struct_0(sK0)) )
    | ~ spl10_558 ),
    inference(resolution,[],[f3058,f106])).

fof(f3197,plain,
    ( ~ spl10_583
    | ~ spl10_581
    | ~ spl10_42
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3165,f2748,f2670,f301,f3188,f3195])).

fof(f3195,plain,
    ( spl10_583
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_583])])).

fof(f3188,plain,
    ( spl10_581
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_581])])).

fof(f3165,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),sK2)
    | ~ spl10_42
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f994])).

fof(f994,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl10_42 ),
    inference(resolution,[],[f302,f106])).

fof(f3190,plain,
    ( ~ spl10_579
    | ~ spl10_581
    | spl10_41
    | ~ spl10_414
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3164,f2748,f2670,f2169,f295,f3188,f3182])).

fof(f3182,plain,
    ( spl10_579
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_579])])).

fof(f3164,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1))
    | ~ spl10_41
    | ~ spl10_414
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f2781])).

fof(f2781,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,k4_tmap_1(sK0,sK1)) )
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(resolution,[],[f2703,f106])).

fof(f3177,plain,
    ( ~ spl10_575
    | spl10_576
    | ~ spl10_492
    | spl10_503 ),
    inference(avatar_split_clause,[],[f3162,f2748,f2670,f3175,f3172])).

fof(f3172,plain,
    ( spl10_575
  <=> ~ sP9(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_575])])).

fof(f3175,plain,
    ( spl10_576
  <=> ! [X3] : ~ r2_hidden(X3,k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_576])])).

fof(f3162,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k4_tmap_1(sK0,sK4(sK0)))
        | ~ sP9(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) )
    | ~ spl10_492
    | ~ spl10_503 ),
    inference(resolution,[],[f3021,f135])).

fof(f3144,plain,
    ( spl10_416
    | spl10_409 ),
    inference(avatar_split_clause,[],[f3143,f2117,f2177])).

fof(f2177,plain,
    ( spl10_416
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_416])])).

fof(f2117,plain,
    ( spl10_409
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_409])])).

fof(f3143,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_409 ),
    inference(resolution,[],[f2118,f445])).

fof(f2118,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_409 ),
    inference(avatar_component_clause,[],[f2117])).

fof(f3140,plain,
    ( spl10_572
    | spl10_553 ),
    inference(avatar_split_clause,[],[f3133,f3040,f3138])).

fof(f3138,plain,
    ( spl10_572
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_572])])).

fof(f3133,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_553 ),
    inference(resolution,[],[f3041,f445])).

fof(f3130,plain,
    ( spl10_566
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(avatar_split_clause,[],[f3118,f3043,f646,f3092])).

fof(f3092,plain,
    ( spl10_566
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_566])])).

fof(f3043,plain,
    ( spl10_552
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_552])])).

fof(f3118,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k3_struct_0(sK0)))
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(resolution,[],[f3044,f756])).

fof(f3044,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_552 ),
    inference(avatar_component_clause,[],[f3043])).

fof(f3129,plain,
    ( spl10_564
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(avatar_split_clause,[],[f3117,f3043,f646,f3085])).

fof(f3085,plain,
    ( spl10_564
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_564])])).

fof(f3117,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(resolution,[],[f3044,f780])).

fof(f3128,plain,
    ( spl10_562
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(avatar_split_clause,[],[f3116,f3043,f646,f3078])).

fof(f3078,plain,
    ( spl10_562
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_562])])).

fof(f3116,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))))
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(resolution,[],[f3044,f888])).

fof(f3127,plain,
    ( spl10_570
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(avatar_split_clause,[],[f3115,f3043,f646,f3125])).

fof(f3125,plain,
    ( spl10_570
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_570])])).

fof(f3115,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))))))
    | ~ spl10_118
    | ~ spl10_552 ),
    inference(resolution,[],[f3044,f1002])).

fof(f3114,plain,
    ( spl10_560
    | spl10_549 ),
    inference(avatar_split_clause,[],[f3113,f3027,f3066])).

fof(f3066,plain,
    ( spl10_560
  <=> k1_funct_1(k6_relat_1(k3_struct_0(sK0)),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_560])])).

fof(f3113,plain,
    ( k1_funct_1(k6_relat_1(k3_struct_0(sK0)),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0))
    | ~ spl10_549 ),
    inference(resolution,[],[f3028,f445])).

fof(f3112,plain,
    ( spl10_568
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(avatar_split_clause,[],[f3100,f3030,f646,f3110])).

fof(f3110,plain,
    ( spl10_568
  <=> k3_struct_0(sK0) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_568])])).

fof(f3030,plain,
    ( spl10_548
  <=> v1_xboole_0(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_548])])).

fof(f3100,plain,
    ( k3_struct_0(sK0) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(resolution,[],[f3031,f756])).

fof(f3031,plain,
    ( v1_xboole_0(k3_struct_0(sK0))
    | ~ spl10_548 ),
    inference(avatar_component_clause,[],[f3030])).

fof(f3105,plain,
    ( spl10_566
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(avatar_split_clause,[],[f3099,f3030,f646,f3092])).

fof(f3099,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k3_struct_0(sK0)))
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(resolution,[],[f3031,f780])).

fof(f3104,plain,
    ( spl10_564
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(avatar_split_clause,[],[f3098,f3030,f646,f3085])).

fof(f3098,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(resolution,[],[f3031,f888])).

fof(f3103,plain,
    ( spl10_562
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(avatar_split_clause,[],[f3097,f3030,f646,f3078])).

fof(f3097,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))))
    | ~ spl10_118
    | ~ spl10_548 ),
    inference(resolution,[],[f3031,f1002])).

fof(f3096,plain,
    ( ~ spl10_406
    | spl10_549 ),
    inference(avatar_contradiction_clause,[],[f3095])).

fof(f3095,plain,
    ( $false
    | ~ spl10_406
    | ~ spl10_549 ),
    inference(subsumption_resolution,[],[f3073,f3028])).

fof(f3073,plain,
    ( v1_xboole_0(k3_struct_0(sK0))
    | ~ spl10_406 ),
    inference(resolution,[],[f2112,f270])).

fof(f2112,plain,
    ( sP9(k3_struct_0(sK0))
    | ~ spl10_406 ),
    inference(avatar_component_clause,[],[f2111])).

fof(f2111,plain,
    ( spl10_406
  <=> sP9(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_406])])).

fof(f3094,plain,
    ( spl10_566
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(avatar_split_clause,[],[f3071,f2111,f646,f3092])).

fof(f3071,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k3_struct_0(sK0)))
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(resolution,[],[f2112,f779])).

fof(f3087,plain,
    ( spl10_564
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(avatar_split_clause,[],[f3070,f2111,f646,f3085])).

fof(f3070,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(resolution,[],[f2112,f891])).

fof(f3080,plain,
    ( spl10_562
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(avatar_split_clause,[],[f3069,f2111,f646,f3078])).

fof(f3069,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k3_struct_0(sK0)))))))
    | ~ spl10_118
    | ~ spl10_406 ),
    inference(resolution,[],[f2112,f1001])).

fof(f3068,plain,
    ( spl10_560
    | spl10_549 ),
    inference(avatar_split_clause,[],[f3061,f3027,f3066])).

fof(f3061,plain,
    ( k1_funct_1(k6_relat_1(k3_struct_0(sK0)),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0))
    | ~ spl10_549 ),
    inference(resolution,[],[f3028,f445])).

fof(f3060,plain,
    ( spl10_406
    | ~ spl10_409
    | ~ spl10_394 ),
    inference(avatar_split_clause,[],[f2549,f2034,f2117,f2111])).

fof(f2549,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | sP9(k3_struct_0(sK0))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f134])).

fof(f3059,plain,
    ( spl10_408
    | spl10_558
    | ~ spl10_394 ),
    inference(avatar_split_clause,[],[f2566,f2034,f3057,f2114])).

fof(f2114,plain,
    ( spl10_408
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_408])])).

fof(f2566,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_struct_0(sK0))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl10_394 ),
    inference(resolution,[],[f2079,f104])).

fof(f2079,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k3_struct_0(sK0)) )
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f102])).

fof(f3055,plain,
    ( ~ spl10_409
    | spl10_556
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2954,f2245,f3053,f2117])).

fof(f3053,plain,
    ( spl10_556
  <=> ! [X8] :
        ( ~ r2_hidden(X8,sK3(k1_zfmisc_1(sK2)))
        | sP9(X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_556])])).

fof(f2954,plain,
    ( ! [X8] :
        ( ~ r2_hidden(X8,sK3(k1_zfmisc_1(sK2)))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | sP9(X8) )
    | ~ spl10_430 ),
    inference(resolution,[],[f2864,f134])).

fof(f3051,plain,
    ( spl10_552
    | spl10_554
    | ~ spl10_394
    | spl10_409 ),
    inference(avatar_split_clause,[],[f3025,f2117,f2034,f3049,f3043])).

fof(f3025,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))) = sK3(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2570,f547])).

fof(f2570,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_struct_0(sK0))
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2567,f128])).

fof(f2567,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k3_struct_0(sK0)) )
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(subsumption_resolution,[],[f2566,f2118])).

fof(f3038,plain,
    ( spl10_548
    | spl10_550
    | ~ spl10_394
    | spl10_409 ),
    inference(avatar_split_clause,[],[f3024,f2117,f2034,f3036,f3030])).

fof(f3024,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k3_struct_0(sK0))) = sK3(k3_struct_0(sK0))
    | v1_xboole_0(k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2570,f251])).

fof(f3011,plain,
    ( ~ spl10_547
    | spl10_413
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f3004,f2245,f2127,f3009])).

fof(f3009,plain,
    ( spl10_547
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_547])])).

fof(f3004,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_413
    | ~ spl10_430 ),
    inference(duplicate_literal_removal,[],[f3003])).

fof(f3003,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_413
    | ~ spl10_430 ),
    inference(resolution,[],[f2961,f2959])).

fof(f2987,plain,
    ( ~ spl10_545
    | ~ spl10_543
    | ~ spl10_42
    | spl10_413
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2966,f2245,f2127,f301,f2978,f2985])).

fof(f2985,plain,
    ( spl10_545
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_545])])).

fof(f2978,plain,
    ( spl10_543
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_543])])).

fof(f2966,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK2)
    | ~ spl10_42
    | ~ spl10_413
    | ~ spl10_430 ),
    inference(resolution,[],[f2959,f994])).

fof(f2980,plain,
    ( ~ spl10_541
    | ~ spl10_543
    | spl10_41
    | spl10_413
    | ~ spl10_414
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2965,f2245,f2169,f2127,f295,f2978,f2972])).

fof(f2972,plain,
    ( spl10_541
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_541])])).

fof(f2965,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK3(k1_zfmisc_1(sK2)))
    | ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1))
    | ~ spl10_41
    | ~ spl10_413
    | ~ spl10_414
    | ~ spl10_430 ),
    inference(resolution,[],[f2959,f2781])).

fof(f2946,plain,
    ( spl10_538
    | spl10_534
    | ~ spl10_118
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2931,f2245,f646,f2903,f2944])).

fof(f2944,plain,
    ( spl10_538
  <=> k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_538])])).

fof(f2931,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_430 ),
    inference(superposition,[],[f778,f2246])).

fof(f2939,plain,
    ( spl10_174
    | ~ spl10_118
    | ~ spl10_162
    | spl10_203 ),
    inference(avatar_split_clause,[],[f2938,f1097,f905,f646,f965])).

fof(f965,plain,
    ( spl10_174
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f1097,plain,
    ( spl10_203
  <=> k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_203])])).

fof(f2938,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_162
    | ~ spl10_203 ),
    inference(subsumption_resolution,[],[f2930,f1098])).

fof(f1098,plain,
    ( k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_203 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f2930,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_162 ),
    inference(superposition,[],[f778,f906])).

fof(f2937,plain,
    ( spl10_192
    | ~ spl10_100
    | ~ spl10_118
    | spl10_191 ),
    inference(avatar_split_clause,[],[f2936,f1058,f646,f570,f1067])).

fof(f1067,plain,
    ( spl10_192
  <=> k1_funct_1(k3_struct_0(sK4(sK5)),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f570,plain,
    ( spl10_100
  <=> k3_struct_0(sK4(sK5)) = k6_relat_1(u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f1058,plain,
    ( spl10_191
  <=> u1_struct_0(sK4(sK5)) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f2936,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK5)),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5)))
    | ~ spl10_100
    | ~ spl10_118
    | ~ spl10_191 ),
    inference(subsumption_resolution,[],[f2927,f1059])).

fof(f1059,plain,
    ( u1_struct_0(sK4(sK5)) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_191 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f2927,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK5)),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5)))
    | u1_struct_0(sK4(sK5)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_100
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f571])).

fof(f571,plain,
    ( k3_struct_0(sK4(sK5)) = k6_relat_1(u1_struct_0(sK4(sK5)))
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f570])).

fof(f2935,plain,
    ( spl10_188
    | ~ spl10_98
    | ~ spl10_118
    | spl10_187 ),
    inference(avatar_split_clause,[],[f2934,f1045,f646,f563,f1054])).

fof(f1054,plain,
    ( spl10_188
  <=> k1_funct_1(k3_struct_0(sK4(sK1)),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_188])])).

fof(f563,plain,
    ( spl10_98
  <=> k3_struct_0(sK4(sK1)) = k6_relat_1(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f1045,plain,
    ( spl10_187
  <=> u1_struct_0(sK4(sK1)) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_187])])).

fof(f2934,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK1)),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1)))
    | ~ spl10_98
    | ~ spl10_118
    | ~ spl10_187 ),
    inference(subsumption_resolution,[],[f2926,f1046])).

fof(f1046,plain,
    ( u1_struct_0(sK4(sK1)) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_187 ),
    inference(avatar_component_clause,[],[f1045])).

fof(f2926,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK1)),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1)))
    | u1_struct_0(sK4(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_98
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f564])).

fof(f564,plain,
    ( k3_struct_0(sK4(sK1)) = k6_relat_1(u1_struct_0(sK4(sK1)))
    | ~ spl10_98 ),
    inference(avatar_component_clause,[],[f563])).

fof(f2933,plain,
    ( spl10_184
    | ~ spl10_96
    | ~ spl10_118
    | spl10_183 ),
    inference(avatar_split_clause,[],[f2932,f1032,f646,f556,f1041])).

fof(f1041,plain,
    ( spl10_184
  <=> k1_funct_1(k3_struct_0(sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f556,plain,
    ( spl10_96
  <=> k3_struct_0(sK4(sK0)) = k6_relat_1(u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f2932,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | ~ spl10_96
    | ~ spl10_118
    | ~ spl10_183 ),
    inference(subsumption_resolution,[],[f2925,f1033])).

fof(f2925,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | u1_struct_0(sK4(sK0)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_96
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f557])).

fof(f557,plain,
    ( k3_struct_0(sK4(sK0)) = k6_relat_1(u1_struct_0(sK4(sK0)))
    | ~ spl10_96 ),
    inference(avatar_component_clause,[],[f556])).

fof(f2919,plain,
    ( ~ spl10_537
    | ~ spl10_530 ),
    inference(avatar_split_clause,[],[f2909,f2887,f2917])).

fof(f2917,plain,
    ( spl10_537
  <=> ~ sP9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_537])])).

fof(f2887,plain,
    ( spl10_530
  <=> r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_530])])).

fof(f2909,plain,
    ( ~ sP9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_530 ),
    inference(resolution,[],[f2888,f135])).

fof(f2888,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_530 ),
    inference(avatar_component_clause,[],[f2887])).

fof(f2912,plain,
    ( spl10_532
    | ~ spl10_530 ),
    inference(avatar_split_clause,[],[f2908,f2887,f2894])).

fof(f2894,plain,
    ( spl10_532
  <=> m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_532])])).

fof(f2908,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_530 ),
    inference(resolution,[],[f2888,f105])).

fof(f2911,plain,
    ( spl10_534
    | ~ spl10_530 ),
    inference(avatar_split_clause,[],[f2906,f2887,f2903])).

fof(f2906,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_530 ),
    inference(resolution,[],[f2888,f128])).

fof(f2905,plain,
    ( spl10_534
    | ~ spl10_430
    | spl10_527 ),
    inference(avatar_split_clause,[],[f2898,f2871,f2245,f2903])).

fof(f2871,plain,
    ( spl10_527
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_527])])).

fof(f2898,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_430
    | ~ spl10_527 ),
    inference(forward_demodulation,[],[f2897,f2246])).

fof(f2897,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_527 ),
    inference(resolution,[],[f2872,f445])).

fof(f2872,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_527 ),
    inference(avatar_component_clause,[],[f2871])).

fof(f2896,plain,
    ( spl10_532
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2867,f2245,f2894])).

fof(f2867,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_430 ),
    inference(superposition,[],[f107,f2246])).

fof(f2889,plain,
    ( spl10_526
    | spl10_530
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2866,f2245,f2887,f2874])).

fof(f2874,plain,
    ( spl10_526
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_526])])).

fof(f2866,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_430 ),
    inference(superposition,[],[f251,f2246])).

fof(f2882,plain,
    ( spl10_526
    | ~ spl10_529
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f2865,f2245,f2880,f2874])).

fof(f2880,plain,
    ( spl10_529
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_529])])).

fof(f2865,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(sK2)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_430 ),
    inference(superposition,[],[f268,f2246])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f251,f106])).

fof(f2858,plain,
    ( ~ spl10_525
    | spl10_41
    | ~ spl10_414 ),
    inference(avatar_split_clause,[],[f2851,f2169,f295,f2856])).

fof(f2856,plain,
    ( spl10_525
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_525])])).

fof(f2851,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1))
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(duplicate_literal_removal,[],[f2848])).

fof(f2848,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k4_tmap_1(sK0,sK1))
    | ~ spl10_41
    | ~ spl10_414 ),
    inference(resolution,[],[f2781,f2703])).

fof(f2847,plain,
    ( ~ spl10_515
    | ~ spl10_504 ),
    inference(avatar_split_clause,[],[f2842,f2755,f2803])).

fof(f2803,plain,
    ( spl10_515
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_515])])).

fof(f2755,plain,
    ( spl10_504
  <=> r2_hidden(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_504])])).

fof(f2842,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_504 ),
    inference(resolution,[],[f2756,f106])).

fof(f2756,plain,
    ( r2_hidden(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_504 ),
    inference(avatar_component_clause,[],[f2755])).

fof(f2846,plain,
    ( spl10_512
    | ~ spl10_504 ),
    inference(avatar_split_clause,[],[f2841,f2755,f2796])).

fof(f2796,plain,
    ( spl10_512
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK4(sK0))) = k4_tmap_1(sK0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_512])])).

fof(f2841,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK4(sK0))) = k4_tmap_1(sK0,sK4(sK0))
    | ~ spl10_504 ),
    inference(resolution,[],[f2756,f128])).

fof(f2840,plain,
    ( spl10_510
    | spl10_507 ),
    inference(avatar_split_clause,[],[f2839,f2758,f2777])).

fof(f2777,plain,
    ( spl10_510
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_510])])).

fof(f2758,plain,
    ( spl10_507
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_507])])).

fof(f2839,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_507 ),
    inference(resolution,[],[f2759,f445])).

fof(f2759,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_507 ),
    inference(avatar_component_clause,[],[f2758])).

fof(f2838,plain,
    ( spl10_522
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(avatar_split_clause,[],[f2815,f2761,f646,f2836])).

fof(f2836,plain,
    ( spl10_522
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_522])])).

fof(f2761,plain,
    ( spl10_506
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_506])])).

fof(f2815,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(resolution,[],[f2762,f756])).

fof(f2762,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_506 ),
    inference(avatar_component_clause,[],[f2761])).

fof(f2831,plain,
    ( spl10_520
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(avatar_split_clause,[],[f2814,f2761,f646,f2829])).

fof(f2829,plain,
    ( spl10_520
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_520])])).

fof(f2814,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(resolution,[],[f2762,f780])).

fof(f2824,plain,
    ( spl10_518
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(avatar_split_clause,[],[f2813,f2761,f646,f2822])).

fof(f2822,plain,
    ( spl10_518
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_518])])).

fof(f2813,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))))))
    | ~ spl10_118
    | ~ spl10_506 ),
    inference(resolution,[],[f2762,f888])).

fof(f2812,plain,
    ( ~ spl10_517
    | ~ spl10_504 ),
    inference(avatar_split_clause,[],[f2790,f2755,f2810])).

fof(f2810,plain,
    ( spl10_517
  <=> ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_517])])).

fof(f2790,plain,
    ( ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_504 ),
    inference(resolution,[],[f2756,f135])).

fof(f2805,plain,
    ( ~ spl10_515
    | ~ spl10_504 ),
    inference(avatar_split_clause,[],[f2788,f2755,f2803])).

fof(f2788,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_504 ),
    inference(resolution,[],[f2756,f106])).

fof(f2798,plain,
    ( spl10_512
    | ~ spl10_504 ),
    inference(avatar_split_clause,[],[f2787,f2755,f2796])).

fof(f2787,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK4(sK0))) = k4_tmap_1(sK0,sK4(sK0))
    | ~ spl10_504 ),
    inference(resolution,[],[f2756,f128])).

fof(f2779,plain,
    ( spl10_510
    | spl10_507 ),
    inference(avatar_split_clause,[],[f2772,f2758,f2777])).

fof(f2772,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_507 ),
    inference(resolution,[],[f2759,f445])).

fof(f2771,plain,
    ( spl10_508
    | spl10_503 ),
    inference(avatar_split_clause,[],[f2764,f2748,f2769])).

fof(f2764,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | ~ spl10_503 ),
    inference(resolution,[],[f2749,f445])).

fof(f2763,plain,
    ( spl10_504
    | spl10_506
    | ~ spl10_492 ),
    inference(avatar_split_clause,[],[f2711,f2670,f2761,f2755])).

fof(f2711,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | r2_hidden(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl10_492 ),
    inference(resolution,[],[f2671,f104])).

fof(f2750,plain,
    ( spl10_500
    | ~ spl10_503
    | ~ spl10_492 ),
    inference(avatar_split_clause,[],[f2709,f2670,f2748,f2742])).

fof(f2709,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))
    | sP9(k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492 ),
    inference(resolution,[],[f2671,f134])).

fof(f2737,plain,
    ( ~ spl10_499
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f2730,f2681,f2670,f2627,f2735])).

fof(f2735,plain,
    ( spl10_499
  <=> ~ sP8(u1_struct_0(sK0),u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_499])])).

fof(f2730,plain,
    ( ~ sP8(u1_struct_0(sK0),u1_struct_0(sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f2729,f2628])).

fof(f2729,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f2708,f2682])).

fof(f2708,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK4(sK0)))
    | ~ spl10_492 ),
    inference(resolution,[],[f2671,f133])).

fof(f2728,plain,
    ( spl10_496
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(avatar_split_clause,[],[f2721,f2681,f2670,f2627,f2726])).

fof(f2726,plain,
    ( spl10_496
  <=> r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),k4_tmap_1(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_496])])).

fof(f2721,plain,
    ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_482
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f2720,f2628])).

fof(f2720,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492
    | ~ spl10_494 ),
    inference(subsumption_resolution,[],[f2707,f2682])).

fof(f2707,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),k4_tmap_1(sK0,sK4(sK0)))
    | ~ spl10_492 ),
    inference(resolution,[],[f2671,f136])).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2690,plain,
    ( ~ spl10_0
    | spl10_485 ),
    inference(avatar_contradiction_clause,[],[f2689])).

fof(f2689,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_485 ),
    inference(subsumption_resolution,[],[f2688,f142])).

fof(f2688,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_485 ),
    inference(resolution,[],[f2641,f108])).

fof(f108,plain,(
    ! [X0] :
      ( m1_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',existence_m1_pre_topc)).

fof(f2641,plain,
    ( ~ m1_pre_topc(sK4(sK0),sK0)
    | ~ spl10_485 ),
    inference(avatar_component_clause,[],[f2640])).

fof(f2640,plain,
    ( spl10_485
  <=> ~ m1_pre_topc(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_485])])).

fof(f2686,plain,
    ( ~ spl10_0
    | spl10_481 ),
    inference(avatar_contradiction_clause,[],[f2685])).

fof(f2685,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_481 ),
    inference(subsumption_resolution,[],[f2684,f142])).

fof(f2684,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_481 ),
    inference(resolution,[],[f2622,f249])).

fof(f249,plain,(
    ! [X0] :
      ( l1_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f232,f124])).

fof(f232,plain,(
    ! [X0] :
      ( l1_pre_topc(sK4(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_pre_topc(sK4(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f109,f108])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_m1_pre_topc)).

fof(f2622,plain,
    ( ~ l1_struct_0(sK4(sK0))
    | ~ spl10_481 ),
    inference(avatar_component_clause,[],[f2621])).

fof(f2621,plain,
    ( spl10_481
  <=> ~ l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_481])])).

fof(f2683,plain,
    ( ~ spl10_481
    | spl10_494
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2676,f2046,f2040,f2034,f1936,f220,f2681,f2621])).

fof(f2676,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2675,f2035])).

fof(f2675,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2674,f2041])).

fof(f2674,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2673,f2047])).

fof(f2673,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2613,f221])).

fof(f2613,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_378 ),
    inference(duplicate_literal_removal,[],[f2612])).

fof(f2612,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl10_378 ),
    inference(superposition,[],[f113,f1937])).

fof(f2672,plain,
    ( ~ spl10_481
    | spl10_492
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2665,f2046,f2040,f2034,f1936,f220,f2670,f2621])).

fof(f2665,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2664,f2035])).

fof(f2664,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2663,f2041])).

fof(f2663,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2662,f2047])).

fof(f2662,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2614,f221])).

fof(f2614,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_378 ),
    inference(duplicate_literal_removal,[],[f2611])).

fof(f2611,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK4(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl10_378 ),
    inference(superposition,[],[f114,f1937])).

fof(f2661,plain,
    ( ~ spl10_485
    | spl10_486
    | spl10_490
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2657,f2046,f2040,f2034,f1936,f155,f148,f141,f2659,f2646,f2640])).

fof(f2646,plain,
    ( spl10_486
  <=> v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_486])])).

fof(f2659,plain,
    ( spl10_490
  <=> ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_490])])).

fof(f2657,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2656,f2035])).

fof(f2656,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2655,f2041])).

fof(f2655,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2654,f2047])).

fof(f2654,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2653,f149])).

fof(f2653,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_5
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2652,f156])).

fof(f2652,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_0
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2615,f142])).

fof(f2615,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) )
    | ~ spl10_378 ),
    inference(duplicate_literal_removal,[],[f2610])).

fof(f2610,plain,
    ( ! [X1] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X1)
        | m1_subset_1(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_378 ),
    inference(superposition,[],[f115,f1937])).

fof(f2651,plain,
    ( ~ spl10_485
    | spl10_486
    | spl10_488
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2635,f2046,f2040,f2034,f1936,f155,f148,f141,f2649,f2646,f2640])).

fof(f2649,plain,
    ( spl10_488
  <=> ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_488])])).

fof(f2635,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2634,f2035])).

fof(f2634,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2633,f2041])).

fof(f2633,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2632,f2047])).

fof(f2632,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2631,f156])).

fof(f2631,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2630,f142])).

fof(f2630,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_2
    | ~ spl10_378 ),
    inference(subsumption_resolution,[],[f2616,f149])).

fof(f2616,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0))) )
    | ~ spl10_378 ),
    inference(duplicate_literal_removal,[],[f2609])).

fof(f2609,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK4(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK4(sK0)),X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK4(sK0))
        | ~ m1_pre_topc(sK4(sK0),sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK4(sK0),k3_struct_0(sK0),X0),u1_struct_0(sK4(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_378 ),
    inference(superposition,[],[f116,f1937])).

fof(f2629,plain,
    ( ~ spl10_481
    | spl10_482
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2608,f2046,f2040,f2034,f1936,f220,f2627,f2621])).

fof(f2608,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK4(sK0)))
    | ~ l1_struct_0(sK4(sK0))
    | ~ spl10_22
    | ~ spl10_378
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(superposition,[],[f2084,f1937])).

fof(f2084,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0))
        | ~ l1_struct_0(X0) )
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2083,f2041])).

fof(f2083,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)) )
    | ~ spl10_22
    | ~ spl10_394
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2082,f2047])).

fof(f2082,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)) )
    | ~ spl10_22
    | ~ spl10_394 ),
    inference(subsumption_resolution,[],[f2081,f221])).

fof(f2081,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)) )
    | ~ spl10_394 ),
    inference(duplicate_literal_removal,[],[f2073])).

fof(f2073,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)) )
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f112])).

fof(f2607,plain,
    ( ~ spl10_479
    | ~ spl10_394
    | spl10_461 ),
    inference(avatar_split_clause,[],[f2599,f2478,f2034,f2605])).

fof(f2605,plain,
    ( spl10_479
  <=> ~ r2_hidden(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_479])])).

fof(f2478,plain,
    ( spl10_461
  <=> ~ m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_461])])).

fof(f2599,plain,
    ( ~ r2_hidden(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_461 ),
    inference(resolution,[],[f2479,f2079])).

fof(f2479,plain,
    ( ~ m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_461 ),
    inference(avatar_component_clause,[],[f2478])).

fof(f2598,plain,
    ( ~ spl10_477
    | ~ spl10_394
    | spl10_409 ),
    inference(avatar_split_clause,[],[f2591,f2117,f2034,f2596])).

fof(f2596,plain,
    ( spl10_477
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_477])])).

fof(f2591,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(duplicate_literal_removal,[],[f2590])).

fof(f2590,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_struct_0(sK0))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2571,f2567])).

fof(f2571,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,k3_struct_0(sK0)) )
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2567,f106])).

fof(f2588,plain,
    ( ~ spl10_473
    | ~ spl10_475
    | ~ spl10_42
    | ~ spl10_394
    | spl10_409 ),
    inference(avatar_split_clause,[],[f2575,f2117,f2034,f301,f2586,f2580])).

fof(f2580,plain,
    ( spl10_473
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).

fof(f2586,plain,
    ( spl10_475
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_475])])).

fof(f2575,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),k3_struct_0(sK0))
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK2)
    | ~ spl10_42
    | ~ spl10_394
    | ~ spl10_409 ),
    inference(resolution,[],[f2567,f994])).

fof(f2565,plain,
    ( ~ spl10_425
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f2560,f2124,f2213])).

fof(f2213,plain,
    ( spl10_425
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_425])])).

fof(f2124,plain,
    ( spl10_410
  <=> r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_410])])).

fof(f2560,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl10_410 ),
    inference(resolution,[],[f2125,f106])).

fof(f2125,plain,
    ( r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_410 ),
    inference(avatar_component_clause,[],[f2124])).

fof(f2564,plain,
    ( spl10_422
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f2559,f2124,f2206])).

fof(f2206,plain,
    ( spl10_422
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_422])])).

fof(f2559,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl10_410 ),
    inference(resolution,[],[f2125,f128])).

fof(f2558,plain,
    ( spl10_410
    | ~ spl10_394
    | spl10_413 ),
    inference(avatar_split_clause,[],[f2557,f2127,f2034,f2124])).

fof(f2557,plain,
    ( r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_394
    | ~ spl10_413 ),
    inference(subsumption_resolution,[],[f2551,f2128])).

fof(f2551,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f104])).

fof(f2543,plain,
    ( spl10_418
    | spl10_413 ),
    inference(avatar_split_clause,[],[f2542,f2127,f2185])).

fof(f2185,plain,
    ( spl10_418
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_418])])).

fof(f2542,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_413 ),
    inference(resolution,[],[f2128,f445])).

fof(f2541,plain,
    ( ~ spl10_395
    | spl10_470
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_9
    | ~ spl10_156
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2537,f2046,f2040,f871,f169,f162,f155,f148,f141,f2539,f2037])).

fof(f2037,plain,
    ( spl10_395
  <=> ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_395])])).

fof(f2537,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2536,f2041])).

fof(f2536,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2535,f2047])).

fof(f2535,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2534,f163])).

fof(f2534,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_9
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2533,f170])).

fof(f2533,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2532,f156])).

fof(f2532,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2531,f142])).

fof(f2531,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_2
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2518,f149])).

fof(f2518,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1)) )
    | ~ spl10_156 ),
    inference(duplicate_literal_removal,[],[f2517])).

fof(f2517,plain,
    ( ! [X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(k3_struct_0(sK0))
        | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | r2_hidden(sK6(sK0,sK0,sK1,k3_struct_0(sK0),X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl10_156 ),
    inference(superposition,[],[f116,f872])).

fof(f2512,plain,
    ( spl10_468
    | spl10_463 ),
    inference(avatar_split_clause,[],[f2505,f2484,f2510])).

fof(f2510,plain,
    ( spl10_468
  <=> k1_funct_1(k6_relat_1(sK3(sK3(k1_zfmisc_1(sK2)))),sK3(sK3(sK3(k1_zfmisc_1(sK2))))) = sK3(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_468])])).

fof(f2484,plain,
    ( spl10_463
  <=> ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_463])])).

fof(f2505,plain,
    ( k1_funct_1(k6_relat_1(sK3(sK3(k1_zfmisc_1(sK2)))),sK3(sK3(sK3(k1_zfmisc_1(sK2))))) = sK3(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_463 ),
    inference(resolution,[],[f2485,f445])).

fof(f2485,plain,
    ( ~ v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_463 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2504,plain,
    ( ~ spl10_467
    | spl10_462
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2389,f2232,f2487,f2502])).

fof(f2502,plain,
    ( spl10_467
  <=> ~ sP9(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_467])])).

fof(f2487,plain,
    ( spl10_462
  <=> v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_462])])).

fof(f2232,plain,
    ( spl10_428
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_428])])).

fof(f2389,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ sP9(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_428 ),
    inference(superposition,[],[f612,f2233])).

fof(f2233,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_428 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2497,plain,
    ( spl10_464
    | spl10_462
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2490,f2232,f2487,f2495])).

fof(f2495,plain,
    ( spl10_464
  <=> r2_hidden(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_464])])).

fof(f2490,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | r2_hidden(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2388,f2233])).

fof(f2388,plain,
    ( r2_hidden(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_428 ),
    inference(superposition,[],[f547,f2233])).

fof(f2489,plain,
    ( spl10_460
    | spl10_462
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2476,f2232,f2487,f2481])).

fof(f2481,plain,
    ( spl10_460
  <=> m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_460])])).

fof(f2476,plain,
    ( v1_xboole_0(sK3(sK3(k1_zfmisc_1(sK2))))
    | m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2385,f2233])).

fof(f2385,plain,
    ( m1_subset_1(sK3(sK3(sK3(k1_zfmisc_1(sK2)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_428 ),
    inference(superposition,[],[f401,f2233])).

fof(f2475,plain,
    ( ~ spl10_453
    | ~ spl10_455
    | spl10_458
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2471,f2232,f2473,f2457,f2451])).

fof(f2451,plain,
    ( spl10_453
  <=> ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_453])])).

fof(f2457,plain,
    ( spl10_455
  <=> ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_455])])).

fof(f2473,plain,
    ( spl10_458
  <=> ! [X11] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X11)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X11,sK3(k1_zfmisc_1(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_458])])).

fof(f2471,plain,
    ( ! [X11] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),X11)
        | ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X11,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2470,f2233])).

fof(f2470,plain,
    ( ! [X11] :
        ( ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X11,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),X11) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2469,f2233])).

fof(f2469,plain,
    ( ! [X11] :
        ( ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X11,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),X11) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2468,f2233])).

fof(f2468,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),X11) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2381,f2233])).

fof(f2381,plain,
    ( ! [X11] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X11,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(sK0),u1_struct_0(sK0))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),X11) )
    | ~ spl10_428 ),
    inference(superposition,[],[f1177,f2233])).

fof(f1177,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_funct_2(X5,X6,X4,sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
      | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X5,X6)
      | r2_funct_2(X5,X6,sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X4) ) ),
    inference(resolution,[],[f95,f107])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | r2_funct_2(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
       => r2_funct_2(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',symmetry_r2_funct_2)).

fof(f2467,plain,
    ( ~ spl10_453
    | ~ spl10_455
    | spl10_456
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2463,f2232,f2465,f2457,f2451])).

fof(f2465,plain,
    ( spl10_456
  <=> ! [X10] :
        ( sK3(sK3(k1_zfmisc_1(sK2))) = X10
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X10)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X10,sK3(k1_zfmisc_1(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_456])])).

fof(f2463,plain,
    ( ! [X10] :
        ( sK3(sK3(k1_zfmisc_1(sK2))) = X10
        | ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X10,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2462,f2233])).

fof(f2462,plain,
    ( ! [X10] :
        ( ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X10,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(X10)
        | sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X10
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2461,f2233])).

fof(f2461,plain,
    ( ! [X10] :
        ( ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X10,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X10)
        | sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X10
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2460,f2233])).

fof(f2460,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,sK3(k1_zfmisc_1(sK2)))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X10)
        | sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X10
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2380,f2233])).

fof(f2380,plain,
    ( ! [X10] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),X10,sK3(sK3(k1_zfmisc_1(sK2))))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X10)
        | sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X10
        | ~ v1_funct_2(X10,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl10_428 ),
    inference(superposition,[],[f970,f2233])).

fof(f970,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_funct_2(X5,X6,X4,sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))))
      | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))),X5,X6)
      | ~ v1_funct_1(X4)
      | sK3(k1_zfmisc_1(k2_zfmisc_1(X5,X6))) = X4
      | ~ v1_funct_2(X4,X5,X6) ) ),
    inference(resolution,[],[f94,f107])).

fof(f2459,plain,
    ( spl10_450
    | ~ spl10_453
    | ~ spl10_455
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2440,f2232,f2457,f2451,f2445])).

fof(f2445,plain,
    ( spl10_450
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_450])])).

fof(f2440,plain,
    ( ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2439,f2233])).

fof(f2439,plain,
    ( ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(sK2))))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_428 ),
    inference(forward_demodulation,[],[f2379,f2233])).

fof(f2379,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2))))
    | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_428 ),
    inference(superposition,[],[f590,f2233])).

fof(f590,plain,(
    ! [X0,X1] :
      ( r2_funct_2(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
      | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
      | ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0,X1) ) ),
    inference(resolution,[],[f136,f107])).

fof(f2436,plain,
    ( spl10_444
    | ~ spl10_22
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2435,f2232,f220,f2410])).

fof(f2410,plain,
    ( spl10_444
  <=> m1_subset_1(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_444])])).

fof(f2435,plain,
    ( m1_subset_1(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_22
    | ~ spl10_428 ),
    inference(subsumption_resolution,[],[f2373,f221])).

fof(f2373,plain,
    ( m1_subset_1(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ l1_struct_0(sK0)
    | ~ spl10_428 ),
    inference(superposition,[],[f120,f2233])).

fof(f2434,plain,
    ( ~ spl10_447
    | spl10_448
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2421,f2232,f155,f148,f141,f2432,f2426])).

fof(f2426,plain,
    ( spl10_447
  <=> ~ m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_447])])).

fof(f2432,plain,
    ( spl10_448
  <=> m1_subset_1(k4_tmap_1(sK0,sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_448])])).

fof(f2421,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ m1_pre_topc(sK0,sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_428 ),
    inference(subsumption_resolution,[],[f2420,f156])).

fof(f2420,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_428 ),
    inference(subsumption_resolution,[],[f2419,f142])).

fof(f2419,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_428 ),
    inference(subsumption_resolution,[],[f2372,f149])).

fof(f2372,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_428 ),
    inference(superposition,[],[f99,f2233])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_k4_tmap_1)).

fof(f2412,plain,
    ( spl10_444
    | ~ spl10_394
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2368,f2232,f2034,f2410])).

fof(f2368,plain,
    ( m1_subset_1(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_394
    | ~ spl10_428 ),
    inference(backward_demodulation,[],[f2233,f2035])).

fof(f2405,plain,
    ( ~ spl10_443
    | spl10_411
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2365,f2232,f2121,f2403])).

fof(f2403,plain,
    ( spl10_443
  <=> ~ r2_hidden(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_443])])).

fof(f2121,plain,
    ( spl10_411
  <=> ~ r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_411])])).

fof(f2365,plain,
    ( ~ r2_hidden(k3_struct_0(sK0),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_411
    | ~ spl10_428 ),
    inference(backward_demodulation,[],[f2233,f2122])).

fof(f2122,plain,
    ( ~ r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_411 ),
    inference(avatar_component_clause,[],[f2121])).

fof(f2398,plain,
    ( ~ spl10_441
    | spl10_425
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f2364,f2232,f2213,f2396])).

fof(f2396,plain,
    ( spl10_441
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_441])])).

fof(f2364,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),k3_struct_0(sK0))
    | ~ spl10_425
    | ~ spl10_428 ),
    inference(backward_demodulation,[],[f2233,f2214])).

fof(f2214,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl10_425 ),
    inference(avatar_component_clause,[],[f2213])).

fof(f2335,plain,
    ( spl10_428
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(avatar_split_clause,[],[f2334,f2130,f646,f2232])).

fof(f2130,plain,
    ( spl10_412
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_412])])).

fof(f2334,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(resolution,[],[f2227,f647])).

fof(f2227,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = X1 )
    | ~ spl10_412 ),
    inference(resolution,[],[f2131,f122])).

fof(f2131,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_412 ),
    inference(avatar_component_clause,[],[f2130])).

fof(f2329,plain,
    ( ~ spl10_439
    | ~ spl10_434 ),
    inference(avatar_split_clause,[],[f2312,f2308,f2327])).

fof(f2327,plain,
    ( spl10_439
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_439])])).

fof(f2308,plain,
    ( spl10_434
  <=> r2_hidden(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_434])])).

fof(f2312,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1))
    | ~ spl10_434 ),
    inference(resolution,[],[f2309,f106])).

fof(f2309,plain,
    ( r2_hidden(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_434 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f2322,plain,
    ( spl10_436
    | ~ spl10_434 ),
    inference(avatar_split_clause,[],[f2311,f2308,f2320])).

fof(f2320,plain,
    ( spl10_436
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK1)) = k4_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_436])])).

fof(f2311,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK1)) = k4_tmap_1(sK0,sK1)
    | ~ spl10_434 ),
    inference(resolution,[],[f2309,f128])).

fof(f2310,plain,
    ( spl10_434
    | spl10_33
    | ~ spl10_414 ),
    inference(avatar_split_clause,[],[f2303,f2169,f259,f2308])).

fof(f259,plain,
    ( spl10_33
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f2303,plain,
    ( r2_hidden(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_33
    | ~ spl10_414 ),
    inference(subsumption_resolution,[],[f2285,f260])).

fof(f260,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f259])).

fof(f2285,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_414 ),
    inference(resolution,[],[f2170,f104])).

fof(f2302,plain,
    ( spl10_432
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(avatar_split_clause,[],[f2295,f2194,f2169,f2055,f2300])).

fof(f2300,plain,
    ( spl10_432
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_432])])).

fof(f2295,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k4_tmap_1(sK0,sK1))
    | ~ spl10_400
    | ~ spl10_414
    | ~ spl10_420 ),
    inference(subsumption_resolution,[],[f2294,f2195])).

fof(f2294,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k4_tmap_1(sK0,sK1))
    | ~ spl10_400
    | ~ spl10_414 ),
    inference(subsumption_resolution,[],[f2281,f2056])).

fof(f2281,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),k4_tmap_1(sK0,sK1))
    | ~ spl10_414 ),
    inference(resolution,[],[f2170,f136])).

fof(f2256,plain,
    ( spl10_162
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f2254,f646,f905])).

fof(f2254,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_118 ),
    inference(resolution,[],[f780,f647])).

fof(f2255,plain,
    ( spl10_430
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(avatar_split_clause,[],[f2251,f2130,f646,f2245])).

fof(f2251,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(resolution,[],[f780,f2131])).

fof(f2247,plain,
    ( spl10_430
    | ~ spl10_118
    | ~ spl10_426 ),
    inference(avatar_split_clause,[],[f2239,f2217,f646,f2245])).

fof(f2217,plain,
    ( spl10_426
  <=> sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_426])])).

fof(f2239,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl10_118
    | ~ spl10_426 ),
    inference(resolution,[],[f779,f2218])).

fof(f2218,plain,
    ( sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_426 ),
    inference(avatar_component_clause,[],[f2217])).

fof(f2240,plain,
    ( spl10_162
    | ~ spl10_118
    | ~ spl10_164 ),
    inference(avatar_split_clause,[],[f2238,f925,f646,f905])).

fof(f925,plain,
    ( spl10_164
  <=> sP9(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_164])])).

fof(f2238,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_118
    | ~ spl10_164 ),
    inference(resolution,[],[f779,f926])).

fof(f926,plain,
    ( sP9(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_164 ),
    inference(avatar_component_clause,[],[f925])).

fof(f2234,plain,
    ( spl10_428
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(avatar_split_clause,[],[f2225,f2130,f646,f2232])).

fof(f2225,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_412 ),
    inference(resolution,[],[f2131,f756])).

fof(f2222,plain,
    ( ~ spl10_427
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f2200,f2124,f2220])).

fof(f2220,plain,
    ( spl10_427
  <=> ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_427])])).

fof(f2200,plain,
    ( ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_410 ),
    inference(resolution,[],[f2125,f135])).

fof(f2215,plain,
    ( ~ spl10_425
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f2198,f2124,f2213])).

fof(f2198,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl10_410 ),
    inference(resolution,[],[f2125,f106])).

fof(f2208,plain,
    ( spl10_422
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f2197,f2124,f2206])).

fof(f2197,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl10_410 ),
    inference(resolution,[],[f2125,f128])).

fof(f2196,plain,
    ( spl10_420
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2189,f2046,f2040,f2034,f871,f246,f220,f2194])).

fof(f2189,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2188,f247])).

fof(f2188,plain,
    ( v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(superposition,[],[f2084,f872])).

fof(f2187,plain,
    ( spl10_418
    | spl10_413 ),
    inference(avatar_split_clause,[],[f2180,f2127,f2185])).

fof(f2180,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_413 ),
    inference(resolution,[],[f2128,f445])).

fof(f2179,plain,
    ( spl10_416
    | spl10_409 ),
    inference(avatar_split_clause,[],[f2172,f2117,f2177])).

fof(f2172,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl10_409 ),
    inference(resolution,[],[f2118,f445])).

fof(f2171,plain,
    ( spl10_414
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2164,f2046,f2040,f2034,f871,f246,f220,f2169])).

fof(f2164,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2163,f247])).

fof(f2163,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2162,f2035])).

fof(f2162,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2161,f2041])).

fof(f2161,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2160,f2047])).

fof(f2160,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2144,f221])).

fof(f2144,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_156 ),
    inference(duplicate_literal_removal,[],[f2143])).

fof(f2143,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl10_156 ),
    inference(superposition,[],[f114,f872])).

fof(f2132,plain,
    ( spl10_410
    | spl10_412
    | ~ spl10_394 ),
    inference(avatar_split_clause,[],[f2080,f2034,f2130,f2124])).

fof(f2080,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | r2_hidden(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f104])).

fof(f2119,plain,
    ( spl10_406
    | ~ spl10_409
    | ~ spl10_394 ),
    inference(avatar_split_clause,[],[f2078,f2034,f2117,f2111])).

fof(f2078,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | sP9(k3_struct_0(sK0))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f134])).

fof(f2106,plain,
    ( ~ spl10_405
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2099,f2046,f2040,f2034,f2104])).

fof(f2104,plain,
    ( spl10_405
  <=> ~ sP8(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_405])])).

fof(f2099,plain,
    ( ~ sP8(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2098,f2047])).

fof(f2098,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_396 ),
    inference(subsumption_resolution,[],[f2077,f2041])).

fof(f2077,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f133])).

fof(f2097,plain,
    ( spl10_402
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(avatar_split_clause,[],[f2090,f2046,f2040,f2034,f2095])).

fof(f2095,plain,
    ( spl10_402
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_402])])).

fof(f2090,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_396
    | ~ spl10_398 ),
    inference(subsumption_resolution,[],[f2089,f2047])).

fof(f2089,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl10_394
    | ~ spl10_396 ),
    inference(subsumption_resolution,[],[f2076,f2041])).

fof(f2076,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k3_struct_0(sK0))
    | ~ spl10_394 ),
    inference(resolution,[],[f2035,f136])).

fof(f2072,plain,
    ( ~ spl10_22
    | spl10_395 ),
    inference(avatar_contradiction_clause,[],[f2071])).

fof(f2071,plain,
    ( $false
    | ~ spl10_22
    | ~ spl10_395 ),
    inference(subsumption_resolution,[],[f2070,f221])).

fof(f2070,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_395 ),
    inference(resolution,[],[f2038,f120])).

fof(f2038,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_395 ),
    inference(avatar_component_clause,[],[f2037])).

fof(f2069,plain,
    ( ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6
    | spl10_401 ),
    inference(avatar_contradiction_clause,[],[f2068])).

fof(f2068,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_401 ),
    inference(subsumption_resolution,[],[f2067,f156])).

fof(f2067,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_401 ),
    inference(subsumption_resolution,[],[f2066,f163])).

fof(f2066,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_401 ),
    inference(subsumption_resolution,[],[f2065,f142])).

fof(f2065,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_401 ),
    inference(subsumption_resolution,[],[f2064,f149])).

fof(f2064,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_401 ),
    inference(resolution,[],[f2053,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2053,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl10_401 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f2052,plain,
    ( spl10_401
  <=> ~ v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_401])])).

fof(f2063,plain,
    ( ~ spl10_22
    | spl10_397 ),
    inference(avatar_contradiction_clause,[],[f2062])).

fof(f2062,plain,
    ( $false
    | ~ spl10_22
    | ~ spl10_397 ),
    inference(subsumption_resolution,[],[f2061,f221])).

fof(f2061,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_397 ),
    inference(resolution,[],[f2044,f119])).

fof(f2044,plain,
    ( ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_397 ),
    inference(avatar_component_clause,[],[f2043])).

fof(f2043,plain,
    ( spl10_397
  <=> ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_397])])).

fof(f2060,plain,
    ( ~ spl10_22
    | spl10_399 ),
    inference(avatar_contradiction_clause,[],[f2059])).

fof(f2059,plain,
    ( $false
    | ~ spl10_22
    | ~ spl10_399 ),
    inference(subsumption_resolution,[],[f2058,f221])).

fof(f2058,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_399 ),
    inference(resolution,[],[f2050,f118])).

fof(f2050,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | ~ spl10_399 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f2049,plain,
    ( spl10_399
  <=> ~ v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_399])])).

fof(f2057,plain,
    ( ~ spl10_395
    | ~ spl10_397
    | ~ spl10_399
    | spl10_400
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156 ),
    inference(avatar_split_clause,[],[f2032,f871,f246,f220,f2055,f2049,f2043,f2037])).

fof(f2032,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_22
    | ~ spl10_28
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2031,f247])).

fof(f2031,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_22
    | ~ spl10_156 ),
    inference(subsumption_resolution,[],[f2030,f221])).

fof(f2030,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ spl10_156 ),
    inference(duplicate_literal_removal,[],[f2029])).

fof(f2029,plain,
    ( v1_funct_2(k4_tmap_1(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(k3_struct_0(sK0))
    | ~ v1_funct_2(k3_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl10_156 ),
    inference(superposition,[],[f113,f872])).

fof(f2028,plain,
    ( spl10_392
    | spl10_253 ),
    inference(avatar_split_clause,[],[f2021,f1351,f2026])).

fof(f2026,plain,
    ( spl10_392
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_392])])).

fof(f1351,plain,
    ( spl10_253
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_253])])).

fof(f2021,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))) = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ spl10_253 ),
    inference(resolution,[],[f1352,f445])).

fof(f1352,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ spl10_253 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f2015,plain,
    ( spl10_172
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2011,f945,f952])).

fof(f952,plain,
    ( spl10_172
  <=> m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f945,plain,
    ( spl10_170
  <=> r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f2011,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_170 ),
    inference(resolution,[],[f946,f105])).

fof(f946,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_170 ),
    inference(avatar_component_clause,[],[f945])).

fof(f2014,plain,
    ( spl10_174
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f2009,f945,f965])).

fof(f2009,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_170 ),
    inference(resolution,[],[f946,f128])).

fof(f1983,plain,
    ( spl10_390
    | spl10_353 ),
    inference(avatar_split_clause,[],[f1976,f1830,f1981])).

fof(f1981,plain,
    ( spl10_390
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK5)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK5))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_390])])).

fof(f1830,plain,
    ( spl10_353
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_353])])).

fof(f1976,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK5)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK5))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK5))))
    | ~ spl10_353 ),
    inference(resolution,[],[f1831,f445])).

fof(f1831,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK5))))
    | ~ spl10_353 ),
    inference(avatar_component_clause,[],[f1830])).

fof(f1975,plain,
    ( spl10_214
    | spl10_167 ),
    inference(avatar_split_clause,[],[f1974,f929,f1195])).

fof(f1195,plain,
    ( spl10_214
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_214])])).

fof(f929,plain,
    ( spl10_167
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_167])])).

fof(f1974,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f930,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(avatar_component_clause,[],[f929])).

fof(f1971,plain,
    ( spl10_384
    | spl10_386
    | ~ spl10_389
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f1929,f204,f1969,f1963,f1957])).

fof(f1957,plain,
    ( spl10_384
  <=> k4_tmap_1(sK5,sK4(sK5)) = k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_384])])).

fof(f1963,plain,
    ( spl10_386
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_386])])).

fof(f1969,plain,
    ( spl10_389
  <=> ~ v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_389])])).

fof(f204,plain,
    ( spl10_18
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f1929,plain,
    ( ~ v2_pre_topc(sK5)
    | v2_struct_0(sK5)
    | k4_tmap_1(sK5,sK4(sK5)) = k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK4(sK5))
    | ~ spl10_18 ),
    inference(resolution,[],[f863,f205])).

fof(f205,plain,
    ( l1_pre_topc(sK5)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f863,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(X0,sK4(X0)) = k2_tmap_1(X0,X0,k3_struct_0(X0),sK4(X0)) ) ),
    inference(duplicate_literal_removal,[],[f862])).

fof(f862,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(X0,sK4(X0)) = k2_tmap_1(X0,X0,k3_struct_0(X0),sK4(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f100,f108])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',d7_tmap_1)).

fof(f1952,plain,
    ( spl10_380
    | ~ spl10_383
    | spl10_9
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f1939,f238,f169,f1950,f1944])).

fof(f1944,plain,
    ( spl10_380
  <=> k4_tmap_1(sK1,sK4(sK1)) = k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_380])])).

fof(f1950,plain,
    ( spl10_383
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_383])])).

fof(f238,plain,
    ( spl10_26
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f1939,plain,
    ( ~ v2_pre_topc(sK1)
    | k4_tmap_1(sK1,sK4(sK1)) = k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1))
    | ~ spl10_9
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f1927,f170])).

fof(f1927,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | k4_tmap_1(sK1,sK4(sK1)) = k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK4(sK1))
    | ~ spl10_26 ),
    inference(resolution,[],[f863,f239])).

fof(f239,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f1938,plain,
    ( spl10_378
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5 ),
    inference(avatar_split_clause,[],[f1931,f155,f148,f141,f1936])).

fof(f1931,plain,
    ( k4_tmap_1(sK0,sK4(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f1930,f156])).

fof(f1930,plain,
    ( v2_struct_0(sK0)
    | k4_tmap_1(sK0,sK4(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f1926,f149])).

fof(f1926,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k4_tmap_1(sK0,sK4(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK4(sK0))
    | ~ spl10_0 ),
    inference(resolution,[],[f863,f142])).

fof(f1925,plain,
    ( spl10_192
    | ~ spl10_100
    | spl10_341 ),
    inference(avatar_split_clause,[],[f1924,f1785,f570,f1067])).

fof(f1785,plain,
    ( spl10_341
  <=> ~ v1_xboole_0(u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_341])])).

fof(f1924,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK5)),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5)))
    | ~ spl10_100
    | ~ spl10_341 ),
    inference(forward_demodulation,[],[f1923,f571])).

fof(f1923,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK4(sK5))),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5)))
    | ~ spl10_341 ),
    inference(resolution,[],[f1786,f445])).

fof(f1786,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4(sK5)))
    | ~ spl10_341 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1920,plain,
    ( spl10_376
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1783,f1061,f1918])).

fof(f1918,plain,
    ( spl10_376
  <=> m1_subset_1(u1_struct_0(sK4(sK5)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_376])])).

fof(f1061,plain,
    ( spl10_190
  <=> u1_struct_0(sK4(sK5)) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f1783,plain,
    ( m1_subset_1(u1_struct_0(sK4(sK5)),k1_zfmisc_1(sK2))
    | ~ spl10_190 ),
    inference(superposition,[],[f107,f1062])).

fof(f1062,plain,
    ( u1_struct_0(sK4(sK5)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_190 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1913,plain,
    ( spl10_374
    | ~ spl10_190
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1906,f1272,f1061,f1911])).

fof(f1911,plain,
    ( spl10_374
  <=> r2_hidden(u1_struct_0(sK4(sK5)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_374])])).

fof(f1906,plain,
    ( r2_hidden(u1_struct_0(sK4(sK5)),k1_zfmisc_1(sK2))
    | ~ spl10_190
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1782,f1273])).

fof(f1782,plain,
    ( r2_hidden(u1_struct_0(sK4(sK5)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_190 ),
    inference(superposition,[],[f251,f1062])).

fof(f1905,plain,
    ( ~ spl10_373
    | ~ spl10_190
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1898,f1272,f1061,f1903])).

fof(f1903,plain,
    ( spl10_373
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_373])])).

fof(f1898,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK5)))
    | ~ spl10_190
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1781,f1273])).

fof(f1781,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK5)))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_190 ),
    inference(superposition,[],[f268,f1062])).

fof(f1897,plain,
    ( spl10_370
    | spl10_340
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1890,f1061,f1788,f1895])).

fof(f1895,plain,
    ( spl10_370
  <=> m1_subset_1(sK3(u1_struct_0(sK4(sK5))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_370])])).

fof(f1788,plain,
    ( spl10_340
  <=> v1_xboole_0(u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_340])])).

fof(f1890,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK5)))
    | m1_subset_1(sK3(u1_struct_0(sK4(sK5))),sK2)
    | ~ spl10_190 ),
    inference(forward_demodulation,[],[f1777,f1062])).

fof(f1777,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK5))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_190 ),
    inference(superposition,[],[f401,f1062])).

fof(f1889,plain,
    ( spl10_368
    | spl10_340
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1882,f1061,f1788,f1887])).

fof(f1887,plain,
    ( spl10_368
  <=> r2_hidden(sK3(u1_struct_0(sK4(sK5))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_368])])).

fof(f1882,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK5)))
    | r2_hidden(sK3(u1_struct_0(sK4(sK5))),sK2)
    | ~ spl10_190 ),
    inference(forward_demodulation,[],[f1776,f1062])).

fof(f1776,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4(sK5))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_190 ),
    inference(superposition,[],[f547,f1062])).

fof(f1881,plain,
    ( ~ spl10_367
    | ~ spl10_190
    | spl10_199 ),
    inference(avatar_split_clause,[],[f1774,f1084,f1061,f1879])).

fof(f1879,plain,
    ( spl10_367
  <=> u1_struct_0(sK7) != u1_struct_0(sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_367])])).

fof(f1084,plain,
    ( spl10_199
  <=> u1_struct_0(sK7) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_199])])).

fof(f1774,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK4(sK5))
    | ~ spl10_190
    | ~ spl10_199 ),
    inference(superposition,[],[f1085,f1062])).

fof(f1085,plain,
    ( u1_struct_0(sK7) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_199 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1874,plain,
    ( ~ spl10_365
    | ~ spl10_190
    | spl10_195 ),
    inference(avatar_split_clause,[],[f1773,f1071,f1061,f1872])).

fof(f1872,plain,
    ( spl10_365
  <=> u1_struct_0(sK5) != u1_struct_0(sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_365])])).

fof(f1071,plain,
    ( spl10_195
  <=> u1_struct_0(sK5) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_195])])).

fof(f1773,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK4(sK5))
    | ~ spl10_190
    | ~ spl10_195 ),
    inference(superposition,[],[f1072,f1062])).

fof(f1072,plain,
    ( u1_struct_0(sK5) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_195 ),
    inference(avatar_component_clause,[],[f1071])).

fof(f1867,plain,
    ( ~ spl10_363
    | spl10_187
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1772,f1061,f1045,f1865])).

fof(f1865,plain,
    ( spl10_363
  <=> u1_struct_0(sK4(sK1)) != u1_struct_0(sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_363])])).

fof(f1772,plain,
    ( u1_struct_0(sK4(sK1)) != u1_struct_0(sK4(sK5))
    | ~ spl10_187
    | ~ spl10_190 ),
    inference(superposition,[],[f1046,f1062])).

fof(f1860,plain,
    ( ~ spl10_361
    | spl10_183
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1771,f1061,f1032,f1858])).

fof(f1858,plain,
    ( spl10_361
  <=> u1_struct_0(sK4(sK0)) != u1_struct_0(sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_361])])).

fof(f1771,plain,
    ( u1_struct_0(sK4(sK0)) != u1_struct_0(sK4(sK5))
    | ~ spl10_183
    | ~ spl10_190 ),
    inference(superposition,[],[f1033,f1062])).

fof(f1853,plain,
    ( ~ spl10_359
    | spl10_179
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1770,f1061,f1019,f1851])).

fof(f1851,plain,
    ( spl10_359
  <=> u1_struct_0(sK0) != u1_struct_0(sK4(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_359])])).

fof(f1770,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK4(sK5))
    | ~ spl10_179
    | ~ spl10_190 ),
    inference(superposition,[],[f1020,f1062])).

fof(f1846,plain,
    ( ~ spl10_357
    | spl10_87
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1769,f1061,f497,f1844])).

fof(f1844,plain,
    ( spl10_357
  <=> u1_struct_0(sK4(sK5)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_357])])).

fof(f497,plain,
    ( spl10_87
  <=> sK2 != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f1769,plain,
    ( u1_struct_0(sK4(sK5)) != sK2
    | ~ spl10_87
    | ~ spl10_190 ),
    inference(superposition,[],[f498,f1062])).

fof(f498,plain,
    ( sK2 != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f497])).

fof(f1839,plain,
    ( ~ spl10_355
    | spl10_177
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1768,f1061,f987,f1837])).

fof(f1837,plain,
    ( spl10_355
  <=> ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_355])])).

fof(f987,plain,
    ( spl10_177
  <=> ~ sP9(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_177])])).

fof(f1768,plain,
    ( ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK5))))
    | ~ spl10_177
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f988])).

fof(f988,plain,
    ( ~ sP9(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_177 ),
    inference(avatar_component_clause,[],[f987])).

fof(f1832,plain,
    ( ~ spl10_353
    | spl10_167
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1767,f1061,f929,f1830])).

fof(f1767,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK5))))
    | ~ spl10_167
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f930])).

fof(f1825,plain,
    ( spl10_350
    | ~ spl10_164
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1766,f1061,f925,f1823])).

fof(f1823,plain,
    ( spl10_350
  <=> sP9(u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_350])])).

fof(f1766,plain,
    ( sP9(u1_struct_0(sK4(sK5)))
    | ~ spl10_164
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f926])).

fof(f1818,plain,
    ( ~ spl10_349
    | spl10_153
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1765,f1061,f847,f1816])).

fof(f1816,plain,
    ( spl10_349
  <=> ~ m1_subset_1(u1_struct_0(sK4(sK5)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_349])])).

fof(f847,plain,
    ( spl10_153
  <=> ~ m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f1765,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4(sK5)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_153
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f848])).

fof(f848,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_153 ),
    inference(avatar_component_clause,[],[f847])).

fof(f1811,plain,
    ( ~ spl10_347
    | spl10_151
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1764,f1061,f840,f1809])).

fof(f1809,plain,
    ( spl10_347
  <=> ~ r2_hidden(u1_struct_0(sK4(sK5)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_347])])).

fof(f840,plain,
    ( spl10_151
  <=> ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f1764,plain,
    ( ~ r2_hidden(u1_struct_0(sK4(sK5)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_151
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f841])).

fof(f841,plain,
    ( ~ r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_151 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1804,plain,
    ( ~ spl10_345
    | spl10_149
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1763,f1061,f836,f1802])).

fof(f1802,plain,
    ( spl10_345
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_345])])).

fof(f836,plain,
    ( spl10_149
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f1763,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK5)))
    | ~ spl10_149
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f837])).

fof(f837,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_149 ),
    inference(avatar_component_clause,[],[f836])).

fof(f1797,plain,
    ( ~ spl10_343
    | spl10_145
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1762,f1061,f821,f1795])).

fof(f1795,plain,
    ( spl10_343
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK4(sK5))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_343])])).

fof(f821,plain,
    ( spl10_145
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f1762,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK4(sK5))),u1_struct_0(sK0))
    | ~ spl10_145
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f822])).

fof(f822,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | ~ spl10_145 ),
    inference(avatar_component_clause,[],[f821])).

fof(f1790,plain,
    ( spl10_340
    | ~ spl10_118
    | ~ spl10_190 ),
    inference(avatar_split_clause,[],[f1760,f1061,f646,f1788])).

fof(f1760,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK5)))
    | ~ spl10_118
    | ~ spl10_190 ),
    inference(backward_demodulation,[],[f1062,f647])).

fof(f1755,plain,
    ( spl10_338
    | spl10_315 ),
    inference(avatar_split_clause,[],[f1748,f1655,f1753])).

fof(f1753,plain,
    ( spl10_338
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK1)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK1))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_338])])).

fof(f1655,plain,
    ( spl10_315
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_315])])).

fof(f1748,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK1)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK1))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK1))))
    | ~ spl10_315 ),
    inference(resolution,[],[f1656,f445])).

fof(f1656,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK1))))
    | ~ spl10_315 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f1747,plain,
    ( spl10_214
    | spl10_167 ),
    inference(avatar_split_clause,[],[f1746,f929,f1195])).

fof(f1746,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f1743,plain,
    ( spl10_188
    | ~ spl10_98
    | spl10_303 ),
    inference(avatar_split_clause,[],[f1742,f1610,f563,f1054])).

fof(f1610,plain,
    ( spl10_303
  <=> ~ v1_xboole_0(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_303])])).

fof(f1742,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK1)),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1)))
    | ~ spl10_98
    | ~ spl10_303 ),
    inference(forward_demodulation,[],[f1741,f564])).

fof(f1741,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK4(sK1))),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1)))
    | ~ spl10_303 ),
    inference(resolution,[],[f1611,f445])).

fof(f1611,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4(sK1)))
    | ~ spl10_303 ),
    inference(avatar_component_clause,[],[f1610])).

fof(f1738,plain,
    ( spl10_336
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1608,f1048,f1736])).

fof(f1736,plain,
    ( spl10_336
  <=> m1_subset_1(u1_struct_0(sK4(sK1)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_336])])).

fof(f1048,plain,
    ( spl10_186
  <=> u1_struct_0(sK4(sK1)) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_186])])).

fof(f1608,plain,
    ( m1_subset_1(u1_struct_0(sK4(sK1)),k1_zfmisc_1(sK2))
    | ~ spl10_186 ),
    inference(superposition,[],[f107,f1049])).

fof(f1049,plain,
    ( u1_struct_0(sK4(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_186 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f1731,plain,
    ( spl10_334
    | ~ spl10_186
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1724,f1272,f1048,f1729])).

fof(f1729,plain,
    ( spl10_334
  <=> r2_hidden(u1_struct_0(sK4(sK1)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_334])])).

fof(f1724,plain,
    ( r2_hidden(u1_struct_0(sK4(sK1)),k1_zfmisc_1(sK2))
    | ~ spl10_186
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1607,f1273])).

fof(f1607,plain,
    ( r2_hidden(u1_struct_0(sK4(sK1)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_186 ),
    inference(superposition,[],[f251,f1049])).

fof(f1723,plain,
    ( ~ spl10_333
    | ~ spl10_186
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1716,f1272,f1048,f1721])).

fof(f1721,plain,
    ( spl10_333
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_333])])).

fof(f1716,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK1)))
    | ~ spl10_186
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1606,f1273])).

fof(f1606,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_186 ),
    inference(superposition,[],[f268,f1049])).

fof(f1715,plain,
    ( spl10_330
    | spl10_302
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1708,f1048,f1613,f1713])).

fof(f1713,plain,
    ( spl10_330
  <=> m1_subset_1(sK3(u1_struct_0(sK4(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_330])])).

fof(f1613,plain,
    ( spl10_302
  <=> v1_xboole_0(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_302])])).

fof(f1708,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK1)))
    | m1_subset_1(sK3(u1_struct_0(sK4(sK1))),sK2)
    | ~ spl10_186 ),
    inference(forward_demodulation,[],[f1602,f1049])).

fof(f1602,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK1))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_186 ),
    inference(superposition,[],[f401,f1049])).

fof(f1707,plain,
    ( spl10_328
    | spl10_302
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1700,f1048,f1613,f1705])).

fof(f1705,plain,
    ( spl10_328
  <=> r2_hidden(sK3(u1_struct_0(sK4(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_328])])).

fof(f1700,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK1)))
    | r2_hidden(sK3(u1_struct_0(sK4(sK1))),sK2)
    | ~ spl10_186 ),
    inference(forward_demodulation,[],[f1601,f1049])).

fof(f1601,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4(sK1))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_186 ),
    inference(superposition,[],[f547,f1049])).

fof(f1699,plain,
    ( ~ spl10_327
    | ~ spl10_186
    | spl10_199 ),
    inference(avatar_split_clause,[],[f1599,f1084,f1048,f1697])).

fof(f1697,plain,
    ( spl10_327
  <=> u1_struct_0(sK7) != u1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_327])])).

fof(f1599,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK4(sK1))
    | ~ spl10_186
    | ~ spl10_199 ),
    inference(superposition,[],[f1085,f1049])).

fof(f1692,plain,
    ( ~ spl10_325
    | ~ spl10_186
    | spl10_195 ),
    inference(avatar_split_clause,[],[f1598,f1071,f1048,f1690])).

fof(f1690,plain,
    ( spl10_325
  <=> u1_struct_0(sK5) != u1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_325])])).

fof(f1598,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK4(sK1))
    | ~ spl10_186
    | ~ spl10_195 ),
    inference(superposition,[],[f1072,f1049])).

fof(f1685,plain,
    ( ~ spl10_323
    | spl10_183
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1597,f1048,f1032,f1683])).

fof(f1683,plain,
    ( spl10_323
  <=> u1_struct_0(sK4(sK0)) != u1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_323])])).

fof(f1597,plain,
    ( u1_struct_0(sK4(sK0)) != u1_struct_0(sK4(sK1))
    | ~ spl10_183
    | ~ spl10_186 ),
    inference(superposition,[],[f1033,f1049])).

fof(f1678,plain,
    ( ~ spl10_321
    | spl10_179
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1596,f1048,f1019,f1676])).

fof(f1676,plain,
    ( spl10_321
  <=> u1_struct_0(sK0) != u1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_321])])).

fof(f1596,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK4(sK1))
    | ~ spl10_179
    | ~ spl10_186 ),
    inference(superposition,[],[f1020,f1049])).

fof(f1671,plain,
    ( ~ spl10_319
    | spl10_87
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1595,f1048,f497,f1669])).

fof(f1669,plain,
    ( spl10_319
  <=> u1_struct_0(sK4(sK1)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_319])])).

fof(f1595,plain,
    ( u1_struct_0(sK4(sK1)) != sK2
    | ~ spl10_87
    | ~ spl10_186 ),
    inference(superposition,[],[f498,f1049])).

fof(f1664,plain,
    ( ~ spl10_317
    | spl10_177
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1594,f1048,f987,f1662])).

fof(f1662,plain,
    ( spl10_317
  <=> ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_317])])).

fof(f1594,plain,
    ( ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK1))))
    | ~ spl10_177
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f988])).

fof(f1657,plain,
    ( ~ spl10_315
    | spl10_167
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1593,f1048,f929,f1655])).

fof(f1593,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK1))))
    | ~ spl10_167
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f930])).

fof(f1650,plain,
    ( spl10_312
    | ~ spl10_164
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1592,f1048,f925,f1648])).

fof(f1648,plain,
    ( spl10_312
  <=> sP9(u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_312])])).

fof(f1592,plain,
    ( sP9(u1_struct_0(sK4(sK1)))
    | ~ spl10_164
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f926])).

fof(f1643,plain,
    ( ~ spl10_311
    | spl10_153
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1591,f1048,f847,f1641])).

fof(f1641,plain,
    ( spl10_311
  <=> ~ m1_subset_1(u1_struct_0(sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_311])])).

fof(f1591,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_153
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f848])).

fof(f1636,plain,
    ( ~ spl10_309
    | spl10_151
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1590,f1048,f840,f1634])).

fof(f1634,plain,
    ( spl10_309
  <=> ~ r2_hidden(u1_struct_0(sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_309])])).

fof(f1590,plain,
    ( ~ r2_hidden(u1_struct_0(sK4(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_151
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f841])).

fof(f1629,plain,
    ( ~ spl10_307
    | spl10_149
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1589,f1048,f836,f1627])).

fof(f1627,plain,
    ( spl10_307
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_307])])).

fof(f1589,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK1)))
    | ~ spl10_149
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f837])).

fof(f1622,plain,
    ( ~ spl10_305
    | spl10_145
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1588,f1048,f821,f1620])).

fof(f1620,plain,
    ( spl10_305
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK4(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_305])])).

fof(f1588,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK4(sK1))),u1_struct_0(sK0))
    | ~ spl10_145
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f822])).

fof(f1615,plain,
    ( spl10_302
    | ~ spl10_118
    | ~ spl10_186 ),
    inference(avatar_split_clause,[],[f1586,f1048,f646,f1613])).

fof(f1586,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK1)))
    | ~ spl10_118
    | ~ spl10_186 ),
    inference(backward_demodulation,[],[f1049,f647])).

fof(f1566,plain,
    ( spl10_300
    | spl10_279 ),
    inference(avatar_split_clause,[],[f1559,f1473,f1564])).

fof(f1564,plain,
    ( spl10_300
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK0)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_300])])).

fof(f1473,plain,
    ( spl10_279
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_279])])).

fof(f1559,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK4(sK0)))),sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))) = sK3(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_279 ),
    inference(resolution,[],[f1474,f445])).

fof(f1474,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_279 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1558,plain,
    ( spl10_214
    | spl10_167 ),
    inference(avatar_split_clause,[],[f1557,f929,f1195])).

fof(f1557,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f1554,plain,
    ( spl10_184
    | ~ spl10_96
    | spl10_267 ),
    inference(avatar_split_clause,[],[f1553,f1428,f556,f1041])).

fof(f1553,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | ~ spl10_96
    | ~ spl10_267 ),
    inference(forward_demodulation,[],[f1552,f557])).

fof(f1552,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK4(sK0))),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | ~ spl10_267 ),
    inference(resolution,[],[f1429,f445])).

fof(f1549,plain,
    ( spl10_298
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1426,f1035,f1547])).

fof(f1426,plain,
    ( m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_182 ),
    inference(superposition,[],[f107,f1036])).

fof(f1036,plain,
    ( u1_struct_0(sK4(sK0)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_182 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1542,plain,
    ( spl10_296
    | ~ spl10_182
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1535,f1272,f1035,f1540])).

fof(f1535,plain,
    ( r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | ~ spl10_182
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1425,f1273])).

fof(f1425,plain,
    ( r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_182 ),
    inference(superposition,[],[f251,f1036])).

fof(f1534,plain,
    ( ~ spl10_295
    | ~ spl10_182
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1527,f1272,f1035,f1532])).

fof(f1532,plain,
    ( spl10_295
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_295])])).

fof(f1527,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK0)))
    | ~ spl10_182
    | ~ spl10_233 ),
    inference(subsumption_resolution,[],[f1424,f1273])).

fof(f1424,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK4(sK0)))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_182 ),
    inference(superposition,[],[f268,f1036])).

fof(f1526,plain,
    ( spl10_292
    | spl10_266
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1519,f1035,f1431,f1524])).

fof(f1519,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_182 ),
    inference(forward_demodulation,[],[f1420,f1036])).

fof(f1420,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK4(sK0))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_182 ),
    inference(superposition,[],[f401,f1036])).

fof(f1518,plain,
    ( spl10_290
    | spl10_266
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1511,f1035,f1431,f1516])).

fof(f1511,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | ~ spl10_182 ),
    inference(forward_demodulation,[],[f1419,f1036])).

fof(f1419,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4(sK0))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_182 ),
    inference(superposition,[],[f547,f1036])).

fof(f1510,plain,
    ( ~ spl10_289
    | ~ spl10_182
    | spl10_199 ),
    inference(avatar_split_clause,[],[f1417,f1084,f1035,f1508])).

fof(f1508,plain,
    ( spl10_289
  <=> u1_struct_0(sK7) != u1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_289])])).

fof(f1417,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK4(sK0))
    | ~ spl10_182
    | ~ spl10_199 ),
    inference(superposition,[],[f1085,f1036])).

fof(f1503,plain,
    ( ~ spl10_287
    | ~ spl10_182
    | spl10_195 ),
    inference(avatar_split_clause,[],[f1416,f1071,f1035,f1501])).

fof(f1501,plain,
    ( spl10_287
  <=> u1_struct_0(sK5) != u1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_287])])).

fof(f1416,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK4(sK0))
    | ~ spl10_182
    | ~ spl10_195 ),
    inference(superposition,[],[f1072,f1036])).

fof(f1496,plain,
    ( ~ spl10_285
    | spl10_179
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1415,f1035,f1019,f1494])).

fof(f1494,plain,
    ( spl10_285
  <=> u1_struct_0(sK0) != u1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_285])])).

fof(f1415,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK4(sK0))
    | ~ spl10_179
    | ~ spl10_182 ),
    inference(superposition,[],[f1020,f1036])).

fof(f1489,plain,
    ( ~ spl10_283
    | spl10_87
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1414,f1035,f497,f1487])).

fof(f1487,plain,
    ( spl10_283
  <=> u1_struct_0(sK4(sK0)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_283])])).

fof(f1414,plain,
    ( u1_struct_0(sK4(sK0)) != sK2
    | ~ spl10_87
    | ~ spl10_182 ),
    inference(superposition,[],[f498,f1036])).

fof(f1482,plain,
    ( ~ spl10_281
    | spl10_177
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1413,f1035,f987,f1480])).

fof(f1480,plain,
    ( spl10_281
  <=> ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_281])])).

fof(f1413,plain,
    ( ~ sP9(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_177
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f988])).

fof(f1475,plain,
    ( ~ spl10_279
    | spl10_167
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1412,f1035,f929,f1473])).

fof(f1412,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4(sK0))))
    | ~ spl10_167
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f930])).

fof(f1468,plain,
    ( spl10_276
    | ~ spl10_164
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1411,f1035,f925,f1466])).

fof(f1411,plain,
    ( sP9(u1_struct_0(sK4(sK0)))
    | ~ spl10_164
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f926])).

fof(f1461,plain,
    ( ~ spl10_275
    | spl10_153
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1410,f1035,f847,f1459])).

fof(f1459,plain,
    ( spl10_275
  <=> ~ m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_275])])).

fof(f1410,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_153
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f848])).

fof(f1454,plain,
    ( ~ spl10_273
    | spl10_151
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1409,f1035,f840,f1452])).

fof(f1452,plain,
    ( spl10_273
  <=> ~ r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_273])])).

fof(f1409,plain,
    ( ~ r2_hidden(u1_struct_0(sK4(sK0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_151
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f841])).

fof(f1447,plain,
    ( ~ spl10_271
    | spl10_149
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1408,f1035,f836,f1445])).

fof(f1445,plain,
    ( spl10_271
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_271])])).

fof(f1408,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK4(sK0)))
    | ~ spl10_149
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f837])).

fof(f1440,plain,
    ( ~ spl10_269
    | spl10_145
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1407,f1035,f821,f1438])).

fof(f1438,plain,
    ( spl10_269
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_269])])).

fof(f1407,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK4(sK0))),u1_struct_0(sK0))
    | ~ spl10_145
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f822])).

fof(f1433,plain,
    ( spl10_266
    | ~ spl10_118
    | ~ spl10_182 ),
    inference(avatar_split_clause,[],[f1405,f1035,f646,f1431])).

fof(f1405,plain,
    ( v1_xboole_0(u1_struct_0(sK4(sK0)))
    | ~ spl10_118
    | ~ spl10_182 ),
    inference(backward_demodulation,[],[f1036,f647])).

fof(f1404,plain,
    ( spl10_252
    | spl10_264
    | ~ spl10_255
    | ~ spl10_259
    | ~ spl10_261
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f1390,f197,f190,f183,f1378,f1372,f1360,f1402,f1354])).

fof(f1354,plain,
    ( spl10_252
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_252])])).

fof(f1402,plain,
    ( spl10_264
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f1360,plain,
    ( spl10_255
  <=> ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_255])])).

fof(f1372,plain,
    ( spl10_259
  <=> ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_259])])).

fof(f1378,plain,
    ( spl10_261
  <=> ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_261])])).

fof(f1390,plain,
    ( ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),sK2)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))))
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f1182,f401])).

fof(f1182,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X3) )
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1181,f191])).

fof(f1181,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X3) )
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f1176,f198])).

fof(f1176,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,sK2)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X3) )
    | ~ spl10_12 ),
    inference(resolution,[],[f95,f184])).

fof(f1397,plain,
    ( spl10_262
    | ~ spl10_245
    | ~ spl10_249
    | ~ spl10_251
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f1389,f197,f190,f183,f1347,f1341,f1329,f1395])).

fof(f1395,plain,
    ( spl10_262
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_262])])).

fof(f1329,plain,
    ( spl10_245
  <=> ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_245])])).

fof(f1341,plain,
    ( spl10_249
  <=> ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_249])])).

fof(f1347,plain,
    ( spl10_251
  <=> ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_251])])).

fof(f1389,plain,
    ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f1182,f107])).

fof(f1382,plain,
    ( spl10_214
    | spl10_167 ),
    inference(avatar_split_clause,[],[f1381,f929,f1195])).

fof(f1381,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f1380,plain,
    ( spl10_252
    | ~ spl10_255
    | spl10_256
    | ~ spl10_259
    | ~ spl10_261
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f1324,f197,f190,f183,f1378,f1372,f1366,f1360,f1354])).

fof(f1366,plain,
    ( spl10_256
  <=> sK2 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_256])])).

fof(f1324,plain,
    ( ~ v1_funct_2(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))))
    | sK2 = sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f975,f401])).

fof(f1349,plain,
    ( ~ spl10_245
    | spl10_246
    | ~ spl10_249
    | ~ spl10_251
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f1323,f197,f190,f183,f1347,f1341,f1335,f1329])).

fof(f1335,plain,
    ( spl10_246
  <=> sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_246])])).

fof(f1323,plain,
    ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2)
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(resolution,[],[f975,f107])).

fof(f1320,plain,
    ( spl10_242
    | spl10_221 ),
    inference(avatar_split_clause,[],[f1313,f1231,f1318])).

fof(f1318,plain,
    ( spl10_242
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK5))),sK3(k1_zfmisc_1(u1_struct_0(sK5)))) = sK3(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_242])])).

fof(f1231,plain,
    ( spl10_221
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_221])])).

fof(f1313,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK5))),sK3(k1_zfmisc_1(u1_struct_0(sK5)))) = sK3(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl10_221 ),
    inference(resolution,[],[f1232,f445])).

fof(f1232,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl10_221 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1308,plain,
    ( spl10_240
    | spl10_233 ),
    inference(avatar_split_clause,[],[f1301,f1272,f1306])).

fof(f1306,plain,
    ( spl10_240
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(sK2)),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_240])])).

fof(f1301,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK2)),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_233 ),
    inference(resolution,[],[f1273,f445])).

fof(f1300,plain,
    ( spl10_196
    | ~ spl10_56
    | spl10_217 ),
    inference(avatar_split_clause,[],[f1299,f1214,f359,f1080])).

fof(f1080,plain,
    ( spl10_196
  <=> k1_funct_1(k3_struct_0(sK5),sK3(u1_struct_0(sK5))) = sK3(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_196])])).

fof(f359,plain,
    ( spl10_56
  <=> k3_struct_0(sK5) = k6_relat_1(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f1214,plain,
    ( spl10_217
  <=> ~ v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_217])])).

fof(f1299,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK3(u1_struct_0(sK5))) = sK3(u1_struct_0(sK5))
    | ~ spl10_56
    | ~ spl10_217 ),
    inference(forward_demodulation,[],[f1298,f360])).

fof(f360,plain,
    ( k3_struct_0(sK5) = k6_relat_1(u1_struct_0(sK5))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f359])).

fof(f1298,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK5)),sK3(u1_struct_0(sK5))) = sK3(u1_struct_0(sK5))
    | ~ spl10_217 ),
    inference(resolution,[],[f1215,f445])).

fof(f1215,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl10_217 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1297,plain,
    ( spl10_238
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1212,f1074,f1295])).

fof(f1295,plain,
    ( spl10_238
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_238])])).

fof(f1074,plain,
    ( spl10_194
  <=> u1_struct_0(sK5) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f1212,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK2))
    | ~ spl10_194 ),
    inference(superposition,[],[f107,f1075])).

fof(f1075,plain,
    ( u1_struct_0(sK5) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_194 ),
    inference(avatar_component_clause,[],[f1074])).

fof(f1290,plain,
    ( spl10_232
    | spl10_236
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1211,f1074,f1288,f1275])).

fof(f1288,plain,
    ( spl10_236
  <=> r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_236])])).

fof(f1211,plain,
    ( r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_194 ),
    inference(superposition,[],[f251,f1075])).

fof(f1283,plain,
    ( spl10_232
    | ~ spl10_235
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1210,f1074,f1281,f1275])).

fof(f1281,plain,
    ( spl10_235
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_235])])).

fof(f1210,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),u1_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_194 ),
    inference(superposition,[],[f268,f1075])).

fof(f1270,plain,
    ( spl10_230
    | spl10_216
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1263,f1074,f1217,f1268])).

fof(f1268,plain,
    ( spl10_230
  <=> m1_subset_1(sK3(u1_struct_0(sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_230])])).

fof(f1217,plain,
    ( spl10_216
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f1263,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | m1_subset_1(sK3(u1_struct_0(sK5)),sK2)
    | ~ spl10_194 ),
    inference(forward_demodulation,[],[f1206,f1075])).

fof(f1206,plain,
    ( m1_subset_1(sK3(u1_struct_0(sK5)),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_194 ),
    inference(superposition,[],[f401,f1075])).

fof(f1262,plain,
    ( spl10_228
    | spl10_216
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1255,f1074,f1217,f1260])).

fof(f1260,plain,
    ( spl10_228
  <=> r2_hidden(sK3(u1_struct_0(sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f1255,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | r2_hidden(sK3(u1_struct_0(sK5)),sK2)
    | ~ spl10_194 ),
    inference(forward_demodulation,[],[f1205,f1075])).

fof(f1205,plain,
    ( r2_hidden(sK3(u1_struct_0(sK5)),sK2)
    | v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_194 ),
    inference(superposition,[],[f547,f1075])).

fof(f1254,plain,
    ( ~ spl10_227
    | spl10_179
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1203,f1074,f1019,f1252])).

fof(f1252,plain,
    ( spl10_227
  <=> u1_struct_0(sK0) != u1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_227])])).

fof(f1203,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK5)
    | ~ spl10_179
    | ~ spl10_194 ),
    inference(superposition,[],[f1020,f1075])).

fof(f1247,plain,
    ( ~ spl10_225
    | spl10_87
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1202,f1074,f497,f1245])).

fof(f1245,plain,
    ( spl10_225
  <=> u1_struct_0(sK5) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_225])])).

fof(f1202,plain,
    ( u1_struct_0(sK5) != sK2
    | ~ spl10_87
    | ~ spl10_194 ),
    inference(superposition,[],[f498,f1075])).

fof(f1240,plain,
    ( ~ spl10_223
    | spl10_177
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1201,f1074,f987,f1238])).

fof(f1238,plain,
    ( spl10_223
  <=> ~ sP9(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_223])])).

fof(f1201,plain,
    ( ~ sP9(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl10_177
    | ~ spl10_194 ),
    inference(backward_demodulation,[],[f1075,f988])).

fof(f1233,plain,
    ( ~ spl10_221
    | spl10_167
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1200,f1074,f929,f1231])).

fof(f1200,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl10_167
    | ~ spl10_194 ),
    inference(backward_demodulation,[],[f1075,f930])).

fof(f1226,plain,
    ( spl10_218
    | ~ spl10_164
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1199,f1074,f925,f1224])).

fof(f1224,plain,
    ( spl10_218
  <=> sP9(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f1199,plain,
    ( sP9(u1_struct_0(sK5))
    | ~ spl10_164
    | ~ spl10_194 ),
    inference(backward_demodulation,[],[f1075,f926])).

fof(f1219,plain,
    ( spl10_216
    | ~ spl10_118
    | ~ spl10_194 ),
    inference(avatar_split_clause,[],[f1198,f1074,f646,f1217])).

fof(f1198,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ spl10_118
    | ~ spl10_194 ),
    inference(backward_demodulation,[],[f1075,f647])).

fof(f1197,plain,
    ( spl10_214
    | spl10_167 ),
    inference(avatar_split_clause,[],[f1190,f929,f1195])).

fof(f1190,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f1185,plain,
    ( spl10_180
    | ~ spl10_52
    | spl10_209 ),
    inference(avatar_split_clause,[],[f1184,f1151,f345,f1028])).

fof(f1184,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | ~ spl10_52
    | ~ spl10_209 ),
    inference(forward_demodulation,[],[f1183,f346])).

fof(f1183,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | ~ spl10_209 ),
    inference(resolution,[],[f1152,f445])).

fof(f1172,plain,
    ( spl10_145
    | ~ spl10_178 ),
    inference(avatar_contradiction_clause,[],[f1171])).

fof(f1171,plain,
    ( $false
    | ~ spl10_145
    | ~ spl10_178 ),
    inference(subsumption_resolution,[],[f1112,f107])).

fof(f1112,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_145
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f822])).

fof(f1023,plain,
    ( u1_struct_0(sK0) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_178 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1022,plain,
    ( spl10_178
  <=> u1_struct_0(sK0) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f1170,plain,
    ( ~ spl10_213
    | spl10_143
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f1111,f1022,f814,f1168])).

fof(f1168,plain,
    ( spl10_213
  <=> k1_funct_1(sK2,sK3(u1_struct_0(sK0))) != sK3(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_213])])).

fof(f814,plain,
    ( spl10_143
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f1111,plain,
    ( k1_funct_1(sK2,sK3(u1_struct_0(sK0))) != sK3(u1_struct_0(sK0))
    | ~ spl10_143
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f815])).

fof(f815,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_143 ),
    inference(avatar_component_clause,[],[f814])).

fof(f1163,plain,
    ( ~ spl10_211
    | spl10_141
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f1110,f1022,f784,f1161])).

fof(f1161,plain,
    ( spl10_211
  <=> u1_struct_0(sK0) != sK3(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_211])])).

fof(f784,plain,
    ( spl10_141
  <=> sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f1110,plain,
    ( u1_struct_0(sK0) != sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_141
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f785])).

fof(f785,plain,
    ( sK3(k1_zfmisc_1(sK2)) != sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_141 ),
    inference(avatar_component_clause,[],[f784])).

fof(f1156,plain,
    ( spl10_208
    | ~ spl10_118
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f1105,f1022,f646,f1154])).

fof(f1105,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_118
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f647])).

fof(f1149,plain,
    ( spl10_206
    | ~ spl10_116
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f1104,f1022,f640,f1147])).

fof(f1147,plain,
    ( spl10_206
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f640,plain,
    ( spl10_116
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(sK2)))) = sK3(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f1104,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | ~ spl10_116
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f641])).

fof(f641,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(sK2)))) = sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f640])).

fof(f1142,plain,
    ( ~ spl10_205
    | spl10_83
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f1103,f1022,f479,f1140])).

fof(f1140,plain,
    ( spl10_205
  <=> u1_struct_0(sK0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_205])])).

fof(f479,plain,
    ( spl10_83
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f1103,plain,
    ( u1_struct_0(sK0) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_83
    | ~ spl10_178 ),
    inference(backward_demodulation,[],[f1023,f480])).

fof(f480,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != sK3(k1_zfmisc_1(sK2))
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1102,plain,
    ( spl10_202
    | spl10_174
    | ~ spl10_118
    | ~ spl10_162 ),
    inference(avatar_split_clause,[],[f1017,f905,f646,f965,f1100])).

fof(f1100,plain,
    ( spl10_202
  <=> k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_202])])).

fof(f1017,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_118
    | ~ spl10_162 ),
    inference(superposition,[],[f778,f906])).

fof(f1095,plain,
    ( spl10_198
    | spl10_200
    | ~ spl10_58
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1016,f646,f366,f1093,f1087])).

fof(f1087,plain,
    ( spl10_198
  <=> u1_struct_0(sK7) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_198])])).

fof(f1093,plain,
    ( spl10_200
  <=> k1_funct_1(k3_struct_0(sK7),sK3(u1_struct_0(sK7))) = sK3(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_200])])).

fof(f366,plain,
    ( spl10_58
  <=> k3_struct_0(sK7) = k6_relat_1(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f1016,plain,
    ( k1_funct_1(k3_struct_0(sK7),sK3(u1_struct_0(sK7))) = sK3(u1_struct_0(sK7))
    | u1_struct_0(sK7) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_58
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f367])).

fof(f367,plain,
    ( k3_struct_0(sK7) = k6_relat_1(u1_struct_0(sK7))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f366])).

fof(f1082,plain,
    ( spl10_194
    | spl10_196
    | ~ spl10_56
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1015,f646,f359,f1080,f1074])).

fof(f1015,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK3(u1_struct_0(sK5))) = sK3(u1_struct_0(sK5))
    | u1_struct_0(sK5) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_56
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f360])).

fof(f1069,plain,
    ( spl10_190
    | spl10_192
    | ~ spl10_100
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1014,f646,f570,f1067,f1061])).

fof(f1014,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK5)),sK3(u1_struct_0(sK4(sK5)))) = sK3(u1_struct_0(sK4(sK5)))
    | u1_struct_0(sK4(sK5)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_100
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f571])).

fof(f1056,plain,
    ( spl10_186
    | spl10_188
    | ~ spl10_98
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1013,f646,f563,f1054,f1048])).

fof(f1013,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK1)),sK3(u1_struct_0(sK4(sK1)))) = sK3(u1_struct_0(sK4(sK1)))
    | u1_struct_0(sK4(sK1)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_98
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f564])).

fof(f1043,plain,
    ( spl10_182
    | spl10_184
    | ~ spl10_96
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1012,f646,f556,f1041,f1035])).

fof(f1012,plain,
    ( k1_funct_1(k3_struct_0(sK4(sK0)),sK3(u1_struct_0(sK4(sK0)))) = sK3(u1_struct_0(sK4(sK0)))
    | u1_struct_0(sK4(sK0)) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_96
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f557])).

fof(f1030,plain,
    ( spl10_178
    | spl10_180
    | ~ spl10_52
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f1010,f646,f345,f1028,f1022])).

fof(f1010,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK3(u1_struct_0(sK0))) = sK3(u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_52
    | ~ spl10_118 ),
    inference(superposition,[],[f778,f346])).

fof(f989,plain,
    ( ~ spl10_177
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f979,f945,f987])).

fof(f979,plain,
    ( ~ sP9(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_170 ),
    inference(resolution,[],[f946,f135])).

fof(f982,plain,
    ( spl10_172
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f978,f945,f952])).

fof(f978,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_170 ),
    inference(resolution,[],[f946,f105])).

fof(f981,plain,
    ( spl10_174
    | ~ spl10_170 ),
    inference(avatar_split_clause,[],[f976,f945,f965])).

fof(f976,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_170 ),
    inference(resolution,[],[f946,f128])).

fof(f967,plain,
    ( spl10_174
    | ~ spl10_162
    | spl10_167 ),
    inference(avatar_split_clause,[],[f960,f929,f905,f965])).

fof(f960,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK2))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_162
    | ~ spl10_167 ),
    inference(forward_demodulation,[],[f959,f906])).

fof(f959,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_167 ),
    inference(resolution,[],[f930,f445])).

fof(f954,plain,
    ( spl10_172
    | ~ spl10_162 ),
    inference(avatar_split_clause,[],[f918,f905,f952])).

fof(f918,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_162 ),
    inference(superposition,[],[f107,f906])).

fof(f947,plain,
    ( spl10_166
    | spl10_170
    | ~ spl10_162 ),
    inference(avatar_split_clause,[],[f917,f905,f945,f932])).

fof(f932,plain,
    ( spl10_166
  <=> v1_xboole_0(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f917,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | v1_xboole_0(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_162 ),
    inference(superposition,[],[f251,f906])).

fof(f940,plain,
    ( spl10_166
    | ~ spl10_169
    | ~ spl10_162 ),
    inference(avatar_split_clause,[],[f916,f905,f938,f932])).

fof(f938,plain,
    ( spl10_169
  <=> ~ r2_hidden(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_169])])).

fof(f916,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))),sK3(k1_zfmisc_1(sK2)))
    | v1_xboole_0(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_162 ),
    inference(superposition,[],[f268,f906])).

fof(f927,plain,
    ( spl10_164
    | ~ spl10_118
    | ~ spl10_162 ),
    inference(avatar_split_clause,[],[f920,f905,f646,f925])).

fof(f920,plain,
    ( sP9(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_118
    | ~ spl10_162 ),
    inference(subsumption_resolution,[],[f914,f647])).

fof(f914,plain,
    ( sP9(sK3(k1_zfmisc_1(sK2)))
    | ~ v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_162 ),
    inference(superposition,[],[f403,f906])).

fof(f909,plain,
    ( spl10_130
    | spl10_89 ),
    inference(avatar_split_clause,[],[f908,f516,f706])).

fof(f706,plain,
    ( spl10_130
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f516,plain,
    ( spl10_89
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f908,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_89 ),
    inference(resolution,[],[f517,f445])).

fof(f517,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f516])).

fof(f907,plain,
    ( spl10_162
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f893,f646,f905])).

fof(f893,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(sK2))))
    | ~ spl10_118 ),
    inference(resolution,[],[f780,f647])).

fof(f900,plain,
    ( spl10_160
    | ~ spl10_88
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f890,f646,f519,f898])).

fof(f898,plain,
    ( spl10_160
  <=> sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_160])])).

fof(f519,plain,
    ( spl10_88
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f890,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))))
    | ~ spl10_88
    | ~ spl10_118 ),
    inference(resolution,[],[f780,f520])).

fof(f520,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f519])).

fof(f887,plain,
    ( spl10_158
    | ~ spl10_88
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f878,f646,f519,f885])).

fof(f885,plain,
    ( spl10_158
  <=> k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f878,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_88
    | ~ spl10_118 ),
    inference(resolution,[],[f520,f756])).

fof(f877,plain,
    ( spl10_136
    | spl10_115 ),
    inference(avatar_split_clause,[],[f876,f630,f727])).

fof(f727,plain,
    ( spl10_136
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f876,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_115 ),
    inference(resolution,[],[f631,f445])).

fof(f873,plain,
    ( spl10_156
    | ~ spl10_0
    | ~ spl10_2
    | spl10_5
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f866,f162,f155,f148,f141,f871])).

fof(f866,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f865,f156])).

fof(f865,plain,
    ( v2_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f864,f142])).

fof(f864,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f861,f149])).

fof(f861,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f100,f163])).

fof(f860,plain,
    ( spl10_154
    | spl10_147 ),
    inference(avatar_split_clause,[],[f853,f827,f858])).

fof(f827,plain,
    ( spl10_147
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).

fof(f853,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(u1_struct_0(sK1))),sK3(k1_zfmisc_1(u1_struct_0(sK1)))) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_147 ),
    inference(resolution,[],[f828,f445])).

fof(f828,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_147 ),
    inference(avatar_component_clause,[],[f827])).

fof(f852,plain,
    ( spl10_152
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f809,f787,f850])).

fof(f809,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_140 ),
    inference(superposition,[],[f107,f788])).

fof(f845,plain,
    ( spl10_146
    | spl10_150
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f808,f787,f843,f830])).

fof(f808,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_140 ),
    inference(superposition,[],[f251,f788])).

fof(f838,plain,
    ( spl10_146
    | ~ spl10_149
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f807,f787,f836,f830])).

fof(f807,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),sK3(k1_zfmisc_1(sK2)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_140 ),
    inference(superposition,[],[f268,f788])).

fof(f823,plain,
    ( ~ spl10_145
    | spl10_113
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f799,f787,f627,f821])).

fof(f627,plain,
    ( spl10_113
  <=> ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f799,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | ~ spl10_113
    | ~ spl10_140 ),
    inference(backward_demodulation,[],[f788,f628])).

fof(f628,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl10_113 ),
    inference(avatar_component_clause,[],[f627])).

fof(f816,plain,
    ( ~ spl10_143
    | spl10_111
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f798,f787,f618,f814])).

fof(f618,plain,
    ( spl10_111
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f798,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(sK2)))) != sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_111
    | ~ spl10_140 ),
    inference(backward_demodulation,[],[f788,f619])).

fof(f619,plain,
    ( k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) != sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_111 ),
    inference(avatar_component_clause,[],[f618])).

fof(f795,plain,
    ( spl10_140
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f793,f646,f633,f787])).

fof(f793,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f758,f647])).

fof(f758,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK3(k1_zfmisc_1(u1_struct_0(sK1))) = X1 )
    | ~ spl10_114 ),
    inference(resolution,[],[f634,f122])).

fof(f789,plain,
    ( spl10_140
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f782,f646,f633,f787])).

fof(f782,plain,
    ( sK3(k1_zfmisc_1(sK2)) = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_114
    | ~ spl10_118 ),
    inference(resolution,[],[f756,f634])).

fof(f777,plain,
    ( spl10_126
    | spl10_41 ),
    inference(avatar_split_clause,[],[f776,f295,f692])).

fof(f692,plain,
    ( spl10_126
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f776,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_41 ),
    inference(resolution,[],[f296,f445])).

fof(f775,plain,
    ( spl10_132
    | spl10_79 ),
    inference(avatar_split_clause,[],[f774,f463,f713])).

fof(f713,plain,
    ( spl10_132
  <=> k1_funct_1(k6_relat_1(sK2),sK3(sK2)) = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f774,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK3(sK2)) = sK3(sK2)
    | ~ spl10_79 ),
    inference(resolution,[],[f464,f445])).

fof(f773,plain,
    ( spl10_78
    | ~ spl10_120 ),
    inference(avatar_split_clause,[],[f745,f656,f466])).

fof(f466,plain,
    ( spl10_78
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f656,plain,
    ( spl10_120
  <=> sP9(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_120])])).

fof(f745,plain,
    ( v1_xboole_0(sK2)
    | ~ spl10_120 ),
    inference(resolution,[],[f657,f270])).

fof(f657,plain,
    ( sP9(sK2)
    | ~ spl10_120 ),
    inference(avatar_component_clause,[],[f656])).

fof(f772,plain,
    ( spl10_138
    | ~ spl10_78
    | ~ spl10_114 ),
    inference(avatar_split_clause,[],[f764,f633,f466,f770])).

fof(f770,plain,
    ( spl10_138
  <=> sK2 = sK3(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f764,plain,
    ( sK2 = sK3(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_78
    | ~ spl10_114 ),
    inference(resolution,[],[f734,f634])).

fof(f734,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK2 = X1 )
    | ~ spl10_78 ),
    inference(resolution,[],[f467,f122])).

fof(f467,plain,
    ( v1_xboole_0(sK2)
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f466])).

fof(f765,plain,
    ( spl10_86
    | ~ spl10_78
    | ~ spl10_118 ),
    inference(avatar_split_clause,[],[f763,f646,f466,f500])).

fof(f500,plain,
    ( spl10_86
  <=> sK2 = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f763,plain,
    ( sK2 = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_78
    | ~ spl10_118 ),
    inference(resolution,[],[f734,f647])).

fof(f754,plain,
    ( spl10_124
    | spl10_39
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f753,f352,f285,f685])).

fof(f685,plain,
    ( spl10_124
  <=> k1_funct_1(k3_struct_0(sK1),sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f753,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1))
    | ~ spl10_39
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f752,f353])).

fof(f752,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK1)),sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1))
    | ~ spl10_39 ),
    inference(resolution,[],[f286,f445])).

fof(f751,plain,
    ( spl10_9
    | ~ spl10_28
    | ~ spl10_38 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_28
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f749,f170])).

fof(f749,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_28
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f746,f247])).

fof(f746,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_38 ),
    inference(resolution,[],[f289,f111])).

fof(f289,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl10_38
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f732,plain,
    ( spl10_120
    | ~ spl10_41
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f402,f183,f295,f656])).

fof(f402,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | sP9(sK2)
    | ~ spl10_12 ),
    inference(resolution,[],[f134,f184])).

fof(f731,plain,
    ( ~ spl10_41
    | ~ spl10_12
    | spl10_121 ),
    inference(avatar_split_clause,[],[f730,f659,f183,f295])).

fof(f659,plain,
    ( spl10_121
  <=> ~ sP9(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f730,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_12
    | ~ spl10_121 ),
    inference(subsumption_resolution,[],[f402,f660])).

fof(f660,plain,
    ( ~ sP9(sK2)
    | ~ spl10_121 ),
    inference(avatar_component_clause,[],[f659])).

fof(f729,plain,
    ( spl10_136
    | spl10_115 ),
    inference(avatar_split_clause,[],[f679,f630,f727])).

fof(f679,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl10_115 ),
    inference(resolution,[],[f445,f631])).

fof(f722,plain,
    ( spl10_134
    | spl10_119 ),
    inference(avatar_split_clause,[],[f678,f643,f720])).

fof(f720,plain,
    ( spl10_134
  <=> k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2)))) = sK3(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f643,plain,
    ( spl10_119
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f678,plain,
    ( k1_funct_1(k6_relat_1(sK3(k1_zfmisc_1(sK2))),sK3(sK3(k1_zfmisc_1(sK2)))) = sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_119 ),
    inference(resolution,[],[f445,f644])).

fof(f644,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_119 ),
    inference(avatar_component_clause,[],[f643])).

fof(f715,plain,
    ( spl10_132
    | spl10_79 ),
    inference(avatar_split_clause,[],[f677,f463,f713])).

fof(f677,plain,
    ( k1_funct_1(k6_relat_1(sK2),sK3(sK2)) = sK3(sK2)
    | ~ spl10_79 ),
    inference(resolution,[],[f445,f464])).

fof(f708,plain,
    ( spl10_130
    | spl10_89 ),
    inference(avatar_split_clause,[],[f676,f516,f706])).

fof(f676,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_89 ),
    inference(resolution,[],[f445,f517])).

fof(f701,plain,
    ( spl10_128
    | spl10_33 ),
    inference(avatar_split_clause,[],[f675,f259,f699])).

fof(f699,plain,
    ( spl10_128
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f675,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) = sK3(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_33 ),
    inference(resolution,[],[f445,f260])).

fof(f694,plain,
    ( spl10_126
    | spl10_41 ),
    inference(avatar_split_clause,[],[f674,f295,f692])).

fof(f674,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK3(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_41 ),
    inference(resolution,[],[f445,f296])).

fof(f687,plain,
    ( spl10_124
    | spl10_39
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f680,f352,f285,f685])).

fof(f680,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1))
    | ~ spl10_39
    | ~ spl10_54 ),
    inference(forward_demodulation,[],[f673,f353])).

fof(f673,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK1)),sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1))
    | ~ spl10_39 ),
    inference(resolution,[],[f445,f286])).

fof(f668,plain,
    ( ~ spl10_123
    | spl10_115 ),
    inference(avatar_split_clause,[],[f652,f630,f666])).

fof(f666,plain,
    ( spl10_123
  <=> ~ sP9(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f652,plain,
    ( ~ sP9(u1_struct_0(sK1))
    | ~ spl10_115 ),
    inference(resolution,[],[f612,f631])).

fof(f661,plain,
    ( ~ spl10_121
    | spl10_119 ),
    inference(avatar_split_clause,[],[f651,f643,f659])).

fof(f651,plain,
    ( ~ sP9(sK2)
    | ~ spl10_119 ),
    inference(resolution,[],[f612,f644])).

fof(f648,plain,
    ( spl10_116
    | spl10_118
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f615,f301,f646,f640])).

fof(f615,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(sK2)))
    | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK3(k1_zfmisc_1(sK2)))) = sK3(sK3(k1_zfmisc_1(sK2)))
    | ~ spl10_42 ),
    inference(resolution,[],[f547,f446])).

fof(f446,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X1) = X1 )
    | ~ spl10_42 ),
    inference(resolution,[],[f128,f302])).

fof(f635,plain,
    ( spl10_110
    | ~ spl10_113
    | spl10_114 ),
    inference(avatar_split_clause,[],[f614,f633,f627,f621])).

fof(f621,plain,
    ( spl10_110
  <=> k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f614,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1))))) = sK3(sK3(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f547,f83])).

fof(f608,plain,
    ( spl10_108
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f601,f570,f606])).

fof(f606,plain,
    ( spl10_108
  <=> v1_relat_1(k3_struct_0(sK4(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f601,plain,
    ( v1_relat_1(k3_struct_0(sK4(sK5)))
    | ~ spl10_100 ),
    inference(superposition,[],[f129,f571])).

fof(f129,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',dt_k6_relat_1)).

fof(f600,plain,
    ( spl10_106
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f593,f197,f190,f183,f598])).

fof(f598,plain,
    ( spl10_106
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f593,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f592,f198])).

fof(f592,plain,
    ( ~ v1_funct_1(sK2)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ spl10_12
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f589,f191])).

fof(f589,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK2)
    | ~ spl10_12 ),
    inference(resolution,[],[f136,f184])).

fof(f588,plain,
    ( spl10_104
    | ~ spl10_98 ),
    inference(avatar_split_clause,[],[f581,f563,f586])).

fof(f586,plain,
    ( spl10_104
  <=> v1_relat_1(k3_struct_0(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f581,plain,
    ( v1_relat_1(k3_struct_0(sK4(sK1)))
    | ~ spl10_98 ),
    inference(superposition,[],[f129,f564])).

fof(f580,plain,
    ( spl10_102
    | ~ spl10_96 ),
    inference(avatar_split_clause,[],[f573,f556,f578])).

fof(f578,plain,
    ( spl10_102
  <=> v1_relat_1(k3_struct_0(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f573,plain,
    ( v1_relat_1(k3_struct_0(sK4(sK0)))
    | ~ spl10_96 ),
    inference(superposition,[],[f129,f557])).

fof(f572,plain,
    ( spl10_100
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f551,f204,f570])).

fof(f551,plain,
    ( k3_struct_0(sK4(sK5)) = k6_relat_1(u1_struct_0(sK4(sK5)))
    | ~ spl10_18 ),
    inference(resolution,[],[f338,f205])).

fof(f338,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k3_struct_0(sK4(X0)) = k6_relat_1(u1_struct_0(sK4(X0))) ) ),
    inference(resolution,[],[f130,f249])).

fof(f130,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0)) ) ),
    inference(definition_unfolding,[],[f121,f127])).

fof(f127,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',redefinition_k6_partfun1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',d4_struct_0)).

fof(f565,plain,
    ( spl10_98
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f549,f238,f563])).

fof(f549,plain,
    ( k3_struct_0(sK4(sK1)) = k6_relat_1(u1_struct_0(sK4(sK1)))
    | ~ spl10_26 ),
    inference(resolution,[],[f338,f239])).

fof(f558,plain,
    ( spl10_96
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f548,f141,f556])).

fof(f548,plain,
    ( k3_struct_0(sK4(sK0)) = k6_relat_1(u1_struct_0(sK4(sK0)))
    | ~ spl10_0 ),
    inference(resolution,[],[f338,f142])).

fof(f541,plain,
    ( spl10_94
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f514,f413,f539])).

fof(f539,plain,
    ( spl10_94
  <=> m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f413,plain,
    ( spl10_68
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f514,plain,
    ( m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_68 ),
    inference(superposition,[],[f107,f414])).

fof(f414,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f413])).

fof(f534,plain,
    ( spl10_88
    | spl10_92
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f513,f413,f532,f519])).

fof(f532,plain,
    ( spl10_92
  <=> r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f513,plain,
    ( r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_68 ),
    inference(superposition,[],[f251,f414])).

fof(f527,plain,
    ( spl10_88
    | ~ spl10_91
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f512,f413,f525,f519])).

fof(f525,plain,
    ( spl10_91
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f512,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_68 ),
    inference(superposition,[],[f268,f414])).

fof(f508,plain,
    ( spl10_76
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f503,f256,f452])).

fof(f452,plain,
    ( spl10_76
  <=> k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f256,plain,
    ( spl10_30
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f503,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2) = sK2
    | ~ spl10_30 ),
    inference(resolution,[],[f257,f128])).

fof(f257,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f256])).

fof(f502,plain,
    ( spl10_86
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f495,f466,f500])).

fof(f495,plain,
    ( sK2 = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_78 ),
    inference(resolution,[],[f492,f467])).

fof(f492,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = sK3(k1_zfmisc_1(X0)) )
    | ~ spl10_78 ),
    inference(resolution,[],[f477,f404])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = X0 )
    | ~ spl10_78 ),
    inference(resolution,[],[f467,f122])).

fof(f491,plain,
    ( spl10_84
    | ~ spl10_32
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f476,f466,f262,f489])).

fof(f489,plain,
    ( spl10_84
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f262,plain,
    ( spl10_32
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f476,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK2
    | ~ spl10_32
    | ~ spl10_78 ),
    inference(resolution,[],[f467,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = X0 )
    | ~ spl10_32 ),
    inference(resolution,[],[f263,f122])).

fof(f263,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f262])).

fof(f484,plain,
    ( spl10_82
    | ~ spl10_32
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f475,f466,f262,f482])).

fof(f482,plain,
    ( spl10_82
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f475,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(sK2))
    | ~ spl10_32
    | ~ spl10_78 ),
    inference(resolution,[],[f467,f456])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(X0)) )
    | ~ spl10_32 ),
    inference(resolution,[],[f455,f404])).

fof(f474,plain,
    ( spl10_78
    | spl10_80
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f461,f301,f472,f466])).

fof(f472,plain,
    ( spl10_80
  <=> k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK2)) = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f461,plain,
    ( k1_funct_1(k6_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK3(sK2)) = sK3(sK2)
    | v1_xboole_0(sK2)
    | ~ spl10_42 ),
    inference(resolution,[],[f446,f251])).

fof(f460,plain,
    ( spl10_68
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f459,f262,f413])).

fof(f459,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_32 ),
    inference(resolution,[],[f456,f263])).

fof(f454,plain,
    ( spl10_76
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f447,f256,f452])).

fof(f447,plain,
    ( k1_funct_1(k6_relat_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),sK2) = sK2
    | ~ spl10_30 ),
    inference(resolution,[],[f128,f257])).

fof(f444,plain,
    ( ~ spl10_75
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f437,f197,f190,f183,f442])).

fof(f442,plain,
    ( spl10_75
  <=> ~ sP8(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f437,plain,
    ( ~ sP8(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f436,f198])).

fof(f436,plain,
    ( ~ v1_funct_1(sK2)
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_12
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f434,f191])).

fof(f434,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ sP8(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl10_12 ),
    inference(resolution,[],[f133,f184])).

fof(f433,plain,
    ( ~ spl10_73
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f418,f256,f431])).

fof(f431,plain,
    ( spl10_73
  <=> ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f418,plain,
    ( ~ sP9(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_30 ),
    inference(resolution,[],[f257,f135])).

fof(f426,plain,
    ( ~ spl10_71
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f416,f256,f424])).

fof(f424,plain,
    ( spl10_71
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f416,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK2)
    | ~ spl10_30 ),
    inference(resolution,[],[f257,f106])).

fof(f415,plain,
    ( spl10_68
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f407,f262,f413])).

fof(f407,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))))
    | ~ spl10_32 ),
    inference(resolution,[],[f405,f263])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = sK3(k1_zfmisc_1(X0)) )
    | ~ spl10_32 ),
    inference(resolution,[],[f404,f265])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = X0 )
    | ~ spl10_32 ),
    inference(resolution,[],[f263,f122])).

fof(f400,plain,
    ( spl10_66
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f393,f359,f398])).

fof(f398,plain,
    ( spl10_66
  <=> v1_relat_1(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f393,plain,
    ( v1_relat_1(k3_struct_0(sK5))
    | ~ spl10_56 ),
    inference(superposition,[],[f129,f360])).

fof(f392,plain,
    ( spl10_64
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f385,f366,f390])).

fof(f390,plain,
    ( spl10_64
  <=> v1_relat_1(k3_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f385,plain,
    ( v1_relat_1(k3_struct_0(sK7))
    | ~ spl10_58 ),
    inference(superposition,[],[f129,f367])).

fof(f384,plain,
    ( spl10_62
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f377,f352,f382])).

fof(f382,plain,
    ( spl10_62
  <=> v1_relat_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f377,plain,
    ( v1_relat_1(k3_struct_0(sK1))
    | ~ spl10_54 ),
    inference(superposition,[],[f129,f353])).

fof(f376,plain,
    ( spl10_60
    | ~ spl10_52 ),
    inference(avatar_split_clause,[],[f369,f345,f374])).

fof(f374,plain,
    ( spl10_60
  <=> v1_relat_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f369,plain,
    ( v1_relat_1(k3_struct_0(sK0))
    | ~ spl10_52 ),
    inference(superposition,[],[f129,f346])).

fof(f368,plain,
    ( spl10_58
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f340,f211,f366])).

fof(f211,plain,
    ( spl10_20
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f340,plain,
    ( k3_struct_0(sK7) = k6_relat_1(u1_struct_0(sK7))
    | ~ spl10_20 ),
    inference(resolution,[],[f130,f212])).

fof(f212,plain,
    ( l1_struct_0(sK7)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f211])).

fof(f361,plain,
    ( spl10_56
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f339,f227,f359])).

fof(f227,plain,
    ( spl10_24
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f339,plain,
    ( k3_struct_0(sK5) = k6_relat_1(u1_struct_0(sK5))
    | ~ spl10_24 ),
    inference(resolution,[],[f130,f228])).

fof(f228,plain,
    ( l1_struct_0(sK5)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f354,plain,
    ( spl10_54
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f337,f246,f352])).

fof(f337,plain,
    ( k3_struct_0(sK1) = k6_relat_1(u1_struct_0(sK1))
    | ~ spl10_28 ),
    inference(resolution,[],[f130,f247])).

fof(f347,plain,
    ( spl10_52
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f336,f220,f345])).

fof(f336,plain,
    ( k3_struct_0(sK0) = k6_relat_1(u1_struct_0(sK0))
    | ~ spl10_22 ),
    inference(resolution,[],[f130,f221])).

fof(f335,plain,
    ( ~ spl10_51
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f328,f301,f333])).

fof(f333,plain,
    ( spl10_51
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f328,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl10_42 ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl10_42 ),
    inference(resolution,[],[f313,f302])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_42 ),
    inference(resolution,[],[f302,f106])).

fof(f326,plain,
    ( ~ spl10_47
    | spl10_48
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f315,f301,f324,f321])).

fof(f321,plain,
    ( spl10_47
  <=> ~ sP9(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f324,plain,
    ( spl10_48
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f315,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ sP9(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) )
    | ~ spl10_42 ),
    inference(resolution,[],[f302,f135])).

fof(f312,plain,
    ( spl10_44
    | ~ spl10_32
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f304,f298,f262,f310])).

fof(f310,plain,
    ( spl10_44
  <=> k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f298,plain,
    ( spl10_40
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f304,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_32
    | ~ spl10_40 ),
    inference(resolution,[],[f299,f265])).

fof(f299,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f298])).

fof(f303,plain,
    ( spl10_40
    | spl10_42
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f293,f183,f301,f298])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) )
    | ~ spl10_12 ),
    inference(resolution,[],[f291,f104])).

fof(f291,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_12 ),
    inference(resolution,[],[f102,f184])).

fof(f290,plain,
    ( spl10_34
    | ~ spl10_37
    | spl10_38 ),
    inference(avatar_split_clause,[],[f267,f288,f282,f276])).

fof(f276,plain,
    ( spl10_34
  <=> k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f282,plain,
    ( spl10_37
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f267,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(u1_struct_0(sK1)),u1_struct_0(sK0))
    | k1_funct_1(sK2,sK3(u1_struct_0(sK1))) = sK3(u1_struct_0(sK1)) ),
    inference(resolution,[],[f251,f83])).

fof(f264,plain,
    ( spl10_30
    | spl10_32
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f250,f183,f262,f256])).

fof(f250,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl10_12 ),
    inference(resolution,[],[f104,f184])).

fof(f248,plain,
    ( spl10_28
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f241,f238,f246])).

fof(f241,plain,
    ( l1_struct_0(sK1)
    | ~ spl10_26 ),
    inference(resolution,[],[f239,f124])).

fof(f240,plain,
    ( spl10_26
    | ~ spl10_0
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f233,f162,f141,f238])).

fof(f233,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_0
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f230,f142])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f109,f163])).

fof(f229,plain,
    ( spl10_24
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f215,f204,f227])).

fof(f215,plain,
    ( l1_struct_0(sK5)
    | ~ spl10_18 ),
    inference(resolution,[],[f124,f205])).

fof(f222,plain,
    ( spl10_22
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f214,f141,f220])).

fof(f214,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_0 ),
    inference(resolution,[],[f124,f142])).

fof(f213,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f123,f211])).

fof(f123,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',existence_l1_struct_0)).

fof(f206,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f110,f204])).

fof(f110,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t96_tmap_1.p',existence_l1_pre_topc)).

fof(f199,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f84,f197])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f192,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f85,f190])).

fof(f85,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f185,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f86,f183])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f178,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f87,f176])).

fof(f87,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f171,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f88,f169])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f164,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f89,f162])).

fof(f89,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f157,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f90,f155])).

fof(f90,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f150,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f91,f148])).

fof(f91,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f143,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f92,f141])).

fof(f92,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------

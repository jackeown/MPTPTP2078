%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t45_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:51 EDT 2019

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       : 3464 (16946 expanded)
%              Number of leaves         :  785 (6914 expanded)
%              Depth                    :   24
%              Number of atoms          : 13860 (58521 expanded)
%              Number of equality atoms :  676 (4573 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f319,f326,f333,f340,f347,f354,f361,f368,f375,f382,f389,f396,f403,f410,f417,f424,f431,f438,f445,f452,f459,f466,f473,f480,f487,f494,f501,f508,f515,f522,f529,f536,f543,f550,f564,f571,f578,f585,f592,f599,f606,f615,f624,f652,f659,f675,f686,f700,f707,f728,f736,f799,f813,f830,f838,f847,f871,f878,f888,f898,f939,f958,f966,f974,f982,f990,f992,f1022,f1099,f1107,f1116,f1124,f1132,f1140,f1227,f1282,f1292,f1302,f1312,f1322,f1327,f1351,f1358,f1379,f1392,f1405,f1418,f1425,f1454,f1461,f1468,f1475,f1485,f1487,f1495,f1503,f1505,f1513,f1516,f1524,f1532,f1540,f1546,f1547,f1554,f1576,f1593,f1598,f1602,f1606,f1628,f1638,f1646,f1655,f1663,f1671,f1679,f1687,f1689,f1691,f1700,f1730,f1743,f1757,f1771,f1784,f1798,f1812,f1826,f1839,f1891,f1908,f1925,f1932,f1939,f1944,f1954,f2011,f2013,f2060,f2119,f2133,f2153,f2173,f2192,f2212,f2232,f2252,f2271,f2312,f2333,f2336,f2345,f2354,f2356,f2358,f2360,f2367,f2368,f2369,f2373,f2376,f2379,f2381,f2382,f2384,f2387,f2389,f2391,f2393,f2394,f2395,f2397,f2400,f2402,f2405,f2407,f2409,f2411,f2413,f2415,f2418,f2421,f2422,f2424,f2426,f2427,f2429,f2431,f2432,f2449,f2451,f2452,f2459,f2466,f2473,f2480,f2487,f2494,f2501,f2508,f2515,f2522,f2524,f2526,f2528,f2533,f2534,f2573,f2594,f2597,f2606,f2615,f2649,f2679,f2698,f2699,f2710,f2718,f2726,f2728,f2736,f2743,f2744,f2746,f2752,f2772,f2787,f2821,f2840,f2841,f2852,f2860,f2868,f2870,f2877,f2900,f2940,f2948,f2959,f3031,f3050,f3051,f3062,f3070,f3078,f3080,f3087,f3106,f3142,f3161,f3162,f3173,f3181,f3189,f3191,f3198,f3341,f3368,f3375,f3386,f3409,f3416,f3453,f3476,f3483,f3585,f3598,f3802,f3869,f3881,f3890,f3894,f3895,f3902,f3903,f3910,f3911,f3918,f3919,f3920,f3921,f3923,f3925,f3932,f3944,f3953,f3954,f3955,f3957,f3970,f4188,f4206,f4214,f4222,f4224,f4228,f4237,f4245,f4252,f4259,f4266,f4273,f4280,f4287,f4294,f4301,f4309,f4317,f4331,f4345,f4347,f4358,f4372,f4392,f4394,f4396,f4407,f4421,f4441,f4443,f4451,f4453,f4458,f4463,f4465,f4473,f4481,f4483,f4491,f4493,f4498,f4503,f4505,f4513,f4521,f4523,f4531,f4539,f4547,f4555,f4563,f4571,f4579,f4587,f4595,f4603,f4605,f4607,f4648,f4656,f4664,f4684,f4689,f4694,f4702,f4710,f4712,f4720,f4728,f4858,f4874,f4891,f4907,f4926,f4995,f5030,f5041,f5094,f5123,f5133,f5141,f5148,f5156,f5163,f5166,f5171,f5174,f5179,f5184,f5189,f5192,f5195,f5198,f5204,f5210,f5213,f5217,f5220,f5222,f5224,f5228,f5229,f5232,f5233,f5236,f5240,f5242,f5327,f5346,f5359,f5363,f5370,f5372,f5409,f5428,f5441,f5445,f5452,f5454,f5568,f5609,f5616,f5623,f5642,f5646,f5650,f5657,f5664,f5665,f5673,f5681,f5686,f5688,f5704,f5706,f5707,f5748,f5847,f5866,f5879,f5883,f5890,f5892,f5943,f5994,f6018,f6037,f6050,f6054,f6061,f6063,f6223,f6245,f6265,f6285,f6289,f6296,f6303,f6304,f6305,f6307,f6309,f6316,f6323,f6324,f6325,f6328,f6333,f6336,f6341,f6345,f6348,f6353,f6356,f6361,f6363,f6368,f6371,f6373,f6376,f6378,f6464,f6466,f6488,f6489,f6530,f6532,f6534,f6536,f6544,f6548,f6550,f6552,f6554,f6587,f6591,f6593,f6594,f6625,f6626,f6651,f6658,f6665,f6672,f6679,f6686,f6693,f6700,f6707,f6714,f6721,f6728,f6730,f6755,f6762,f6769,f6776,f6783,f6790,f6797,f6804,f6811,f6818,f6825,f6832,f6833,f6860,f6898,f6903,f6908,f6947,f6962,f6976,f6990,f7004,f7018,f7035,f7039,f7061,f7068,f7093,f7095,f7122,f7123,f7150,f7157,f7164,f7171,f7178,f7185,f7192,f7199,f7206,f7213,f7220,f7227,f7234,f7257,f7264,f7271,f7278,f7285,f7292,f7299,f7306,f7313,f7320,f7327,f7334,f7341,f7376,f7415,f7419,f7423,f7440,f7445,f7455,f7464,f7470,f7475,f7480,f7491,f7500,f7506,f7511,f7516,f7599,f7600,f7642,f7649,f7656,f7675,f7679,f7683,f7690,f7697,f7698,f7705,f7709,f7717,f7725,f7730,f7732,f7737,f7741,f7750,f7752,f7754,f7833,f7857,f7895,f7911,f7925,f7938,f8004,f8008,f8034,f8041,f8048,f8055,f8062,f8069,f8076,f8083,f8090,f8097,f8104,f8111,f8114,f8117,f8120,f8123,f8126,f8129,f8132,f8133,f8136,f8138,f8139,f8143,f8146,f8150,f8151,f8155,f8159,f8163,f8167,f8171,f8176,f8179,f8182,f8184,f8186,f8188,f8192,f8196,f8201,f8204,f8207,f8208,f8210,f8212,f8214,f8218,f8220,f8223,f8225,f8228,f8231,f8237,f8240,f8243,f8245,f8246,f8247,f8250,f8251,f8253,f8254,f8255,f8258,f8259,f8260,f8263,f8266,f8270,f8273,f8277,f8309,f8351,f8355,f8358,f8363,f8366,f8368,f8373,f8376,f8385,f8389,f8393,f8402,f8405,f8430,f8437,f8444,f8451,f8458,f8465,f8472,f8479,f8486,f8493,f8500,f8507,f8509,f8557,f8594,f8599,f8603,f8608,f8619,f8658,f8816,f8820,f8827,f8840,f8852,f8862,f8866,f8877,f8881,f9125,f9137,f9141,f9153,f9229,f9301,f9329,f9422,f9475,f9502,f9529,f9779,f9867,f9957,f10587,f10598,f10622,f10993,f10998,f11005,f11093,f11097,f11115])).

fof(f11115,plain,
    ( ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(avatar_contradiction_clause,[],[f11114])).

fof(f11114,plain,
    ( $false
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11113,f332])).

fof(f332,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_4 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl31_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_4])])).

fof(f11113,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(forward_demodulation,[],[f11112,f1424])).

fof(f1424,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f1423,plain,
    ( spl31_194
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_194])])).

fof(f11112,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11111,f339])).

fof(f339,plain,
    ( ~ v3_tex_2(sK3,sK1)
    | ~ spl31_7 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl31_7
  <=> ~ v3_tex_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_7])])).

fof(f11111,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tex_2(sK3,sK1)
    | ~ spl31_2
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11110,f325])).

fof(f325,plain,
    ( l1_pre_topc(sK1)
    | ~ spl31_2 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl31_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_2])])).

fof(f11110,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11086,f2056])).

fof(f2056,plain,
    ( v2_tex_2(sK3,sK1)
    | ~ spl31_296 ),
    inference(avatar_component_clause,[],[f2055])).

fof(f2055,plain,
    ( spl31_296
  <=> v2_tex_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_296])])).

fof(f11086,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_1202 ),
    inference(trivial_inequality_removal,[],[f11073])).

fof(f11073,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_1202 ),
    inference(superposition,[],[f201,f10992])).

fof(f10992,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ spl31_1202 ),
    inference(avatar_component_clause,[],[f10991])).

fof(f10991,plain,
    ( spl31_1202
  <=> sK3 = sK4(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1202])])).

fof(f201,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',d7_tex_2)).

fof(f11097,plain,
    ( spl31_1204
    | ~ spl31_2
    | spl31_7
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(avatar_split_clause,[],[f11096,f10991,f2055,f1423,f698,f338,f324,f11091])).

fof(f11091,plain,
    ( spl31_1204
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1204])])).

fof(f698,plain,
    ( spl31_96
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_96])])).

fof(f11096,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11095,f699])).

fof(f699,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_96 ),
    inference(avatar_component_clause,[],[f698])).

fof(f11095,plain,
    ( r1_tarski(sK3,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11094,f339])).

fof(f11094,plain,
    ( r1_tarski(sK3,sK3)
    | v3_tex_2(sK3,sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_296
    | ~ spl31_1202 ),
    inference(subsumption_resolution,[],[f11057,f2056])).

fof(f11057,plain,
    ( r1_tarski(sK3,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_1202 ),
    inference(superposition,[],[f3267,f10992])).

fof(f3267,plain,
    ( ! [X1] :
        ( r1_tarski(X1,sK4(sK1,X1))
        | ~ v2_tex_2(X1,sK1)
        | v3_tex_2(X1,sK1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1872,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',t3_subset)).

fof(f1872,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK1)
        | r1_tarski(X1,sK4(sK1,X1))
        | v3_tex_2(X1,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1869,f325])).

fof(f1869,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_tex_2(X1,sK1)
        | r1_tarski(X1,sK4(sK1,X1))
        | v3_tex_2(X1,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f200,f1424])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK4(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f11093,plain,
    ( spl31_1204
    | ~ spl31_582
    | ~ spl31_1202 ),
    inference(avatar_split_clause,[],[f11051,f10991,f4243,f11091])).

fof(f4243,plain,
    ( spl31_582
  <=> r1_tarski(sK3,sK4(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_582])])).

fof(f11051,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl31_582
    | ~ spl31_1202 ),
    inference(backward_demodulation,[],[f10992,f4244])).

fof(f4244,plain,
    ( r1_tarski(sK3,sK4(sK1,sK3))
    | ~ spl31_582 ),
    inference(avatar_component_clause,[],[f4243])).

fof(f11005,plain,
    ( spl31_1202
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_8
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(avatar_split_clause,[],[f11004,f2055,f1906,f1423,f698,f345,f338,f331,f324,f317,f10991])).

fof(f317,plain,
    ( spl31_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_0])])).

fof(f345,plain,
    ( spl31_8
  <=> v3_tex_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_8])])).

fof(f1906,plain,
    ( spl31_284
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_284])])).

fof(f11004,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f11003,f699])).

fof(f11003,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | sK3 = sK4(sK1,sK3)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(forward_demodulation,[],[f11002,f1424])).

fof(f11002,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f11001,f325])).

fof(f11001,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f11000,f332])).

fof(f11000,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10999,f339])).

fof(f10999,plain,
    ( sK3 = sK4(sK1,sK3)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10982,f2056])).

fof(f10982,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(duplicate_literal_removal,[],[f10981])).

fof(f10981,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | v3_tex_2(sK3,sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f6399,f1866])).

fof(f1866,plain,(
    ! [X8,X9] :
      ( r1_tarski(X9,sK4(X8,X9))
      | ~ v2_tex_2(X9,X8)
      | ~ l1_pre_topc(X8)
      | v3_tex_2(X9,X8)
      | ~ r1_tarski(X9,u1_struct_0(X8)) ) ),
    inference(resolution,[],[f200,f224])).

fof(f6399,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,sK4(sK1,X0))
        | sK3 = sK4(sK1,X0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f6380,f3834])).

fof(f3834,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(sK4(sK1,X0),sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f3816,f1855])).

fof(f1855,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK1)
        | v2_tex_2(sK4(sK1,X1),sK1)
        | v3_tex_2(X1,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1852,f325])).

fof(f1852,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_tex_2(X1,sK1)
        | v2_tex_2(sK4(sK1,X1),sK1)
        | v3_tex_2(X1,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f199,f1424])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(sK4(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f3816,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK4(sK1,X0),sK1)
        | v2_tex_2(sK4(sK1,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f3813,f1975])).

fof(f1975,plain,
    ( ! [X1] :
        ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK1)
        | v3_tex_2(X1,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1974,f1424])).

fof(f1974,plain,
    ( ! [X1] :
        ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_tex_2(X1,sK1)
        | v3_tex_2(X1,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1964,f325])).

fof(f1964,plain,
    ( ! [X1] :
        ( m1_subset_1(sK4(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_tex_2(X1,sK1)
        | ~ l1_pre_topc(sK1)
        | v3_tex_2(X1,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f198,f1424])).

fof(f198,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f3813,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f3789,f318])).

fof(f318,plain,
    ( l1_pre_topc(sK0)
    | ~ spl31_0 ),
    inference(avatar_component_clause,[],[f317])).

fof(f3789,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK0) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(duplicate_literal_removal,[],[f3788])).

fof(f3788,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK0) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(equality_resolution,[],[f3622])).

fof(f3622,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_tex_2(X3,sK1)
        | v2_tex_2(X3,X2) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3621,f1424])).

fof(f3621,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_tex_2(X3,sK1)
        | v2_tex_2(X3,X2) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3620,f1907])).

fof(f1907,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl31_284 ),
    inference(avatar_component_clause,[],[f1906])).

fof(f3620,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_tex_2(X3,sK1)
        | v2_tex_2(X3,X2) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3600,f325])).

fof(f3600,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_tex_2(X3,sK1)
        | v2_tex_2(X3,X2) )
    | ~ spl31_194 ),
    inference(superposition,[],[f312,f1424])).

fof(f312,plain,(
    ! [X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X3,X0)
      | v2_tex_2(X3,X1) ) ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | X2 != X3
      | ~ v2_tex_2(X2,X0)
      | v2_tex_2(X3,X1) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f132])).

fof(f132,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f107])).

fof(f107,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',t25_tex_2)).

fof(f6380,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,sK4(sK1,X0))
        | sK3 = sK4(sK1,X0)
        | ~ v2_tex_2(sK4(sK1,X0),sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194 ),
    inference(resolution,[],[f5800,f3321])).

fof(f3321,plain,
    ( ! [X13] :
        ( r1_tarski(sK4(sK1,X13),u1_struct_0(sK0))
        | ~ v2_tex_2(X13,sK1)
        | v3_tex_2(X13,sK1)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1975,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f5800,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(sK3,X0)
        | sK3 = X0
        | ~ v2_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_8 ),
    inference(subsumption_resolution,[],[f5799,f346])).

fof(f346,plain,
    ( v3_tex_2(sK3,sK0)
    | ~ spl31_8 ),
    inference(avatar_component_clause,[],[f345])).

fof(f5799,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK3,X0)
        | sK3 = X0
        | ~ v3_tex_2(sK3,sK0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_0
    | ~ spl31_4 ),
    inference(subsumption_resolution,[],[f5770,f318])).

fof(f5770,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(sK3,X0)
        | sK3 = X0
        | ~ v3_tex_2(sK3,sK0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_4 ),
    inference(resolution,[],[f2072,f332])).

fof(f2072,plain,(
    ! [X21,X22,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ l1_pre_topc(X21)
      | ~ v2_tex_2(X22,X21)
      | ~ r1_tarski(X20,X22)
      | X20 = X22
      | ~ v3_tex_2(X20,X21)
      | ~ r1_tarski(X22,u1_struct_0(X21)) ) ),
    inference(resolution,[],[f202,f224])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f10998,plain,
    ( spl31_1202
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_8
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(avatar_split_clause,[],[f10997,f2055,f1906,f1423,f698,f345,f338,f331,f324,f317,f10991])).

fof(f10997,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_96
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10996,f699])).

fof(f10996,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10995,f332])).

fof(f10995,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10994,f339])).

fof(f10994,plain,
    ( sK3 = sK4(sK1,sK3)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296 ),
    inference(subsumption_resolution,[],[f10983,f2056])).

fof(f10983,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(duplicate_literal_removal,[],[f10980])).

fof(f10980,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f6399,f3267])).

fof(f10993,plain,
    ( spl31_1202
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296
    | ~ spl31_582 ),
    inference(avatar_split_clause,[],[f10986,f4243,f2055,f1906,f1423,f345,f338,f331,f324,f317,f10991])).

fof(f10986,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296
    | ~ spl31_582 ),
    inference(subsumption_resolution,[],[f10985,f332])).

fof(f10985,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296
    | ~ spl31_582 ),
    inference(subsumption_resolution,[],[f10984,f339])).

fof(f10984,plain,
    ( sK3 = sK4(sK1,sK3)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_296
    | ~ spl31_582 ),
    inference(subsumption_resolution,[],[f10979,f2056])).

fof(f10979,plain,
    ( sK3 = sK4(sK1,sK3)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_582 ),
    inference(resolution,[],[f6399,f4244])).

fof(f10622,plain,
    ( spl31_1198
    | spl31_1200
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f10612,f5566,f373,f10620,f10614])).

fof(f10614,plain,
    ( spl31_1198
  <=> ! [X4] : g1_pre_topc(X4,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1198])])).

fof(f10620,plain,
    ( spl31_1200
  <=> u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1200])])).

fof(f373,plain,
    ( spl31_16
  <=> v1_xboole_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_16])])).

fof(f5566,plain,
    ( spl31_780
  <=> g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_780])])).

fof(f10612,plain,
    ( ! [X4] :
        ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = sK9
        | g1_pre_topc(X4,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) )
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(forward_demodulation,[],[f10604,f8671])).

fof(f8671,plain,
    ( ! [X0] : u1_pre_topc(g1_pre_topc(X0,sK9)) = sK9
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f8666,f629])).

fof(f629,plain,
    ( ! [X0] : m1_subset_1(sK9,k1_zfmisc_1(X0))
    | ~ spl31_16 ),
    inference(backward_demodulation,[],[f628,f216])).

fof(f216,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc2_subset_1)).

fof(f628,plain,
    ( ! [X0] : sK6(X0) = sK9
    | ~ spl31_16 ),
    inference(resolution,[],[f625,f217])).

fof(f217,plain,(
    ! [X0] : v1_xboole_0(sK6(X0)) ),
    inference(cnf_transformation,[],[f88])).

fof(f625,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK9 = X0 )
    | ~ spl31_16 ),
    inference(resolution,[],[f204,f374])).

fof(f374,plain,
    ( v1_xboole_0(sK9)
    | ~ spl31_16 ),
    inference(avatar_component_clause,[],[f373])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f114])).

fof(f114,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',t8_boole)).

fof(f8666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_pre_topc(g1_pre_topc(X0,sK9)) = sK9 )
    | ~ spl31_16 ),
    inference(equality_resolution,[],[f4770])).

fof(f4770,plain,
    ( ! [X26,X24,X25] :
        ( g1_pre_topc(X24,sK9) != g1_pre_topc(X25,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
        | u1_pre_topc(g1_pre_topc(X24,sK9)) = X26 )
    | ~ spl31_16 ),
    inference(superposition,[],[f208,f1086])).

fof(f1086,plain,
    ( ! [X2] : g1_pre_topc(X2,sK9) = g1_pre_topc(u1_struct_0(g1_pre_topc(X2,sK9)),u1_pre_topc(g1_pre_topc(X2,sK9)))
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f1072,f746])).

fof(f746,plain,
    ( ! [X1] : l1_pre_topc(g1_pre_topc(X1,sK9))
    | ~ spl31_16 ),
    inference(resolution,[],[f210,f629])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',dt_g1_pre_topc)).

fof(f1072,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(g1_pre_topc(X2,sK9))
        | g1_pre_topc(X2,sK9) = g1_pre_topc(u1_struct_0(g1_pre_topc(X2,sK9)),u1_pre_topc(g1_pre_topc(X2,sK9))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f213,f710])).

fof(f710,plain,
    ( ! [X1] : v1_pre_topc(g1_pre_topc(X1,sK9))
    | ~ spl31_16 ),
    inference(resolution,[],[f209,f629])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f123])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',abstractness_v1_pre_topc)).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',free_g1_pre_topc)).

fof(f10604,plain,
    ( ! [X4] :
        ( g1_pre_topc(X4,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | u1_pre_topc(g1_pre_topc(X4,sK9)) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) )
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(superposition,[],[f10600,f5567])).

fof(f5567,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))
    | ~ spl31_780 ),
    inference(avatar_component_clause,[],[f5566])).

fof(f10600,plain,
    ( ! [X23,X21,X22] :
        ( g1_pre_topc(X21,sK9) != g1_pre_topc(X22,X23)
        | u1_pre_topc(g1_pre_topc(X21,sK9)) = X23 )
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f10599,f629])).

fof(f10599,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(X21)))
        | g1_pre_topc(X21,sK9) != g1_pre_topc(X22,X23)
        | u1_pre_topc(g1_pre_topc(X21,sK9)) = X23 )
    | ~ spl31_16 ),
    inference(forward_demodulation,[],[f10164,f8671])).

fof(f10164,plain,
    ( ! [X23,X21,X22] :
        ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(X21,sK9)),k1_zfmisc_1(k1_zfmisc_1(X21)))
        | g1_pre_topc(X21,sK9) != g1_pre_topc(X22,X23)
        | u1_pre_topc(g1_pre_topc(X21,sK9)) = X23 )
    | ~ spl31_16 ),
    inference(backward_demodulation,[],[f8654,f4769])).

fof(f4769,plain,
    ( ! [X23,X21,X22] :
        ( g1_pre_topc(X21,sK9) != g1_pre_topc(X22,X23)
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(X21,sK9)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X21,sK9)))))
        | u1_pre_topc(g1_pre_topc(X21,sK9)) = X23 )
    | ~ spl31_16 ),
    inference(superposition,[],[f208,f1086])).

fof(f8654,plain,
    ( ! [X0] : u1_struct_0(g1_pre_topc(X0,sK9)) = X0
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f8648,f629])).

fof(f8648,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_struct_0(g1_pre_topc(X0,sK9)) = X0 )
    | ~ spl31_16 ),
    inference(equality_resolution,[],[f4768])).

fof(f4768,plain,
    ( ! [X19,X20,X18] :
        ( g1_pre_topc(X18,sK9) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))
        | u1_struct_0(g1_pre_topc(X18,sK9)) = X19 )
    | ~ spl31_16 ),
    inference(superposition,[],[f207,f1086])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f122])).

fof(f10598,plain,
    ( spl31_1196
    | ~ spl31_1126 ),
    inference(avatar_split_clause,[],[f10590,f8808,f10596])).

fof(f10596,plain,
    ( spl31_1196
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1196])])).

fof(f8808,plain,
    ( spl31_1126
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1126])])).

fof(f10590,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ spl31_1126 ),
    inference(resolution,[],[f8809,f223])).

fof(f223,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',dt_l1_pre_topc)).

fof(f8809,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ spl31_1126 ),
    inference(avatar_component_clause,[],[f8808])).

fof(f10587,plain,
    ( ~ spl31_14
    | spl31_1127 ),
    inference(avatar_contradiction_clause,[],[f10586])).

fof(f10586,plain,
    ( $false
    | ~ spl31_14
    | ~ spl31_1127 ),
    inference(subsumption_resolution,[],[f10585,f367])).

fof(f367,plain,
    ( l1_pre_topc(sK8)
    | ~ spl31_14 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl31_14
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_14])])).

fof(f10585,plain,
    ( ~ l1_pre_topc(sK8)
    | ~ spl31_1127 ),
    inference(resolution,[],[f8812,f773])).

fof(f773,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f214,f210])).

fof(f214,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',dt_u1_pre_topc)).

fof(f8812,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ spl31_1127 ),
    inference(avatar_component_clause,[],[f8811])).

fof(f8811,plain,
    ( spl31_1127
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1127])])).

fof(f9957,plain,
    ( ~ spl31_1195
    | spl31_1187 ),
    inference(avatar_split_clause,[],[f9950,f9521,f9955])).

fof(f9955,plain,
    ( spl31_1195
  <=> ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1195])])).

fof(f9521,plain,
    ( spl31_1187
  <=> ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1187])])).

fof(f9950,plain,
    ( ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | ~ spl31_1187 ),
    inference(resolution,[],[f9522,f224])).

fof(f9522,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_1187 ),
    inference(avatar_component_clause,[],[f9521])).

fof(f9867,plain,
    ( ~ spl31_1193
    | spl31_1179 ),
    inference(avatar_split_clause,[],[f9860,f9494,f9865])).

fof(f9865,plain,
    ( spl31_1193
  <=> ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1193])])).

fof(f9494,plain,
    ( spl31_1179
  <=> ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1179])])).

fof(f9860,plain,
    ( ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | ~ spl31_1179 ),
    inference(resolution,[],[f9495,f224])).

fof(f9495,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_1179 ),
    inference(avatar_component_clause,[],[f9494])).

fof(f9779,plain,
    ( ~ spl31_1191
    | spl31_1171 ),
    inference(avatar_split_clause,[],[f9772,f9467,f9777])).

fof(f9777,plain,
    ( spl31_1191
  <=> ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1191])])).

fof(f9467,plain,
    ( spl31_1171
  <=> ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1171])])).

fof(f9772,plain,
    ( ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),u1_struct_0(sK0))
    | ~ spl31_1171 ),
    inference(resolution,[],[f9468,f224])).

fof(f9468,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_1171 ),
    inference(avatar_component_clause,[],[f9467])).

fof(f9529,plain,
    ( spl31_1182
    | ~ spl31_1185
    | ~ spl31_1187
    | spl31_1188
    | ~ spl31_108
    | spl31_237
    | ~ spl31_816 ),
    inference(avatar_split_clause,[],[f9504,f5746,f1653,f828,f9527,f9521,f9515,f9509])).

fof(f9509,plain,
    ( spl31_1182
  <=> v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1182])])).

fof(f9515,plain,
    ( spl31_1185
  <=> ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1185])])).

fof(f9527,plain,
    ( spl31_1188
  <=> v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1188])])).

fof(f828,plain,
    ( spl31_108
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_108])])).

fof(f1653,plain,
    ( spl31_237
  <=> ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_237])])).

fof(f5746,plain,
    ( spl31_816
  <=> ! [X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X14,sK1)
        | ~ v2_tex_2(X14,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_816])])).

fof(f9504,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_237
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9503,f1654])).

fof(f1654,plain,
    ( ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_237 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f9503,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9432,f829])).

fof(f829,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108 ),
    inference(avatar_component_clause,[],[f828])).

fof(f9432,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_816 ),
    inference(resolution,[],[f5747,f4633])).

fof(f4633,plain,(
    ! [X5] :
      ( v2_tex_2(sK4(X5,sK22(X5)),X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK22(X5),X5)
      | v7_struct_0(X5)
      | v3_tex_2(sK22(X5),X5) ) ),
    inference(subsumption_resolution,[],[f4612,f223])).

fof(f4612,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | v7_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK22(X5),X5)
      | v2_tex_2(sK4(X5,sK22(X5)),X5)
      | v3_tex_2(sK22(X5),X5) ) ),
    inference(resolution,[],[f4141,f199])).

fof(f4141,plain,(
    ! [X0] :
      ( m1_subset_1(sK22(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f267,f274])).

fof(f274,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f161,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f160])).

fof(f160,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v2_struct_0(X0)
       => v7_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc1_struct_0)).

fof(f267,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK22(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc5_tex_2)).

fof(f5747,plain,
    ( ! [X14] :
        ( ~ v2_tex_2(X14,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X14,sK1)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_816 ),
    inference(avatar_component_clause,[],[f5746])).

fof(f9502,plain,
    ( spl31_1174
    | ~ spl31_1177
    | ~ spl31_1179
    | spl31_1180
    | ~ spl31_108
    | spl31_237
    | ~ spl31_816 ),
    inference(avatar_split_clause,[],[f9477,f5746,f1653,f828,f9500,f9494,f9488,f9482])).

fof(f9482,plain,
    ( spl31_1174
  <=> v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1174])])).

fof(f9488,plain,
    ( spl31_1177
  <=> ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1177])])).

fof(f9500,plain,
    ( spl31_1180
  <=> v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1180])])).

fof(f9477,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_237
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9476,f1654])).

fof(f9476,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9431,f829])).

fof(f9431,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_816 ),
    inference(resolution,[],[f5747,f4113])).

fof(f4113,plain,(
    ! [X5] :
      ( v2_tex_2(sK4(X5,sK21(X5)),X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK21(X5),X5)
      | v7_struct_0(X5)
      | v3_tex_2(sK21(X5),X5) ) ),
    inference(subsumption_resolution,[],[f4092,f223])).

fof(f4092,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | v7_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK21(X5),X5)
      | v2_tex_2(sK4(X5,sK21(X5)),X5)
      | v3_tex_2(sK21(X5),X5) ) ),
    inference(resolution,[],[f4086,f199])).

fof(f4086,plain,(
    ! [X0] :
      ( m1_subset_1(sK21(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f263,f274])).

fof(f263,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK21(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f150])).

fof(f150,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f103])).

fof(f103,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc6_tex_2)).

fof(f9475,plain,
    ( spl31_1166
    | ~ spl31_1169
    | ~ spl31_1171
    | spl31_1172
    | ~ spl31_108
    | spl31_237
    | ~ spl31_816 ),
    inference(avatar_split_clause,[],[f9450,f5746,f1653,f828,f9473,f9467,f9461,f9455])).

fof(f9455,plain,
    ( spl31_1166
  <=> v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1166])])).

fof(f9461,plain,
    ( spl31_1169
  <=> ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1169])])).

fof(f9473,plain,
    ( spl31_1172
  <=> v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1172])])).

fof(f9450,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_237
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9449,f1654])).

fof(f9449,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_816 ),
    inference(subsumption_resolution,[],[f9430,f829])).

fof(f9430,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_816 ),
    inference(resolution,[],[f5747,f4054])).

fof(f4054,plain,(
    ! [X5] :
      ( v2_tex_2(sK4(X5,sK20(X5)),X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK20(X5),X5)
      | v7_struct_0(X5)
      | v3_tex_2(sK20(X5),X5) ) ),
    inference(subsumption_resolution,[],[f4033,f223])).

fof(f4033,plain,(
    ! [X5] :
      ( ~ l1_struct_0(X5)
      | v7_struct_0(X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_tex_2(sK20(X5),X5)
      | v2_tex_2(sK4(X5,sK20(X5)),X5)
      | v3_tex_2(sK20(X5),X5) ) ),
    inference(resolution,[],[f3971,f199])).

fof(f3971,plain,(
    ! [X0] :
      ( m1_subset_1(sK20(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f259,f274])).

fof(f259,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK20(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f99])).

fof(f99,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc4_tex_2)).

fof(f9422,plain,
    ( spl31_816
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(avatar_split_clause,[],[f4158,f2009,f1906,f1574,f1423,f828,f324,f5746])).

fof(f1574,plain,
    ( spl31_220
  <=> u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_220])])).

fof(f2009,plain,
    ( spl31_292
  <=> u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_292])])).

fof(f4158,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(duplicate_literal_removal,[],[f4157])).

fof(f4157,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f4156,f1575])).

fof(f1575,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(avatar_component_clause,[],[f1574])).

fof(f4156,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(trivial_inequality_removal,[],[f4155])).

fof(f4155,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f4154,f2010])).

fof(f2010,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_292 ),
    inference(avatar_component_clause,[],[f2009])).

fof(f4154,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4144,f829])).

fof(f4144,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(superposition,[],[f3640,f1575])).

fof(f3640,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v2_tex_2(X3,X2)
        | v2_tex_2(X3,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3639,f1424])).

fof(f3639,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X2)
        | ~ v2_tex_2(X3,X2)
        | v2_tex_2(X3,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3638,f1907])).

fof(f3638,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X2)
        | ~ v2_tex_2(X3,X2)
        | v2_tex_2(X3,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3608,f325])).

fof(f3608,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(X2)
        | ~ v2_tex_2(X3,X2)
        | v2_tex_2(X3,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f312,f1424])).

fof(f9329,plain,
    ( ~ spl31_1163
    | ~ spl31_1165
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292
    | spl31_1159 ),
    inference(avatar_split_clause,[],[f9316,f9293,f2009,f1906,f1574,f1423,f828,f324,f9327,f9321])).

fof(f9321,plain,
    ( spl31_1163
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1163])])).

fof(f9327,plain,
    ( spl31_1165
  <=> ~ v2_tex_2(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1165])])).

fof(f9293,plain,
    ( spl31_1159
  <=> ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1159])])).

fof(f9316,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292
    | ~ spl31_1159 ),
    inference(resolution,[],[f9294,f3807])).

fof(f3807,plain,
    ( ! [X2] :
        ( v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(duplicate_literal_removal,[],[f3806])).

fof(f3806,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f3805,f1575])).

fof(f3805,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,sK1)
        | v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(trivial_inequality_removal,[],[f3804])).

fof(f3804,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,sK1)
        | v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f3803,f2010])).

fof(f3803,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,sK1)
        | v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f3782,f829])).

fof(f3782,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X2,sK1)
        | v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(superposition,[],[f3622,f1575])).

fof(f9294,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_1159 ),
    inference(avatar_component_clause,[],[f9293])).

fof(f9301,plain,
    ( ~ spl31_1155
    | spl31_1156
    | ~ spl31_1159
    | ~ spl31_1161
    | spl31_107
    | ~ spl31_108
    | ~ spl31_220
    | ~ spl31_496 ),
    inference(avatar_split_clause,[],[f9276,f3085,f1574,f828,f811,f9299,f9293,f9287,f9281])).

fof(f9281,plain,
    ( spl31_1155
  <=> ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1155])])).

fof(f9287,plain,
    ( spl31_1156
  <=> u1_struct_0(sK0) = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1156])])).

fof(f9299,plain,
    ( spl31_1161
  <=> ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1161])])).

fof(f811,plain,
    ( spl31_107
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_107])])).

fof(f3085,plain,
    ( spl31_496
  <=> r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_496])])).

fof(f9276,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_107
    | ~ spl31_108
    | ~ spl31_220
    | ~ spl31_496 ),
    inference(forward_demodulation,[],[f9275,f1575])).

fof(f9275,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_107
    | ~ spl31_108
    | ~ spl31_496 ),
    inference(subsumption_resolution,[],[f9274,f812])).

fof(f812,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_107 ),
    inference(avatar_component_clause,[],[f811])).

fof(f9274,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_496 ),
    inference(subsumption_resolution,[],[f9266,f829])).

fof(f9266,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_496 ),
    inference(resolution,[],[f5802,f3086])).

fof(f3086,plain,
    ( r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_496 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f5802,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(sK15(X6),X7)
      | ~ v2_tex_2(X7,X6)
      | ~ l1_pre_topc(X6)
      | sK15(X6) = X7
      | ~ v3_tex_2(sK15(X6),X6)
      | ~ r1_tarski(X7,u1_struct_0(X6))
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f5773,f223])).

fof(f5773,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ v2_tex_2(X7,X6)
      | ~ r1_tarski(sK15(X6),X7)
      | sK15(X6) = X7
      | ~ v3_tex_2(sK15(X6),X6)
      | ~ r1_tarski(X7,u1_struct_0(X6))
      | ~ l1_struct_0(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f2072,f243])).

fof(f243,plain,(
    ! [X0] :
      ( m1_subset_1(sK15(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f84])).

fof(f84,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc20_struct_0)).

fof(f9229,plain,
    ( spl31_738
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_1124 ),
    inference(avatar_split_clause,[],[f9203,f8617,f1423,f324,f5182])).

fof(f5182,plain,
    ( spl31_738
  <=> ! [X2] :
        ( v1_xboole_0(sK4(sK1,X2))
        | v3_tex_2(X2,sK1)
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(sK4(sK1,X2))
        | v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_738])])).

fof(f8617,plain,
    ( spl31_1124
  <=> ! [X2] :
        ( v1_subset_1(X2,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X2)
        | v1_xboole_0(X2)
        | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1124])])).

fof(f9203,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(sK4(sK1,X0))
        | v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_1124 ),
    inference(resolution,[],[f8618,f3321])).

fof(f8618,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X2)
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl31_1124 ),
    inference(avatar_component_clause,[],[f8617])).

fof(f9153,plain,
    ( ~ spl31_1141
    | spl31_1152
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f9145,f5566,f9151,f8857])).

fof(f8857,plain,
    ( spl31_1141
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1141])])).

fof(f9151,plain,
    ( spl31_1152
  <=> ! [X6] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = u1_pre_topc(g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1152])])).

fof(f9145,plain,
    ( ! [X6] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = u1_pre_topc(g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))) )
    | ~ spl31_780 ),
    inference(superposition,[],[f5257,f5567])).

fof(f5257,plain,(
    ! [X26,X24,X25] :
      ( g1_pre_topc(X25,X26) != g1_pre_topc(X24,sK7(k1_zfmisc_1(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(X25)))
      | u1_pre_topc(g1_pre_topc(X24,sK7(k1_zfmisc_1(X24)))) = X26 ) ),
    inference(superposition,[],[f208,f1085])).

fof(f1085,plain,(
    ! [X1] : g1_pre_topc(X1,sK7(k1_zfmisc_1(X1))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X1,sK7(k1_zfmisc_1(X1)))),u1_pre_topc(g1_pre_topc(X1,sK7(k1_zfmisc_1(X1))))) ),
    inference(subsumption_resolution,[],[f1071,f751])).

fof(f751,plain,(
    ! [X0] : l1_pre_topc(g1_pre_topc(X0,sK7(k1_zfmisc_1(X0)))) ),
    inference(subsumption_resolution,[],[f745,f221])).

fof(f221,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc1_subset_1)).

fof(f745,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(X0,sK7(k1_zfmisc_1(X0))))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f210,f219])).

fof(f219,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_subset_1)).

fof(f1071,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(g1_pre_topc(X1,sK7(k1_zfmisc_1(X1))))
      | g1_pre_topc(X1,sK7(k1_zfmisc_1(X1))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X1,sK7(k1_zfmisc_1(X1)))),u1_pre_topc(g1_pre_topc(X1,sK7(k1_zfmisc_1(X1))))) ) ),
    inference(resolution,[],[f213,f714])).

fof(f714,plain,(
    ! [X2] : v1_pre_topc(g1_pre_topc(X2,sK7(k1_zfmisc_1(X2)))) ),
    inference(subsumption_resolution,[],[f711,f221])).

fof(f711,plain,(
    ! [X2] :
      ( v1_pre_topc(g1_pre_topc(X2,sK7(k1_zfmisc_1(X2))))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f209,f219])).

fof(f9141,plain,
    ( spl31_1124
    | ~ spl31_70
    | spl31_123
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8613,f1423,f896,f569,f8617])).

fof(f569,plain,
    ( spl31_70
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_70])])).

fof(f896,plain,
    ( spl31_123
  <=> ~ v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_123])])).

fof(f8613,plain,
    ( ! [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X1,u1_struct_0(sK0))
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f8612,f1424])).

fof(f8612,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8611,f570])).

fof(f570,plain,
    ( l1_struct_0(sK1)
    | ~ spl31_70 ),
    inference(avatar_component_clause,[],[f569])).

fof(f8611,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X1)
        | ~ l1_struct_0(sK1) )
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8585,f897])).

fof(f897,plain,
    ( ~ v7_struct_0(sK1)
    | ~ spl31_123 ),
    inference(avatar_component_clause,[],[f896])).

fof(f8585,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | v7_struct_0(sK1)
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X1)
        | ~ l1_struct_0(sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f5072,f1424])).

fof(f5072,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(X17,u1_struct_0(X16))
      | v7_struct_0(X16)
      | v1_xboole_0(X17)
      | v1_subset_1(X17,u1_struct_0(X16))
      | ~ v1_zfmisc_1(X17)
      | ~ l1_struct_0(X16) ) ),
    inference(resolution,[],[f5048,f224])).

fof(f5048,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f271,f274])).

fof(f271,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f154])).

fof(f154,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( ~ v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc9_tex_2)).

fof(f9137,plain,
    ( ~ spl31_1141
    | spl31_1150
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f9129,f5566,f9135,f8857])).

fof(f9135,plain,
    ( spl31_1150
  <=> ! [X6] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = u1_struct_0(g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1150])])).

fof(f9129,plain,
    ( ! [X6] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = u1_struct_0(g1_pre_topc(X6,sK7(k1_zfmisc_1(X6)))) )
    | ~ spl31_780 ),
    inference(superposition,[],[f5255,f5567])).

fof(f5255,plain,(
    ! [X19,X20,X18] :
      ( g1_pre_topc(X19,X20) != g1_pre_topc(X18,sK7(k1_zfmisc_1(X18)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))
      | u1_struct_0(g1_pre_topc(X18,sK7(k1_zfmisc_1(X18)))) = X19 ) ),
    inference(superposition,[],[f207,f1085])).

fof(f9125,plain,
    ( spl31_1124
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8349,f5208,f8617])).

fof(f5208,plain,
    ( spl31_742
  <=> ! [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_742])])).

fof(f8349,plain,
    ( ! [X2] :
        ( ~ v1_zfmisc_1(X2)
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X2,u1_struct_0(sK0)) )
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f224])).

fof(f5209,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(X1)
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl31_742 ),
    inference(avatar_component_clause,[],[f5208])).

fof(f8881,plain,
    ( ~ spl31_1141
    | spl31_1148
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8806,f5566,f373,f8879,f8857])).

fof(f8879,plain,
    ( spl31_1148
  <=> ! [X15] :
        ( g1_pre_topc(X15,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | u1_pre_topc(g1_pre_topc(X15,sK9)) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1148])])).

fof(f8806,plain,
    ( ! [X15] :
        ( g1_pre_topc(X15,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_pre_topc(g1_pre_topc(X15,sK9)) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) )
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(superposition,[],[f4770,f5567])).

fof(f8877,plain,
    ( ~ spl31_1141
    | spl31_1146
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8805,f5566,f373,f8875,f8857])).

fof(f8875,plain,
    ( spl31_1146
  <=> ! [X14] :
        ( g1_pre_topc(X14,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | u1_struct_0(g1_pre_topc(X14,sK9)) = u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1146])])).

fof(f8805,plain,
    ( ! [X14] :
        ( g1_pre_topc(X14,sK9) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_struct_0(g1_pre_topc(X14,sK9)) = u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) )
    | ~ spl31_16
    | ~ spl31_780 ),
    inference(superposition,[],[f4768,f5567])).

fof(f8866,plain,
    ( ~ spl31_1141
    | spl31_1144
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8791,f5566,f8864,f8857])).

fof(f8864,plain,
    ( spl31_1144
  <=> ! [X11,X10] :
        ( g1_pre_topc(X10,X11) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = X11 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1144])])).

fof(f8791,plain,
    ( ! [X10,X11] :
        ( g1_pre_topc(X10,X11) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = X11 )
    | ~ spl31_780 ),
    inference(superposition,[],[f208,f5567])).

fof(f8862,plain,
    ( ~ spl31_1141
    | spl31_1142
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8789,f5566,f8860,f8857])).

fof(f8860,plain,
    ( spl31_1142
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1142])])).

fof(f8789,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) = X6 )
    | ~ spl31_780 ),
    inference(superposition,[],[f207,f5567])).

fof(f8852,plain,
    ( ~ spl31_1139
    | spl31_816
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8845,f5566,f1906,f1574,f1423,f828,f324,f5746,f8850])).

fof(f8850,plain,
    ( spl31_1139
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1139])])).

fof(f8845,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ v2_tex_2(X5,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X5,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(duplicate_literal_removal,[],[f8844])).

fof(f8844,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X5,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X5,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(forward_demodulation,[],[f8843,f1575])).

fof(f8843,plain,
    ( ! [X5] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X5,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X5,sK1) )
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(subsumption_resolution,[],[f8842,f829])).

fof(f8842,plain,
    ( ! [X5] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(X5,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X5,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(inner_rewriting,[],[f8788])).

fof(f8788,plain,
    ( ! [X5] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | ~ v2_tex_2(X5,g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | v2_tex_2(X5,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_780 ),
    inference(superposition,[],[f3640,f5567])).

fof(f8840,plain,
    ( ~ spl31_1127
    | spl31_1134
    | ~ spl31_1137
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8786,f5566,f8838,f8832,f8811])).

fof(f8832,plain,
    ( spl31_1134
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1134])])).

fof(f8838,plain,
    ( spl31_1137
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1137])])).

fof(f8786,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ spl31_780 ),
    inference(superposition,[],[f993,f5567])).

fof(f993,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f205,f214])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & ~ v1_xboole_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(X0,X1))
        & ~ v2_struct_0(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc9_pre_topc)).

fof(f8827,plain,
    ( ~ spl31_1127
    | spl31_1132
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8784,f5566,f8825,f8811])).

fof(f8825,plain,
    ( spl31_1132
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1132])])).

fof(f8784,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
    | ~ spl31_780 ),
    inference(superposition,[],[f774,f5567])).

fof(f774,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f214,f209])).

fof(f8820,plain,
    ( ~ spl31_1127
    | spl31_1130
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8782,f5566,f8818,f8811])).

fof(f8818,plain,
    ( spl31_1130
  <=> ! [X3,X2] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | v2_tex_2(X3,g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | ~ v2_tex_2(X3,X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1130])])).

fof(f8782,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))
        | ~ l1_pre_topc(X2)
        | ~ v2_tex_2(X3,X2)
        | v2_tex_2(X3,g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))) )
    | ~ spl31_780 ),
    inference(superposition,[],[f312,f5567])).

fof(f8816,plain,
    ( ~ spl31_1127
    | spl31_1128
    | ~ spl31_780 ),
    inference(avatar_split_clause,[],[f8781,f5566,f8814,f8811])).

fof(f8814,plain,
    ( spl31_1128
  <=> ! [X1,X0] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | v2_tex_2(X1,X0)
        | ~ v2_tex_2(X1,g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1128])])).

fof(f8781,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | ~ v2_tex_2(X1,g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)))
        | v2_tex_2(X1,X0) )
    | ~ spl31_780 ),
    inference(superposition,[],[f312,f5567])).

fof(f8658,plain,
    ( ~ spl31_110
    | spl31_237
    | ~ spl31_1030 ),
    inference(avatar_contradiction_clause,[],[f8657])).

fof(f8657,plain,
    ( $false
    | ~ spl31_110
    | ~ spl31_237
    | ~ spl31_1030 ),
    inference(subsumption_resolution,[],[f8656,f1654])).

fof(f8656,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_1030 ),
    inference(subsumption_resolution,[],[f8655,f837])).

fof(f837,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl31_110
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_110])])).

fof(f8655,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_1030 ),
    inference(resolution,[],[f7704,f1054])).

fof(f1054,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(sK22(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f269,f274])).

fof(f269,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_zfmisc_1(sK22(X0)) ) ),
    inference(cnf_transformation,[],[f153])).

fof(f7704,plain,
    ( v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_1030 ),
    inference(avatar_component_clause,[],[f7703])).

fof(f7703,plain,
    ( spl31_1030
  <=> v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1030])])).

fof(f8619,plain,
    ( spl31_236
    | spl31_1124
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8615,f1574,f836,f8617,f1650])).

fof(f1650,plain,
    ( spl31_236
  <=> v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_236])])).

fof(f8615,plain,
    ( ! [X2] :
        ( v1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_zfmisc_1(X2) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f8614,f1575])).

fof(f8614,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_zfmisc_1(X2) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8586,f837])).

fof(f8586,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_zfmisc_1(X2)
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f5072,f1575])).

fof(f8608,plain,
    ( spl31_570
    | ~ spl31_68
    | spl31_121
    | ~ spl31_670
    | spl31_831
    | ~ spl31_882 ),
    inference(avatar_split_clause,[],[f8607,f6301,f5874,f4569,f886,f562,f3951])).

fof(f3951,plain,
    ( spl31_570
  <=> v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_570])])).

fof(f562,plain,
    ( spl31_68
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_68])])).

fof(f886,plain,
    ( spl31_121
  <=> ~ v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_121])])).

fof(f4569,plain,
    ( spl31_670
  <=> r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_670])])).

fof(f5874,plain,
    ( spl31_831
  <=> ~ v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_831])])).

fof(f6301,plain,
    ( spl31_882
  <=> v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_882])])).

fof(f8607,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_670
    | ~ spl31_831
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8606,f563])).

fof(f563,plain,
    ( l1_struct_0(sK0)
    | ~ spl31_68 ),
    inference(avatar_component_clause,[],[f562])).

fof(f8606,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_670
    | ~ spl31_831
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8605,f6302])).

fof(f6302,plain,
    ( v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_882 ),
    inference(avatar_component_clause,[],[f6301])).

fof(f8605,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_670
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f8604,f5875])).

fof(f5875,plain,
    ( ~ v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_831 ),
    inference(avatar_component_clause,[],[f5874])).

fof(f8604,plain,
    ( v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_670 ),
    inference(subsumption_resolution,[],[f8566,f887])).

fof(f887,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_121 ),
    inference(avatar_component_clause,[],[f886])).

fof(f8566,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_670 ),
    inference(resolution,[],[f5072,f4570])).

fof(f4570,plain,
    ( r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_670 ),
    inference(avatar_component_clause,[],[f4569])).

fof(f8603,plain,
    ( spl31_718
    | spl31_720
    | ~ spl31_68
    | spl31_121
    | ~ spl31_520
    | ~ spl31_562 ),
    inference(avatar_split_clause,[],[f8602,f3900,f3196,f886,f562,f4905,f4896])).

fof(f4896,plain,
    ( spl31_718
  <=> v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_718])])).

fof(f4905,plain,
    ( spl31_720
  <=> v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_720])])).

fof(f3196,plain,
    ( spl31_520
  <=> r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_520])])).

fof(f3900,plain,
    ( spl31_562
  <=> v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_562])])).

fof(f8602,plain,
    ( v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_520
    | ~ spl31_562 ),
    inference(subsumption_resolution,[],[f8601,f563])).

fof(f8601,plain,
    ( v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_520
    | ~ spl31_562 ),
    inference(subsumption_resolution,[],[f8600,f3901])).

fof(f3901,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_562 ),
    inference(avatar_component_clause,[],[f3900])).

fof(f8600,plain,
    ( v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_520 ),
    inference(subsumption_resolution,[],[f8564,f887])).

fof(f8564,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_520 ),
    inference(resolution,[],[f5072,f3197])).

fof(f3197,plain,
    ( r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_520 ),
    inference(avatar_component_clause,[],[f3196])).

fof(f8599,plain,
    ( spl31_710
    | ~ spl31_68
    | spl31_121
    | ~ spl31_496
    | ~ spl31_564
    | spl31_713 ),
    inference(avatar_split_clause,[],[f8598,f4869,f3908,f3085,f886,f562,f4863])).

fof(f4863,plain,
    ( spl31_710
  <=> v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_710])])).

fof(f3908,plain,
    ( spl31_564
  <=> v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_564])])).

fof(f4869,plain,
    ( spl31_713
  <=> ~ v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_713])])).

fof(f8598,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_496
    | ~ spl31_564
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8597,f563])).

fof(f8597,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_496
    | ~ spl31_564
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8596,f3909])).

fof(f3909,plain,
    ( v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_564 ),
    inference(avatar_component_clause,[],[f3908])).

fof(f8596,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_496
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8595,f4870])).

fof(f4870,plain,
    ( ~ v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_713 ),
    inference(avatar_component_clause,[],[f4869])).

fof(f8595,plain,
    ( v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_121
    | ~ spl31_496 ),
    inference(subsumption_resolution,[],[f8562,f887])).

fof(f8562,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(sK0)
    | ~ spl31_496 ),
    inference(resolution,[],[f5072,f3086])).

fof(f8594,plain,
    ( spl31_738
    | ~ spl31_2
    | ~ spl31_68
    | spl31_121
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8593,f1423,f886,f562,f324,f5182])).

fof(f8593,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X0))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8592,f563])).

fof(f8592,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X0))
        | ~ l1_struct_0(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_121
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8560,f887])).

fof(f8560,plain,
    ( ! [X0] :
        ( v7_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X0))
        | ~ l1_struct_0(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f5072,f3321])).

fof(f8557,plain,
    ( ~ spl31_237
    | spl31_1122
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8553,f1574,f836,f811,f8555,f1653])).

fof(f8555,plain,
    ( spl31_1122
  <=> ! [X2] :
        ( ~ v1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(X2)
        | ~ r1_tarski(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1122])])).

fof(f8553,plain,
    ( ! [X2] :
        ( ~ v1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_xboole_0(X2)
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f8552,f1575])).

fof(f8552,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8551,f812])).

fof(f8551,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8542,f837])).

fof(f8542,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f4828,f1575])).

fof(f4828,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(X17,u1_struct_0(X16))
      | ~ l1_struct_0(X16)
      | v2_struct_0(X16)
      | v1_xboole_0(X17)
      | ~ v1_subset_1(X17,u1_struct_0(X16))
      | ~ v7_struct_0(X16) ) ),
    inference(resolution,[],[f258,f224])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ v1_xboole_0(X1)
           => ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc6_tex_2)).

fof(f8509,plain,
    ( spl31_1096
    | ~ spl31_733
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8508,f5208,f5143,f8400])).

fof(f8400,plain,
    ( spl31_1096
  <=> v1_xboole_0(sK27(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1096])])).

fof(f5143,plain,
    ( spl31_733
  <=> ~ v1_zfmisc_1(sK27(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_733])])).

fof(f8508,plain,
    ( ~ v1_zfmisc_1(sK27(u1_struct_0(sK0)))
    | v1_xboole_0(sK27(u1_struct_0(sK0)))
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8345,f291])).

fof(f291,plain,(
    ! [X0] : ~ v1_subset_1(sK27(X0),X0) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc3_subset_1)).

fof(f8345,plain,
    ( ~ v1_zfmisc_1(sK27(u1_struct_0(sK0)))
    | v1_xboole_0(sK27(u1_struct_0(sK0)))
    | v1_subset_1(sK27(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f290])).

fof(f290,plain,(
    ! [X0] : m1_subset_1(sK27(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

fof(f8507,plain,
    ( spl31_1120
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8422,f8400,f373,f8505])).

fof(f8505,plain,
    ( spl31_1120
  <=> sK9 = sK27(sK27(sK27(sK27(sK27(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1120])])).

fof(f8422,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK27(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f1046])).

fof(f1046,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK9 = sK27(sK27(sK27(sK27(X2)))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f819,f635])).

fof(f635,plain,(
    ! [X0] :
      ( v1_xboole_0(sK27(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f218,f290])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc1_subset_1)).

fof(f819,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK9 = sK27(sK27(sK27(X2))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f667,f635])).

fof(f667,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK9 = sK27(sK27(X0)) )
    | ~ spl31_16 ),
    inference(resolution,[],[f660,f635])).

fof(f660,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK9 = sK27(X0) )
    | ~ spl31_16 ),
    inference(resolution,[],[f635,f625])).

fof(f8401,plain,
    ( v1_xboole_0(sK27(u1_struct_0(sK0)))
    | ~ spl31_1096 ),
    inference(avatar_component_clause,[],[f8400])).

fof(f8500,plain,
    ( spl31_1118
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8421,f8400,f373,f8498])).

fof(f8498,plain,
    ( spl31_1118
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK27(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1118])])).

fof(f8421,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK27(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f1041])).

fof(f1041,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK9 = sK27(sK5(k1_zfmisc_1(sK27(X2)))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f668,f635])).

fof(f668,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK9 = sK27(sK5(k1_zfmisc_1(X1))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f660,f639])).

fof(f639,plain,(
    ! [X5] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X5)))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f218,f215])).

fof(f215,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',existence_m1_subset_1)).

fof(f8493,plain,
    ( spl31_1116
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8420,f8400,f373,f8491])).

fof(f8491,plain,
    ( spl31_1116
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK27(u1_struct_0(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1116])])).

fof(f8420,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK27(u1_struct_0(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f1036])).

fof(f1036,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK5(k1_zfmisc_1(sK27(sK27(X2)))) = sK9 )
    | ~ spl31_16 ),
    inference(resolution,[],[f792,f635])).

fof(f792,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK5(k1_zfmisc_1(sK27(X2))) = sK9 )
    | ~ spl31_16 ),
    inference(resolution,[],[f663,f635])).

fof(f663,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK5(k1_zfmisc_1(X0)) = sK9 )
    | ~ spl31_16 ),
    inference(resolution,[],[f639,f625])).

fof(f8486,plain,
    ( spl31_1114
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8418,f8400,f373,f8484])).

fof(f8484,plain,
    ( spl31_1114
  <=> sK9 = sK27(sK27(sK27(sK27(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1114])])).

fof(f8418,plain,
    ( sK9 = sK27(sK27(sK27(sK27(u1_struct_0(sK0)))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f819])).

fof(f8479,plain,
    ( spl31_1112
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8417,f8400,f373,f8477])).

fof(f8477,plain,
    ( spl31_1112
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1112])])).

fof(f8417,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f817])).

fof(f817,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK9 = sK27(sK27(sK5(k1_zfmisc_1(X1)))) )
    | ~ spl31_16 ),
    inference(resolution,[],[f667,f639])).

fof(f8472,plain,
    ( spl31_1110
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8416,f8400,f373,f8470])).

fof(f8470,plain,
    ( spl31_1110
  <=> sK5(k1_zfmisc_1(sK27(sK27(u1_struct_0(sK0))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1110])])).

fof(f8416,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(u1_struct_0(sK0))))) = sK9
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f792])).

fof(f8465,plain,
    ( spl31_1108
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8415,f8400,f373,f8463])).

fof(f8463,plain,
    ( spl31_1108
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1108])])).

fof(f8415,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f790])).

fof(f790,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(X1)))) = sK9 )
    | ~ spl31_16 ),
    inference(resolution,[],[f663,f639])).

fof(f8458,plain,
    ( spl31_1106
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8414,f8400,f373,f8456])).

fof(f8456,plain,
    ( spl31_1106
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1106])])).

fof(f8414,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f668])).

fof(f8451,plain,
    ( spl31_1104
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8413,f8400,f373,f8449])).

fof(f8449,plain,
    ( spl31_1104
  <=> sK9 = sK27(sK27(sK27(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1104])])).

fof(f8413,plain,
    ( sK9 = sK27(sK27(sK27(u1_struct_0(sK0))))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f667])).

fof(f8444,plain,
    ( spl31_1102
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8411,f8400,f373,f8442])).

fof(f8442,plain,
    ( spl31_1102
  <=> sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1102])])).

fof(f8411,plain,
    ( sK5(k1_zfmisc_1(sK27(u1_struct_0(sK0)))) = sK9
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f663])).

fof(f8437,plain,
    ( spl31_1100
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8409,f8400,f373,f8435])).

fof(f8435,plain,
    ( spl31_1100
  <=> sK9 = sK27(sK27(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1100])])).

fof(f8409,plain,
    ( sK9 = sK27(sK27(u1_struct_0(sK0)))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f660])).

fof(f8430,plain,
    ( spl31_1098
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(avatar_split_clause,[],[f8408,f8400,f373,f8428])).

fof(f8428,plain,
    ( spl31_1098
  <=> sK9 = sK27(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1098])])).

fof(f8408,plain,
    ( sK9 = sK27(u1_struct_0(sK0))
    | ~ spl31_16
    | ~ spl31_1096 ),
    inference(resolution,[],[f8401,f625])).

fof(f8405,plain,
    ( spl31_1060
    | ~ spl31_736
    | ~ spl31_742
    | spl31_1063 ),
    inference(avatar_split_clause,[],[f8404,f7933,f5208,f5161,f7927])).

fof(f7927,plain,
    ( spl31_1060
  <=> v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1060])])).

fof(f5161,plain,
    ( spl31_736
  <=> v1_zfmisc_1(sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_736])])).

fof(f7933,plain,
    ( spl31_1063
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1063])])).

fof(f8404,plain,
    ( v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl31_736
    | ~ spl31_742
    | ~ spl31_1063 ),
    inference(subsumption_resolution,[],[f8403,f7934])).

fof(f7934,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_1063 ),
    inference(avatar_component_clause,[],[f7933])).

fof(f8403,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl31_736
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8350,f5162])).

fof(f5162,plain,
    ( v1_zfmisc_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_736 ),
    inference(avatar_component_clause,[],[f5161])).

fof(f8350,plain,
    ( ~ v1_zfmisc_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f215])).

fof(f8402,plain,
    ( spl31_1096
    | ~ spl31_732
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8395,f5208,f5146,f8400])).

fof(f5146,plain,
    ( spl31_732
  <=> v1_zfmisc_1(sK27(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_732])])).

fof(f8395,plain,
    ( v1_xboole_0(sK27(u1_struct_0(sK0)))
    | ~ spl31_732
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8394,f291])).

fof(f8394,plain,
    ( v1_xboole_0(sK27(u1_struct_0(sK0)))
    | v1_subset_1(sK27(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_732
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8345,f5147])).

fof(f5147,plain,
    ( v1_zfmisc_1(sK27(u1_struct_0(sK0)))
    | ~ spl31_732 ),
    inference(avatar_component_clause,[],[f5146])).

fof(f8393,plain,
    ( spl31_874
    | spl31_89
    | ~ spl31_742
    | spl31_877
    | ~ spl31_878 ),
    inference(avatar_split_clause,[],[f8392,f6280,f6274,f5208,f650,f6271])).

fof(f6271,plain,
    ( spl31_874
  <=> v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_874])])).

fof(f650,plain,
    ( spl31_89
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_89])])).

fof(f6274,plain,
    ( spl31_877
  <=> ~ v1_xboole_0(sK26(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_877])])).

fof(f6280,plain,
    ( spl31_878
  <=> v1_zfmisc_1(sK26(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_878])])).

fof(f8392,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_742
    | ~ spl31_877
    | ~ spl31_878 ),
    inference(subsumption_resolution,[],[f8391,f651])).

fof(f651,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_89 ),
    inference(avatar_component_clause,[],[f650])).

fof(f8391,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742
    | ~ spl31_877
    | ~ spl31_878 ),
    inference(subsumption_resolution,[],[f8390,f6275])).

fof(f6275,plain,
    ( ~ v1_xboole_0(sK26(u1_struct_0(sK0)))
    | ~ spl31_877 ),
    inference(avatar_component_clause,[],[f6274])).

fof(f8390,plain,
    ( v1_xboole_0(sK26(u1_struct_0(sK0)))
    | v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742
    | ~ spl31_878 ),
    inference(subsumption_resolution,[],[f8344,f6281])).

fof(f6281,plain,
    ( v1_zfmisc_1(sK26(u1_struct_0(sK0)))
    | ~ spl31_878 ),
    inference(avatar_component_clause,[],[f6280])).

fof(f8344,plain,
    ( ~ v1_zfmisc_1(sK26(u1_struct_0(sK0)))
    | v1_xboole_0(sK26(u1_struct_0(sK0)))
    | v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f286])).

fof(f286,plain,(
    ! [X0] :
      ( m1_subset_1(sK26(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f93])).

fof(f93,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc3_realset1)).

fof(f8389,plain,
    ( spl31_868
    | spl31_89
    | ~ spl31_742
    | spl31_871
    | ~ spl31_872 ),
    inference(avatar_split_clause,[],[f8388,f6260,f6254,f5208,f650,f6251])).

fof(f6251,plain,
    ( spl31_868
  <=> v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_868])])).

fof(f6254,plain,
    ( spl31_871
  <=> ~ v1_xboole_0(sK25(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_871])])).

fof(f6260,plain,
    ( spl31_872
  <=> v1_zfmisc_1(sK25(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_872])])).

fof(f8388,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_742
    | ~ spl31_871
    | ~ spl31_872 ),
    inference(subsumption_resolution,[],[f8387,f651])).

fof(f8387,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742
    | ~ spl31_871
    | ~ spl31_872 ),
    inference(subsumption_resolution,[],[f8386,f6255])).

fof(f6255,plain,
    ( ~ v1_xboole_0(sK25(u1_struct_0(sK0)))
    | ~ spl31_871 ),
    inference(avatar_component_clause,[],[f6254])).

fof(f8386,plain,
    ( v1_xboole_0(sK25(u1_struct_0(sK0)))
    | v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742
    | ~ spl31_872 ),
    inference(subsumption_resolution,[],[f8343,f6261])).

fof(f6261,plain,
    ( v1_zfmisc_1(sK25(u1_struct_0(sK0)))
    | ~ spl31_872 ),
    inference(avatar_component_clause,[],[f6260])).

fof(f8343,plain,
    ( ~ v1_zfmisc_1(sK25(u1_struct_0(sK0)))
    | v1_xboole_0(sK25(u1_struct_0(sK0)))
    | v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f283])).

fof(f283,plain,(
    ! [X0] :
      ( m1_subset_1(sK25(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_tex_2)).

fof(f8385,plain,
    ( spl31_1006
    | spl31_1094
    | spl31_89
    | ~ spl31_730
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8378,f5208,f5139,f650,f8383,f7435])).

fof(f7435,plain,
    ( spl31_1006
  <=> v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1006])])).

fof(f8383,plain,
    ( spl31_1094
  <=> v1_xboole_0(sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1094])])).

fof(f5139,plain,
    ( spl31_730
  <=> v1_zfmisc_1(sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_730])])).

fof(f8378,plain,
    ( v1_xboole_0(sK7(u1_struct_0(sK0)))
    | v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_730
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8377,f651])).

fof(f8377,plain,
    ( v1_xboole_0(sK7(u1_struct_0(sK0)))
    | v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_730
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8341,f5140])).

fof(f5140,plain,
    ( v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | ~ spl31_730 ),
    inference(avatar_component_clause,[],[f5139])).

fof(f8341,plain,
    ( ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v1_xboole_0(sK7(u1_struct_0(sK0)))
    | v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f219])).

fof(f8376,plain,
    ( spl31_570
    | ~ spl31_674
    | ~ spl31_742
    | spl31_831
    | ~ spl31_882 ),
    inference(avatar_split_clause,[],[f8375,f6301,f5874,f5208,f4585,f3951])).

fof(f4585,plain,
    ( spl31_674
  <=> m1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_674])])).

fof(f8375,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674
    | ~ spl31_742
    | ~ spl31_831
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8374,f5875])).

fof(f8374,plain,
    ( v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674
    | ~ spl31_742
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8336,f6302])).

fof(f8336,plain,
    ( ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f4586])).

fof(f4586,plain,
    ( m1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_674 ),
    inference(avatar_component_clause,[],[f4585])).

fof(f8373,plain,
    ( spl31_1052
    | ~ spl31_68
    | spl31_101
    | ~ spl31_728
    | ~ spl31_742
    | spl31_1055 ),
    inference(avatar_split_clause,[],[f8372,f7906,f5208,f5131,f726,f562,f7900])).

fof(f7900,plain,
    ( spl31_1052
  <=> v1_subset_1(sK16(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1052])])).

fof(f726,plain,
    ( spl31_101
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_101])])).

fof(f5131,plain,
    ( spl31_728
  <=> v1_zfmisc_1(sK16(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_728])])).

fof(f7906,plain,
    ( spl31_1055
  <=> ~ v1_xboole_0(sK16(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1055])])).

fof(f8372,plain,
    ( v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_728
    | ~ spl31_742
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f8371,f727])).

fof(f727,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl31_101 ),
    inference(avatar_component_clause,[],[f726])).

fof(f8371,plain,
    ( v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_728
    | ~ spl31_742
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f8370,f563])).

fof(f8370,plain,
    ( v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_728
    | ~ spl31_742
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f8369,f7907])).

fof(f7907,plain,
    ( ~ v1_xboole_0(sK16(sK0))
    | ~ spl31_1055 ),
    inference(avatar_component_clause,[],[f7906])).

fof(f8369,plain,
    ( v1_xboole_0(sK16(sK0))
    | v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_728
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8333,f5132])).

fof(f5132,plain,
    ( v1_zfmisc_1(sK16(sK0))
    | ~ spl31_728 ),
    inference(avatar_component_clause,[],[f5131])).

fof(f8333,plain,
    ( ~ v1_zfmisc_1(sK16(sK0))
    | v1_xboole_0(sK16(sK0))
    | v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f246])).

fof(f246,plain,(
    ! [X0] :
      ( m1_subset_1(sK16(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc4_struct_0)).

fof(f8368,plain,
    ( spl31_718
    | spl31_720
    | ~ spl31_402
    | ~ spl31_562
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8367,f5208,f3900,f2613,f4905,f4896])).

fof(f2613,plain,
    ( spl31_402
  <=> m1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_402])])).

fof(f8367,plain,
    ( v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_402
    | ~ spl31_562
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8332,f3901])).

fof(f8332,plain,
    ( ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_402
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f2614])).

fof(f2614,plain,
    ( m1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_402 ),
    inference(avatar_component_clause,[],[f2613])).

fof(f8366,plain,
    ( spl31_714
    | ~ spl31_400
    | ~ spl31_566
    | spl31_717
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8365,f5208,f4886,f3916,f2604,f4880])).

fof(f4880,plain,
    ( spl31_714
  <=> v1_subset_1(sK16(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_714])])).

fof(f2604,plain,
    ( spl31_400
  <=> m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_400])])).

fof(f3916,plain,
    ( spl31_566
  <=> v1_zfmisc_1(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_566])])).

fof(f4886,plain,
    ( spl31_717
  <=> ~ v1_xboole_0(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_717])])).

fof(f8365,plain,
    ( v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400
    | ~ spl31_566
    | ~ spl31_717
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8364,f4887])).

fof(f4887,plain,
    ( ~ v1_xboole_0(sK16(sK1))
    | ~ spl31_717 ),
    inference(avatar_component_clause,[],[f4886])).

fof(f8364,plain,
    ( v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400
    | ~ spl31_566
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8331,f3917])).

fof(f3917,plain,
    ( v1_zfmisc_1(sK16(sK1))
    | ~ spl31_566 ),
    inference(avatar_component_clause,[],[f3916])).

fof(f8331,plain,
    ( ~ v1_zfmisc_1(sK16(sK1))
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f2605])).

fof(f2605,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_400 ),
    inference(avatar_component_clause,[],[f2604])).

fof(f8363,plain,
    ( spl31_862
    | ~ spl31_68
    | spl31_101
    | ~ spl31_742
    | spl31_865
    | ~ spl31_866 ),
    inference(avatar_split_clause,[],[f8362,f6240,f6234,f5208,f726,f562,f6231])).

fof(f6231,plain,
    ( spl31_862
  <=> v1_subset_1(sK15(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_862])])).

fof(f6234,plain,
    ( spl31_865
  <=> ~ v1_xboole_0(sK15(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_865])])).

fof(f6240,plain,
    ( spl31_866
  <=> v1_zfmisc_1(sK15(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_866])])).

fof(f8362,plain,
    ( v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_742
    | ~ spl31_865
    | ~ spl31_866 ),
    inference(subsumption_resolution,[],[f8361,f727])).

fof(f8361,plain,
    ( v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_742
    | ~ spl31_865
    | ~ spl31_866 ),
    inference(subsumption_resolution,[],[f8360,f563])).

fof(f8360,plain,
    ( v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_742
    | ~ spl31_865
    | ~ spl31_866 ),
    inference(subsumption_resolution,[],[f8359,f6235])).

fof(f6235,plain,
    ( ~ v1_xboole_0(sK15(sK0))
    | ~ spl31_865 ),
    inference(avatar_component_clause,[],[f6234])).

fof(f8359,plain,
    ( v1_xboole_0(sK15(sK0))
    | v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_742
    | ~ spl31_866 ),
    inference(subsumption_resolution,[],[f8330,f6241])).

fof(f6241,plain,
    ( v1_zfmisc_1(sK15(sK0))
    | ~ spl31_866 ),
    inference(avatar_component_clause,[],[f6240])).

fof(f8330,plain,
    ( ~ v1_zfmisc_1(sK15(sK0))
    | v1_xboole_0(sK15(sK0))
    | v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f243])).

fof(f8358,plain,
    ( spl31_710
    | ~ spl31_364
    | ~ spl31_564
    | spl31_713
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8357,f5208,f4869,f3908,f2352,f4863])).

fof(f2352,plain,
    ( spl31_364
  <=> m1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_364])])).

fof(f8357,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364
    | ~ spl31_564
    | ~ spl31_713
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8356,f4870])).

fof(f8356,plain,
    ( v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364
    | ~ spl31_564
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8329,f3909])).

fof(f8329,plain,
    ( ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f2353])).

fof(f2353,plain,
    ( m1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_364 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f8355,plain,
    ( spl31_706
    | ~ spl31_362
    | ~ spl31_428
    | spl31_709
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8354,f5208,f4853,f2734,f2343,f4847])).

fof(f4847,plain,
    ( spl31_706
  <=> v1_subset_1(sK15(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_706])])).

fof(f2343,plain,
    ( spl31_362
  <=> m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_362])])).

fof(f2734,plain,
    ( spl31_428
  <=> v1_zfmisc_1(sK15(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_428])])).

fof(f4853,plain,
    ( spl31_709
  <=> ~ v1_xboole_0(sK15(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_709])])).

fof(f8354,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362
    | ~ spl31_428
    | ~ spl31_709
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8353,f4854])).

fof(f4854,plain,
    ( ~ v1_xboole_0(sK15(sK1))
    | ~ spl31_709 ),
    inference(avatar_component_clause,[],[f4853])).

fof(f8353,plain,
    ( v1_xboole_0(sK15(sK1))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362
    | ~ spl31_428
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f8328,f2735])).

fof(f2735,plain,
    ( v1_zfmisc_1(sK15(sK1))
    | ~ spl31_428 ),
    inference(avatar_component_clause,[],[f2734])).

fof(f8328,plain,
    ( ~ v1_zfmisc_1(sK15(sK1))
    | v1_xboole_0(sK15(sK1))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f2344])).

fof(f2344,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_362 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f8351,plain,
    ( spl31_738
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f8326,f5208,f1423,f324,f5182])).

fof(f8326,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(sK4(sK1,X0))
        | v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f1975])).

fof(f8309,plain,
    ( spl31_660
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f8303,f4545,f4529])).

fof(f4529,plain,
    ( spl31_660
  <=> r1_tarski(sK21(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_660])])).

fof(f4545,plain,
    ( spl31_664
  <=> m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_664])])).

fof(f8303,plain,
    ( r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f225])).

fof(f4546,plain,
    ( m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_664 ),
    inference(avatar_component_clause,[],[f4545])).

fof(f8277,plain,
    ( spl31_122
    | spl31_1006
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_730 ),
    inference(avatar_split_clause,[],[f8276,f5139,f1423,f569,f7435,f893])).

fof(f893,plain,
    ( spl31_122
  <=> v7_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_122])])).

fof(f8276,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_730 ),
    inference(subsumption_resolution,[],[f8275,f5140])).

fof(f8275,plain,
    ( ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f8274,f1424])).

fof(f8274,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK1)))
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7758,f570])).

fof(f7758,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK1)))
    | ~ spl31_194 ),
    inference(superposition,[],[f5086,f1424])).

fof(f5086,plain,(
    ! [X8] :
      ( v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_zfmisc_1(sK7(u1_struct_0(X8))) ) ),
    inference(subsumption_resolution,[],[f5085,f4057])).

fof(f4057,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(u1_struct_0(X12))
      | v7_struct_0(X12)
      | ~ l1_struct_0(X12) ) ),
    inference(subsumption_resolution,[],[f4046,f1049])).

fof(f1049,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK20(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f260,f274])).

fof(f260,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(sK20(X0)) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f4046,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | v7_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12))
      | v1_xboole_0(sK20(X12)) ) ),
    inference(resolution,[],[f3971,f218])).

fof(f5085,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v7_struct_0(X8)
      | v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | ~ v1_zfmisc_1(sK7(u1_struct_0(X8)))
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f5064,f220])).

fof(f220,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f5064,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v7_struct_0(X8)
      | v1_xboole_0(sK7(u1_struct_0(X8)))
      | v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | ~ v1_zfmisc_1(sK7(u1_struct_0(X8)))
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(resolution,[],[f5048,f219])).

fof(f8273,plain,
    ( ~ spl31_123
    | ~ spl31_1007
    | ~ spl31_70
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8272,f1423,f650,f569,f7438,f896])).

fof(f7438,plain,
    ( spl31_1007
  <=> ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1007])])).

fof(f8272,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8271,f651])).

fof(f8271,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7430,f1424])).

fof(f7430,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7425,f570])).

fof(f7425,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_194 ),
    inference(superposition,[],[f4909,f1424])).

fof(f4909,plain,(
    ! [X8] :
      ( ~ v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | ~ l1_struct_0(X8)
      | ~ v7_struct_0(X8)
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f4908,f220])).

fof(f4908,plain,(
    ! [X8] :
      ( ~ v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(sK7(u1_struct_0(X8)))
      | ~ v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f4820,f242])).

fof(f242,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f62])).

fof(f62,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc1_struct_0)).

fof(f4820,plain,(
    ! [X8] :
      ( ~ v7_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v2_struct_0(X8)
      | v1_xboole_0(sK7(u1_struct_0(X8)))
      | ~ v1_subset_1(sK7(u1_struct_0(X8)),u1_struct_0(X8))
      | v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(resolution,[],[f258,f219])).

fof(f8270,plain,
    ( spl31_236
    | spl31_1006
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_730 ),
    inference(avatar_split_clause,[],[f8269,f5139,f1574,f836,f7435,f1650])).

fof(f8269,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_730 ),
    inference(subsumption_resolution,[],[f8268,f5140])).

fof(f8268,plain,
    ( ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f8267,f1575])).

fof(f8267,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7759,f837])).

fof(f7759,plain,
    ( v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_220 ),
    inference(superposition,[],[f5086,f1575])).

fof(f8266,plain,
    ( ~ spl31_237
    | ~ spl31_1007
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8265,f1574,f836,f650,f7438,f1653])).

fof(f8265,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8264,f651])).

fof(f8264,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7441,f1575])).

fof(f7441,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7426,f837])).

fof(f7426,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f4909,f1575])).

fof(f8263,plain,
    ( spl31_810
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f8262,f4718,f726,f562,f886,f5693])).

fof(f5693,plain,
    ( spl31_810
  <=> v1_zfmisc_1(sK22(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_810])])).

fof(f4718,plain,
    ( spl31_702
  <=> m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_702])])).

fof(f8262,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f8261,f727])).

fof(f8261,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f6854,f563])).

fof(f6854,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f4985])).

fof(f4985,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f4984,f280])).

fof(f280,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc2_realset1)).

fof(f4984,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f257,f258])).

fof(f257,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc7_tex_2)).

fof(f4719,plain,
    ( m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_702 ),
    inference(avatar_component_clause,[],[f4718])).

fof(f8260,plain,
    ( spl31_810
    | ~ spl31_117
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f6857,f4718,f869,f5693])).

fof(f869,plain,
    ( spl31_117
  <=> ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_117])])).

fof(f6857,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f166])).

fof(f166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc5_funct_1)).

fof(f8259,plain,
    ( ~ spl31_117
    | spl31_810
    | ~ spl31_724 ),
    inference(avatar_split_clause,[],[f6885,f4990,f5693,f869])).

fof(f4990,plain,
    ( spl31_724
  <=> r1_tarski(sK22(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_724])])).

fof(f6885,plain,
    ( v1_zfmisc_1(sK22(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_724 ),
    inference(resolution,[],[f4991,f854])).

fof(f854,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,X6)
      | v1_zfmisc_1(X7)
      | ~ v1_zfmisc_1(X6) ) ),
    inference(resolution,[],[f282,f224])).

fof(f4991,plain,
    ( r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_724 ),
    inference(avatar_component_clause,[],[f4990])).

fof(f8258,plain,
    ( ~ spl31_121
    | spl31_810
    | ~ spl31_68
    | spl31_101
    | ~ spl31_724 ),
    inference(avatar_split_clause,[],[f8257,f4990,f726,f562,f5693,f886])).

fof(f8257,plain,
    ( v1_zfmisc_1(sK22(sK1))
    | ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_724 ),
    inference(subsumption_resolution,[],[f8256,f727])).

fof(f8256,plain,
    ( v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_724 ),
    inference(subsumption_resolution,[],[f7349,f563])).

fof(f7349,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ v7_struct_0(sK0)
    | ~ spl31_724 ),
    inference(resolution,[],[f5016,f4991])).

fof(f5016,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(X17,u1_struct_0(X16))
      | ~ l1_struct_0(X16)
      | v2_struct_0(X16)
      | v1_zfmisc_1(X17)
      | ~ v7_struct_0(X16) ) ),
    inference(resolution,[],[f4985,f224])).

fof(f8255,plain,
    ( ~ spl31_811
    | spl31_812
    | spl31_116
    | spl31_669
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f8112,f4718,f4561,f866,f5702,f5696])).

fof(f5696,plain,
    ( spl31_811
  <=> ~ v1_zfmisc_1(sK22(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_811])])).

fof(f5702,plain,
    ( spl31_812
  <=> v1_xboole_0(sK22(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_812])])).

fof(f866,plain,
    ( spl31_116
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_116])])).

fof(f4561,plain,
    ( spl31_669
  <=> ~ v1_subset_1(sK22(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_669])])).

fof(f8112,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK22(sK1))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_669
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f7785,f4562])).

fof(f4562,plain,
    ( ~ v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_669 ),
    inference(avatar_component_clause,[],[f4561])).

fof(f7785,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f7761,f4719])).

fof(f7761,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1) ) ),
    inference(subsumption_resolution,[],[f303,f218])).

fof(f303,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ( ~ v1_subset_1(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( ~ v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc5_tex_2)).

fof(f8254,plain,
    ( ~ spl31_811
    | spl31_812
    | spl31_120
    | ~ spl31_68
    | spl31_669
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f8153,f4718,f4561,f562,f883,f5702,f5696])).

fof(f883,plain,
    ( spl31_120
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_120])])).

fof(f8153,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_669
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f8152,f4562])).

fof(f8152,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f6855,f563])).

fof(f6855,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f5048])).

fof(f8253,plain,
    ( spl31_718
    | spl31_720
    | spl31_116
    | ~ spl31_402
    | ~ spl31_562 ),
    inference(avatar_split_clause,[],[f8252,f3900,f2613,f866,f4905,f4896])).

fof(f8252,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_402
    | ~ spl31_562 ),
    inference(subsumption_resolution,[],[f7779,f3901])).

fof(f7779,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f7761,f2614])).

fof(f8251,plain,
    ( spl31_720
    | ~ spl31_719
    | ~ spl31_117
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f7397,f2613,f869,f4899,f4905])).

fof(f4899,plain,
    ( spl31_719
  <=> ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_719])])).

fof(f7397,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f7379,f2614])).

fof(f7379,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f293,f218])).

fof(f293,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc1_tex_2)).

fof(f8250,plain,
    ( spl31_720
    | spl31_236
    | spl31_718
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_562 ),
    inference(avatar_split_clause,[],[f8249,f3900,f1574,f836,f4896,f1650,f4905])).

fof(f8249,plain,
    ( v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_562 ),
    inference(subsumption_resolution,[],[f8248,f3901])).

fof(f8248,plain,
    ( v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7868,f837])).

fof(f7868,plain,
    ( v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f5084,f1575])).

fof(f5084,plain,(
    ! [X4] :
      ( v1_subset_1(sK16(X4),u1_struct_0(X4))
      | v7_struct_0(X4)
      | v1_xboole_0(sK16(X4))
      | ~ l1_struct_0(X4)
      | ~ v1_zfmisc_1(sK16(X4)) ) ),
    inference(subsumption_resolution,[],[f5080,f274])).

fof(f5080,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v7_struct_0(X4)
      | v1_xboole_0(sK16(X4))
      | v1_subset_1(sK16(X4),u1_struct_0(X4))
      | ~ v1_zfmisc_1(sK16(X4))
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f5058])).

fof(f5058,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | v7_struct_0(X4)
      | v1_xboole_0(sK16(X4))
      | v1_subset_1(sK16(X4),u1_struct_0(X4))
      | ~ v1_zfmisc_1(sK16(X4))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f5048,f246])).

fof(f8247,plain,
    ( ~ spl31_237
    | ~ spl31_719
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f7066,f1574,f836,f811,f4899,f1653])).

fof(f7066,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7065,f812])).

fof(f7065,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7064,f837])).

fof(f7064,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4875,f1575])).

fof(f4875,plain,(
    ! [X4] :
      ( ~ v1_subset_1(sK16(X4),u1_struct_0(X4))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ v7_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f4836,f247])).

fof(f247,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK16(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f139])).

fof(f4836,plain,(
    ! [X4] :
      ( ~ v7_struct_0(X4)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(sK16(X4))
      | ~ v1_subset_1(sK16(X4),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f4814])).

fof(f4814,plain,(
    ! [X4] :
      ( ~ v7_struct_0(X4)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | v1_xboole_0(sK16(X4))
      | ~ v1_subset_1(sK16(X4),u1_struct_0(X4))
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f258,f246])).

fof(f8246,plain,
    ( ~ spl31_721
    | spl31_718
    | spl31_89
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f8229,f2613,f650,f4896,f4902])).

fof(f4902,plain,
    ( spl31_721
  <=> ~ v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_721])])).

fof(f8229,plain,
    ( v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_89
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f6926,f651])).

fof(f6926,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f308,f2614])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f187,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc2_subset_1)).

fof(f8245,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8244,f1423,f876,f869])).

fof(f876,plain,
    ( spl31_119
  <=> ~ v1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_119])])).

fof(f8244,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f877,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl31_119 ),
    inference(avatar_component_clause,[],[f876])).

fof(f8243,plain,
    ( ~ spl31_813
    | spl31_89
    | spl31_669
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f8242,f4718,f4561,f650,f5699])).

fof(f5699,plain,
    ( spl31_813
  <=> ~ v1_xboole_0(sK22(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_813])])).

fof(f8242,plain,
    ( ~ v1_xboole_0(sK22(sK1))
    | ~ spl31_89
    | ~ spl31_669
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f8241,f4562])).

fof(f8241,plain,
    ( v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK22(sK1))
    | ~ spl31_89
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f6931,f651])).

fof(f6931,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f308,f4719])).

fof(f8240,plain,
    ( ~ spl31_123
    | spl31_1092
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8239,f1423,f734,f569,f8235,f896])).

fof(f8235,plain,
    ( spl31_1092
  <=> ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_zfmisc_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1092])])).

fof(f734,plain,
    ( spl31_103
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_103])])).

fof(f8239,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | v1_zfmisc_1(X1)
        | ~ v7_struct_0(sK1) )
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8238,f735])).

fof(f735,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl31_103 ),
    inference(avatar_component_clause,[],[f734])).

fof(f8238,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1)
        | ~ v7_struct_0(sK1) )
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7366,f570])).

fof(f7366,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1)
        | ~ v7_struct_0(sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f5016,f1424])).

fof(f8237,plain,
    ( ~ spl31_237
    | spl31_1092
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8233,f1574,f836,f811,f8235,f1653])).

fof(f8233,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_zfmisc_1(X2)
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8232,f812])).

fof(f8232,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_zfmisc_1(X2)
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7367,f837])).

fof(f7367,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_zfmisc_1(X2)
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f5016,f1575])).

fof(f8231,plain,
    ( ~ spl31_721
    | spl31_89
    | ~ spl31_402
    | spl31_719 ),
    inference(avatar_split_clause,[],[f8230,f4899,f2613,f650,f4902])).

fof(f8230,plain,
    ( ~ v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_89
    | ~ spl31_402
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f8229,f4900])).

fof(f4900,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_719 ),
    inference(avatar_component_clause,[],[f4899])).

fof(f8228,plain,
    ( ~ spl31_123
    | ~ spl31_715
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8227,f1423,f734,f569,f4883,f896])).

fof(f4883,plain,
    ( spl31_715
  <=> ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_715])])).

fof(f8227,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8226,f735])).

fof(f8226,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7063,f570])).

fof(f7063,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4875,f1424])).

fof(f8225,plain,
    ( ~ spl31_715
    | ~ spl31_117
    | ~ spl31_400
    | spl31_717 ),
    inference(avatar_split_clause,[],[f8224,f4886,f2604,f869,f4883])).

fof(f8224,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f7396,f4887])).

fof(f7396,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK16(sK1))
    | ~ spl31_400 ),
    inference(resolution,[],[f7379,f2605])).

fof(f8223,plain,
    ( ~ spl31_123
    | ~ spl31_707
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8222,f1423,f734,f569,f4850,f896])).

fof(f4850,plain,
    ( spl31_707
  <=> ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_707])])).

fof(f8222,plain,
    ( ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8221,f735])).

fof(f8221,plain,
    ( ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7030,f570])).

fof(f7030,plain,
    ( ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4842,f1424])).

fof(f4842,plain,(
    ! [X3] :
      ( ~ v1_subset_1(sK15(X3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | ~ v7_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f4837,f244])).

fof(f244,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK15(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f4837,plain,(
    ! [X3] :
      ( ~ v7_struct_0(X3)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | v1_xboole_0(sK15(X3))
      | ~ v1_subset_1(sK15(X3),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f4811])).

fof(f4811,plain,(
    ! [X3] :
      ( ~ v7_struct_0(X3)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | v1_xboole_0(sK15(X3))
      | ~ v1_subset_1(sK15(X3),u1_struct_0(X3))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f258,f243])).

fof(f8220,plain,
    ( ~ spl31_707
    | ~ spl31_117
    | ~ spl31_362
    | spl31_709 ),
    inference(avatar_split_clause,[],[f8219,f4853,f2343,f869,f4850])).

fof(f8219,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f7393,f4854])).

fof(f7393,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK15(sK1))
    | ~ spl31_362 ),
    inference(resolution,[],[f7379,f2344])).

fof(f8218,plain,
    ( ~ spl31_571
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_674
    | spl31_831 ),
    inference(avatar_split_clause,[],[f8217,f5874,f4585,f726,f562,f886,f3948])).

fof(f3948,plain,
    ( spl31_571
  <=> ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_571])])).

fof(f8217,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f8216,f5875])).

fof(f8216,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f8215,f727])).

fof(f8215,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f7583,f563])).

fof(f7583,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f258])).

fof(f8214,plain,
    ( ~ spl31_571
    | ~ spl31_117
    | ~ spl31_674
    | spl31_831 ),
    inference(avatar_split_clause,[],[f8213,f5874,f4585,f869,f3948])).

fof(f8213,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f7591,f5875])).

fof(f7591,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f7379])).

fof(f8212,plain,
    ( ~ spl31_557
    | ~ spl31_117
    | ~ spl31_666
    | spl31_775 ),
    inference(avatar_split_clause,[],[f8211,f5436,f4553,f869,f3876])).

fof(f3876,plain,
    ( spl31_557
  <=> ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_557])])).

fof(f4553,plain,
    ( spl31_666
  <=> m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_666])])).

fof(f5436,plain,
    ( spl31_775
  <=> ~ v1_xboole_0(sK20(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_775])])).

fof(f8211,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f7399,f5437])).

fof(f5437,plain,
    ( ~ v1_xboole_0(sK20(sK1))
    | ~ spl31_775 ),
    inference(avatar_component_clause,[],[f5436])).

fof(f7399,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK20(sK1))
    | ~ spl31_666 ),
    inference(resolution,[],[f7379,f4554])).

fof(f4554,plain,
    ( m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_666 ),
    inference(avatar_component_clause,[],[f4553])).

fof(f8210,plain,
    ( ~ spl31_367
    | ~ spl31_117
    | ~ spl31_4
    | spl31_87 ),
    inference(avatar_split_clause,[],[f8209,f641,f331,f869,f2365])).

fof(f2365,plain,
    ( spl31_367
  <=> ~ v1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_367])])).

fof(f641,plain,
    ( spl31_87
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_87])])).

fof(f8209,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_87 ),
    inference(subsumption_resolution,[],[f7389,f642])).

fof(f642,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl31_87 ),
    inference(avatar_component_clause,[],[f641])).

fof(f7389,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | ~ spl31_4 ),
    inference(resolution,[],[f7379,f332])).

fof(f8208,plain,
    ( ~ spl31_237
    | ~ spl31_711
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f7037,f1574,f836,f811,f4866,f1653])).

fof(f4866,plain,
    ( spl31_711
  <=> ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_711])])).

fof(f7037,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7036,f812])).

fof(f7036,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7031,f837])).

fof(f7031,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4842,f1575])).

fof(f8207,plain,
    ( ~ spl31_237
    | ~ spl31_869
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8206,f1574,f836,f650,f6248,f1653])).

fof(f6248,plain,
    ( spl31_869
  <=> ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_869])])).

fof(f8206,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8205,f651])).

fof(f8205,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7471,f1575])).

fof(f7471,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7450,f837])).

fof(f7450,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f4911,f1575])).

fof(f4911,plain,(
    ! [X10] :
      ( ~ v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | ~ l1_struct_0(X10)
      | ~ v7_struct_0(X10)
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f4910,f284])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK25(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f4910,plain,(
    ! [X10] :
      ( ~ v7_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v1_xboole_0(sK25(u1_struct_0(X10)))
      | ~ v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f4822,f242])).

fof(f4822,plain,(
    ! [X10] :
      ( ~ v7_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(sK25(u1_struct_0(X10)))
      | ~ v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(resolution,[],[f258,f283])).

fof(f8204,plain,
    ( ~ spl31_237
    | ~ spl31_875
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f8203,f1574,f836,f650,f6268,f1653])).

fof(f6268,plain,
    ( spl31_875
  <=> ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_875])])).

fof(f8203,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f8202,f651])).

fof(f8202,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7507,f1575])).

fof(f7507,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7486,f837])).

fof(f7486,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f4913,f1575])).

fof(f4913,plain,(
    ! [X11] :
      ( ~ v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | ~ l1_struct_0(X11)
      | ~ v7_struct_0(X11)
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f4912,f287])).

fof(f287,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK26(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f4912,plain,(
    ! [X11] :
      ( ~ v7_struct_0(X11)
      | ~ l1_struct_0(X11)
      | v1_xboole_0(sK26(u1_struct_0(X11)))
      | ~ v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f4823,f242])).

fof(f4823,plain,(
    ! [X11] :
      ( ~ v7_struct_0(X11)
      | ~ l1_struct_0(X11)
      | v2_struct_0(X11)
      | v1_xboole_0(sK26(u1_struct_0(X11)))
      | ~ v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(resolution,[],[f258,f286])).

fof(f8201,plain,
    ( spl31_236
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_730
    | spl31_1007 ),
    inference(avatar_split_clause,[],[f8200,f7438,f5139,f1574,f836,f1650])).

fof(f8200,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_730
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f8199,f5140])).

fof(f8199,plain,
    ( ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_1007 ),
    inference(forward_demodulation,[],[f8198,f1575])).

fof(f8198,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f8197,f837])).

fof(f8197,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_220
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f7759,f7439])).

fof(f7439,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_1007 ),
    inference(avatar_component_clause,[],[f7438])).

fof(f8196,plain,
    ( spl31_236
    | spl31_710
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_564
    | spl31_713 ),
    inference(avatar_split_clause,[],[f8195,f4869,f3908,f1574,f836,f4863,f1650])).

fof(f8195,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_564
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8194,f3909])).

fof(f8194,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8193,f837])).

fof(f8193,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f7863,f4870])).

fof(f7863,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f5083,f1575])).

fof(f5083,plain,(
    ! [X3] :
      ( v1_subset_1(sK15(X3),u1_struct_0(X3))
      | v7_struct_0(X3)
      | v1_xboole_0(sK15(X3))
      | ~ l1_struct_0(X3)
      | ~ v1_zfmisc_1(sK15(X3)) ) ),
    inference(subsumption_resolution,[],[f5081,f274])).

fof(f5081,plain,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | v7_struct_0(X3)
      | v1_xboole_0(sK15(X3))
      | v1_subset_1(sK15(X3),u1_struct_0(X3))
      | ~ v1_zfmisc_1(sK15(X3))
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f5055])).

fof(f5055,plain,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | v7_struct_0(X3)
      | v1_xboole_0(sK15(X3))
      | v1_subset_1(sK15(X3),u1_struct_0(X3))
      | ~ v1_zfmisc_1(sK15(X3))
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f5048,f243])).

fof(f8192,plain,
    ( spl31_720
    | spl31_236
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_562
    | spl31_719 ),
    inference(avatar_split_clause,[],[f8191,f4899,f3900,f1574,f836,f1650,f4905])).

fof(f8191,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_562
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f8190,f3901])).

fof(f8190,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f8189,f837])).

fof(f8189,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f7868,f4900])).

fof(f8188,plain,
    ( spl31_122
    | ~ spl31_70
    | ~ spl31_810 ),
    inference(avatar_split_clause,[],[f8187,f5693,f569,f893])).

fof(f8187,plain,
    ( v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_810 ),
    inference(subsumption_resolution,[],[f6556,f570])).

fof(f6556,plain,
    ( ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_810 ),
    inference(resolution,[],[f5694,f1054])).

fof(f5694,plain,
    ( v1_zfmisc_1(sK22(sK1))
    | ~ spl31_810 ),
    inference(avatar_component_clause,[],[f5693])).

fof(f8186,plain,
    ( spl31_122
    | spl31_868
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8185,f1423,f569,f6251,f893])).

fof(f8185,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f6900,f570])).

fof(f6900,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f5089,f1424])).

fof(f5089,plain,(
    ! [X10] :
      ( v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | v7_struct_0(X10)
      | ~ l1_struct_0(X10) ) ),
    inference(subsumption_resolution,[],[f5088,f4057])).

fof(f5088,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | v7_struct_0(X10)
      | v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f5087,f285])).

fof(f285,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK25(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f167])).

fof(f5087,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | v7_struct_0(X10)
      | v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | ~ v1_zfmisc_1(sK25(u1_struct_0(X10)))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(subsumption_resolution,[],[f5066,f284])).

fof(f5066,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | v7_struct_0(X10)
      | v1_xboole_0(sK25(u1_struct_0(X10)))
      | v1_subset_1(sK25(u1_struct_0(X10)),u1_struct_0(X10))
      | ~ v1_zfmisc_1(sK25(u1_struct_0(X10)))
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(resolution,[],[f5048,f283])).

fof(f8184,plain,
    ( spl31_122
    | spl31_874
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8183,f1423,f569,f6271,f893])).

fof(f8183,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f6905,f570])).

fof(f6905,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f5092,f1424])).

fof(f5092,plain,(
    ! [X11] :
      ( v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | v7_struct_0(X11)
      | ~ l1_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f5091,f4057])).

fof(f5091,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | v7_struct_0(X11)
      | v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f5090,f288])).

fof(f288,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK26(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f5090,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | v7_struct_0(X11)
      | v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | ~ v1_zfmisc_1(sK26(u1_struct_0(X11)))
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(subsumption_resolution,[],[f5067,f287])).

fof(f5067,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | v7_struct_0(X11)
      | v1_xboole_0(sK26(u1_struct_0(X11)))
      | v1_subset_1(sK26(u1_struct_0(X11)),u1_struct_0(X11))
      | ~ v1_zfmisc_1(sK26(u1_struct_0(X11)))
      | v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(resolution,[],[f5048,f286])).

fof(f8182,plain,
    ( ~ spl31_123
    | ~ spl31_869
    | ~ spl31_70
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8181,f1423,f650,f569,f6248,f896])).

fof(f8181,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8180,f651])).

fof(f8180,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7476,f1424])).

fof(f7476,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7449,f570])).

fof(f7449,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_194 ),
    inference(superposition,[],[f4911,f1424])).

fof(f8179,plain,
    ( ~ spl31_123
    | ~ spl31_875
    | ~ spl31_70
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f8178,f1423,f650,f569,f6268,f896])).

fof(f8178,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f8177,f651])).

fof(f8177,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7512,f1424])).

fof(f7512,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7485,f570])).

fof(f7485,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_194 ),
    inference(superposition,[],[f4913,f1424])).

fof(f8176,plain,
    ( spl31_122
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_730
    | spl31_1007 ),
    inference(avatar_split_clause,[],[f8175,f7438,f5139,f1423,f569,f893])).

fof(f8175,plain,
    ( v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_730
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f8174,f5140])).

fof(f8174,plain,
    ( ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_1007 ),
    inference(forward_demodulation,[],[f8173,f1424])).

fof(f8173,plain,
    ( v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK1)))
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f8172,f570])).

fof(f8172,plain,
    ( v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK1)))
    | ~ spl31_194
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f7758,f7439])).

fof(f8171,plain,
    ( spl31_122
    | spl31_706
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_428
    | spl31_709 ),
    inference(avatar_split_clause,[],[f8170,f4853,f2734,f1423,f569,f4847,f893])).

fof(f8170,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_428
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f8169,f2735])).

fof(f8169,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f8168,f570])).

fof(f8168,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_194
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f7862,f4854])).

fof(f7862,plain,
    ( v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK15(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_194 ),
    inference(superposition,[],[f5083,f1424])).

fof(f8167,plain,
    ( spl31_122
    | spl31_714
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_566
    | spl31_717 ),
    inference(avatar_split_clause,[],[f8166,f4886,f3916,f1423,f569,f4880,f893])).

fof(f8166,plain,
    ( v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_566
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f8165,f3917])).

fof(f8165,plain,
    ( v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f8164,f570])).

fof(f8164,plain,
    ( v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_194
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f7867,f4887])).

fof(f7867,plain,
    ( v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | v1_xboole_0(sK16(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_194 ),
    inference(superposition,[],[f5084,f1424])).

fof(f8163,plain,
    ( ~ spl31_557
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_666
    | spl31_775 ),
    inference(avatar_split_clause,[],[f8162,f5436,f4553,f726,f562,f886,f3876])).

fof(f8162,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f8161,f5437])).

fof(f8161,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f8160,f727])).

fof(f8160,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6609,f563])).

fof(f6609,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f258])).

fof(f8159,plain,
    ( spl31_556
    | spl31_120
    | ~ spl31_68
    | ~ spl31_666
    | spl31_775
    | ~ spl31_884 ),
    inference(avatar_split_clause,[],[f8158,f6314,f5436,f4553,f562,f883,f3879])).

fof(f3879,plain,
    ( spl31_556
  <=> v1_subset_1(sK20(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_556])])).

fof(f6314,plain,
    ( spl31_884
  <=> v1_zfmisc_1(sK20(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_884])])).

fof(f8158,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_666
    | ~ spl31_775
    | ~ spl31_884 ),
    inference(subsumption_resolution,[],[f8157,f6315])).

fof(f6315,plain,
    ( v1_zfmisc_1(sK20(sK1))
    | ~ spl31_884 ),
    inference(avatar_component_clause,[],[f6314])).

fof(f8157,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_68
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f8156,f5437])).

fof(f8156,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_68
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6616,f563])).

fof(f6616,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f5048])).

fof(f8155,plain,
    ( spl31_812
    | spl31_120
    | ~ spl31_68
    | spl31_669
    | ~ spl31_702
    | ~ spl31_810 ),
    inference(avatar_split_clause,[],[f8154,f5693,f4718,f4561,f562,f883,f5702])).

fof(f8154,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_669
    | ~ spl31_702
    | ~ spl31_810 ),
    inference(subsumption_resolution,[],[f8153,f5694])).

fof(f8151,plain,
    ( ~ spl31_121
    | spl31_560
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7374,f1423,f726,f562,f324,f3892,f886])).

fof(f3892,plain,
    ( spl31_560
  <=> ! [X5] :
        ( ~ v2_tex_2(X5,sK1)
        | v1_zfmisc_1(sK4(sK1,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tex_2(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_560])])).

fof(f7374,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ v7_struct_0(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7373,f727])).

fof(f7373,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X0))
        | ~ v7_struct_0(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7343,f563])).

fof(f7343,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X0))
        | ~ v7_struct_0(sK0)
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f5016,f3321])).

fof(f8150,plain,
    ( spl31_570
    | spl31_120
    | ~ spl31_68
    | ~ spl31_674
    | spl31_831
    | ~ spl31_882 ),
    inference(avatar_split_clause,[],[f8149,f6301,f5874,f4585,f562,f883,f3951])).

fof(f8149,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_674
    | ~ spl31_831
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8148,f6302])).

fof(f8148,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f8147,f5875])).

fof(f8147,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f7590,f563])).

fof(f7590,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f5048])).

fof(f8146,plain,
    ( spl31_120
    | ~ spl31_68
    | ~ spl31_730
    | spl31_1007 ),
    inference(avatar_split_clause,[],[f8145,f7438,f5139,f562,f883])).

fof(f8145,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_730
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f8144,f5140])).

fof(f8144,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | ~ spl31_68
    | ~ spl31_1007 ),
    inference(subsumption_resolution,[],[f7756,f563])).

fof(f7756,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | ~ spl31_1007 ),
    inference(resolution,[],[f5086,f7439])).

fof(f8143,plain,
    ( spl31_120
    | ~ spl31_68
    | ~ spl31_728
    | spl31_1053
    | spl31_1055 ),
    inference(avatar_split_clause,[],[f8142,f7906,f7903,f5131,f562,f883])).

fof(f7903,plain,
    ( spl31_1053
  <=> ~ v1_subset_1(sK16(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1053])])).

fof(f8142,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_728
    | ~ spl31_1053
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f8141,f5132])).

fof(f8141,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK16(sK0))
    | ~ spl31_68
    | ~ spl31_1053
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f8140,f563])).

fof(f8140,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(sK16(sK0))
    | ~ spl31_1053
    | ~ spl31_1055 ),
    inference(subsumption_resolution,[],[f7959,f7907])).

fof(f7959,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK16(sK0))
    | ~ l1_struct_0(sK0)
    | ~ v1_zfmisc_1(sK16(sK0))
    | ~ spl31_1053 ),
    inference(resolution,[],[f7904,f5084])).

fof(f7904,plain,
    ( ~ v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ spl31_1053 ),
    inference(avatar_component_clause,[],[f7903])).

fof(f8139,plain,
    ( spl31_740
    | ~ spl31_117
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7391,f1423,f324,f869,f5202])).

fof(f5202,plain,
    ( spl31_740
  <=> ! [X2] :
        ( v1_xboole_0(sK4(sK1,X2))
        | v3_tex_2(X2,sK1)
        | ~ v2_tex_2(X2,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_740])])).

fof(f7391,plain,
    ( ! [X12] :
        ( ~ v1_zfmisc_1(u1_struct_0(sK0))
        | ~ v1_subset_1(sK4(sK1,X12),u1_struct_0(sK0))
        | v1_xboole_0(sK4(sK1,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X12,sK1)
        | v3_tex_2(X12,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f7379,f1975])).

fof(f8138,plain,
    ( ~ spl31_711
    | ~ spl31_117
    | ~ spl31_364
    | spl31_713 ),
    inference(avatar_split_clause,[],[f8137,f4869,f2352,f869,f4866])).

fof(f8137,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f7394,f4870])).

fof(f7394,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364 ),
    inference(resolution,[],[f7379,f2353])).

fof(f8136,plain,
    ( spl31_366
    | spl31_116
    | ~ spl31_4
    | spl31_87
    | ~ spl31_114 ),
    inference(avatar_split_clause,[],[f8135,f863,f641,f331,f866,f2362])).

fof(f2362,plain,
    ( spl31_366
  <=> v1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_366])])).

fof(f863,plain,
    ( spl31_114
  <=> v1_zfmisc_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_114])])).

fof(f8135,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_87
    | ~ spl31_114 ),
    inference(subsumption_resolution,[],[f8134,f864])).

fof(f864,plain,
    ( v1_zfmisc_1(sK3)
    | ~ spl31_114 ),
    inference(avatar_component_clause,[],[f863])).

fof(f8134,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4
    | ~ spl31_87 ),
    inference(subsumption_resolution,[],[f7771,f642])).

fof(f7771,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4 ),
    inference(resolution,[],[f7761,f332])).

fof(f8133,plain,
    ( spl31_738
    | spl31_116
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7773,f1423,f324,f866,f5182])).

fof(f7773,plain,
    ( ! [X12] :
        ( v1_zfmisc_1(u1_struct_0(sK0))
        | v1_xboole_0(sK4(sK1,X12))
        | v1_subset_1(sK4(sK1,X12),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X12,sK1)
        | v3_tex_2(X12,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f7761,f1975])).

fof(f8132,plain,
    ( spl31_706
    | spl31_116
    | ~ spl31_362
    | ~ spl31_428
    | spl31_709 ),
    inference(avatar_split_clause,[],[f8131,f4853,f2734,f2343,f866,f4847])).

fof(f8131,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362
    | ~ spl31_428
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f8130,f2735])).

fof(f8130,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_362
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f7775,f4854])).

fof(f7775,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK15(sK1))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_362 ),
    inference(resolution,[],[f7761,f2344])).

fof(f8129,plain,
    ( spl31_710
    | spl31_116
    | ~ spl31_364
    | ~ spl31_564
    | spl31_713 ),
    inference(avatar_split_clause,[],[f8128,f4869,f3908,f2352,f866,f4863])).

fof(f8128,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364
    | ~ spl31_564
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f8127,f3909])).

fof(f8127,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f7776,f4870])).

fof(f7776,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364 ),
    inference(resolution,[],[f7761,f2353])).

fof(f8126,plain,
    ( spl31_714
    | spl31_116
    | ~ spl31_400
    | ~ spl31_566
    | spl31_717 ),
    inference(avatar_split_clause,[],[f8125,f4886,f3916,f2604,f866,f4880])).

fof(f8125,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400
    | ~ spl31_566
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f8124,f3917])).

fof(f8124,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_400
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f7778,f4887])).

fof(f7778,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_400 ),
    inference(resolution,[],[f7761,f2605])).

fof(f8123,plain,
    ( spl31_720
    | spl31_116
    | ~ spl31_402
    | ~ spl31_562
    | spl31_719 ),
    inference(avatar_split_clause,[],[f8122,f4899,f3900,f2613,f866,f4905])).

fof(f8122,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402
    | ~ spl31_562
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f8121,f3901])).

fof(f8121,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402
    | ~ spl31_719 ),
    inference(subsumption_resolution,[],[f7779,f4900])).

fof(f8120,plain,
    ( spl31_556
    | spl31_116
    | ~ spl31_666
    | spl31_775
    | ~ spl31_884 ),
    inference(avatar_split_clause,[],[f8119,f6314,f5436,f4553,f866,f3879])).

fof(f8119,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_666
    | ~ spl31_775
    | ~ spl31_884 ),
    inference(subsumption_resolution,[],[f8118,f6315])).

fof(f8118,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f7781,f5437])).

fof(f7781,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK20(sK1))
    | v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_666 ),
    inference(resolution,[],[f7761,f4554])).

fof(f8117,plain,
    ( spl31_570
    | spl31_116
    | ~ spl31_674
    | spl31_831
    | ~ spl31_882 ),
    inference(avatar_split_clause,[],[f8116,f6301,f5874,f4585,f866,f3951])).

fof(f8116,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674
    | ~ spl31_831
    | ~ spl31_882 ),
    inference(subsumption_resolution,[],[f8115,f6302])).

fof(f8115,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f7783,f5875])).

fof(f7783,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674 ),
    inference(resolution,[],[f7761,f4586])).

fof(f8114,plain,
    ( spl31_812
    | spl31_116
    | spl31_669
    | ~ spl31_702
    | ~ spl31_810 ),
    inference(avatar_split_clause,[],[f8113,f5693,f4718,f4561,f866,f5702])).

fof(f8113,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(sK22(sK1))
    | ~ spl31_669
    | ~ spl31_702
    | ~ spl31_810 ),
    inference(subsumption_resolution,[],[f8112,f5694])).

fof(f8111,plain,
    ( spl31_1090
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8026,f7923,f373,f8109])).

fof(f8109,plain,
    ( spl31_1090
  <=> sK9 = sK27(sK27(sK27(sK27(sK30(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1090])])).

fof(f7923,plain,
    ( spl31_1058
  <=> v1_xboole_0(sK30(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1058])])).

fof(f8026,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK30(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f1046])).

fof(f7924,plain,
    ( v1_xboole_0(sK30(u1_struct_0(sK0)))
    | ~ spl31_1058 ),
    inference(avatar_component_clause,[],[f7923])).

fof(f8104,plain,
    ( spl31_1088
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8025,f7923,f373,f8102])).

fof(f8102,plain,
    ( spl31_1088
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK30(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1088])])).

fof(f8025,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK30(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f1041])).

fof(f8097,plain,
    ( spl31_1086
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8024,f7923,f373,f8095])).

fof(f8095,plain,
    ( spl31_1086
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK30(u1_struct_0(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1086])])).

fof(f8024,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK30(u1_struct_0(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f1036])).

fof(f8090,plain,
    ( spl31_1084
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8022,f7923,f373,f8088])).

fof(f8088,plain,
    ( spl31_1084
  <=> sK9 = sK27(sK27(sK27(sK30(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1084])])).

fof(f8022,plain,
    ( sK9 = sK27(sK27(sK27(sK30(u1_struct_0(sK0)))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f819])).

fof(f8083,plain,
    ( spl31_1082
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8021,f7923,f373,f8081])).

fof(f8081,plain,
    ( spl31_1082
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1082])])).

fof(f8021,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0))))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f817])).

fof(f8076,plain,
    ( spl31_1080
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8020,f7923,f373,f8074])).

fof(f8074,plain,
    ( spl31_1080
  <=> sK5(k1_zfmisc_1(sK27(sK30(u1_struct_0(sK0))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1080])])).

fof(f8020,plain,
    ( sK5(k1_zfmisc_1(sK27(sK30(u1_struct_0(sK0))))) = sK9
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f792])).

fof(f8069,plain,
    ( spl31_1078
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8019,f7923,f373,f8067])).

fof(f8067,plain,
    ( spl31_1078
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1078])])).

fof(f8019,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f790])).

fof(f8062,plain,
    ( spl31_1076
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8018,f7923,f373,f8060])).

fof(f8060,plain,
    ( spl31_1076
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1076])])).

fof(f8018,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f668])).

fof(f8055,plain,
    ( spl31_1074
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8017,f7923,f373,f8053])).

fof(f8053,plain,
    ( spl31_1074
  <=> sK9 = sK27(sK27(sK30(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1074])])).

fof(f8017,plain,
    ( sK9 = sK27(sK27(sK30(u1_struct_0(sK0))))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f667])).

fof(f8048,plain,
    ( spl31_1072
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8015,f7923,f373,f8046])).

fof(f8046,plain,
    ( spl31_1072
  <=> sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1072])])).

fof(f8015,plain,
    ( sK5(k1_zfmisc_1(sK30(u1_struct_0(sK0)))) = sK9
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f663])).

fof(f8041,plain,
    ( spl31_1070
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8013,f7923,f373,f8039])).

fof(f8039,plain,
    ( spl31_1070
  <=> sK9 = sK27(sK30(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1070])])).

fof(f8013,plain,
    ( sK9 = sK27(sK30(u1_struct_0(sK0)))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f660])).

fof(f8034,plain,
    ( spl31_1068
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(avatar_split_clause,[],[f8012,f7923,f373,f8032])).

fof(f8032,plain,
    ( spl31_1068
  <=> sK9 = sK30(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1068])])).

fof(f8012,plain,
    ( sK9 = sK30(u1_struct_0(sK0))
    | ~ spl31_16
    | ~ spl31_1058 ),
    inference(resolution,[],[f7924,f625])).

fof(f8008,plain,
    ( spl31_89
    | spl31_1057 ),
    inference(avatar_contradiction_clause,[],[f8007])).

fof(f8007,plain,
    ( $false
    | ~ spl31_89
    | ~ spl31_1057 ),
    inference(subsumption_resolution,[],[f8006,f651])).

fof(f8006,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_1057 ),
    inference(resolution,[],[f7918,f307])).

fof(f307,plain,(
    ! [X0] :
      ( v1_subset_1(sK30(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f98])).

fof(f98,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc4_subset_1)).

fof(f7918,plain,
    ( ~ v1_subset_1(sK30(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_1057 ),
    inference(avatar_component_clause,[],[f7917])).

fof(f7917,plain,
    ( spl31_1057
  <=> ~ v1_subset_1(sK30(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1057])])).

fof(f8004,plain,
    ( ~ spl31_1065
    | spl31_1066
    | ~ spl31_16
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f7994,f1574,f828,f373,f8002,f7999])).

fof(f7999,plain,
    ( spl31_1065
  <=> ~ v3_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1065])])).

fof(f8002,plain,
    ( spl31_1066
  <=> ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | sK9 = X2
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1066])])).

fof(f7994,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | sK9 = X2
        | ~ v3_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_16
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7986,f829])).

fof(f7986,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v2_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | sK9 = X2
        | ~ v3_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_16
    | ~ spl31_220 ),
    inference(superposition,[],[f5807,f1575])).

fof(f5807,plain,
    ( ! [X26,X25] :
        ( ~ r1_tarski(X26,u1_struct_0(X25))
        | ~ v2_tex_2(X26,X25)
        | sK9 = X26
        | ~ v3_tex_2(sK9,X25)
        | ~ l1_pre_topc(X25) )
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f5786,f690])).

fof(f690,plain,
    ( ! [X1] : r1_tarski(sK9,X1)
    | ~ spl31_16 ),
    inference(resolution,[],[f225,f629])).

fof(f5786,plain,
    ( ! [X26,X25] :
        ( ~ l1_pre_topc(X25)
        | ~ v2_tex_2(X26,X25)
        | ~ r1_tarski(sK9,X26)
        | sK9 = X26
        | ~ v3_tex_2(sK9,X25)
        | ~ r1_tarski(X26,u1_struct_0(X25)) )
    | ~ spl31_16 ),
    inference(resolution,[],[f2072,f629])).

fof(f7938,plain,
    ( ~ spl31_1061
    | spl31_1062
    | ~ spl31_722 ),
    inference(avatar_split_clause,[],[f7894,f4924,f7936,f7930])).

fof(f7930,plain,
    ( spl31_1061
  <=> ~ v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1061])])).

fof(f7936,plain,
    ( spl31_1062
  <=> v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1062])])).

fof(f4924,plain,
    ( spl31_722
  <=> ! [X2] :
        ( ~ v1_subset_1(X2,u1_struct_0(sK0))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_722])])).

fof(f7894,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_subset_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl31_722 ),
    inference(resolution,[],[f4925,f215])).

fof(f4925,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl31_722 ),
    inference(avatar_component_clause,[],[f4924])).

fof(f7925,plain,
    ( ~ spl31_1057
    | spl31_1058
    | spl31_89
    | ~ spl31_722 ),
    inference(avatar_split_clause,[],[f7912,f4924,f650,f7923,f7917])).

fof(f7912,plain,
    ( v1_xboole_0(sK30(u1_struct_0(sK0)))
    | ~ v1_subset_1(sK30(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_722 ),
    inference(subsumption_resolution,[],[f7892,f651])).

fof(f7892,plain,
    ( v1_xboole_0(sK30(u1_struct_0(sK0)))
    | ~ v1_subset_1(sK30(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_722 ),
    inference(resolution,[],[f4925,f306])).

fof(f306,plain,(
    ! [X0] :
      ( m1_subset_1(sK30(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f7911,plain,
    ( ~ spl31_1053
    | spl31_1054
    | ~ spl31_68
    | spl31_101
    | ~ spl31_722 ),
    inference(avatar_split_clause,[],[f7898,f4924,f726,f562,f7909,f7903])).

fof(f7909,plain,
    ( spl31_1054
  <=> v1_xboole_0(sK16(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1054])])).

fof(f7898,plain,
    ( v1_xboole_0(sK16(sK0))
    | ~ v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_722 ),
    inference(subsumption_resolution,[],[f7897,f727])).

fof(f7897,plain,
    ( v1_xboole_0(sK16(sK0))
    | ~ v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_722 ),
    inference(subsumption_resolution,[],[f7878,f563])).

fof(f7878,plain,
    ( v1_xboole_0(sK16(sK0))
    | ~ v1_subset_1(sK16(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_722 ),
    inference(resolution,[],[f4925,f246])).

fof(f7895,plain,
    ( spl31_740
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_722 ),
    inference(avatar_split_clause,[],[f7871,f4924,f1423,f324,f5202])).

fof(f7871,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK1,X0))
        | ~ v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_722 ),
    inference(resolution,[],[f4925,f1975])).

fof(f7857,plain,
    ( ~ spl31_1049
    | spl31_1050
    | spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f7844,f1574,f828,f650,f7855,f7849])).

fof(f7849,plain,
    ( spl31_1049
  <=> ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1049])])).

fof(f7855,plain,
    ( spl31_1050
  <=> v2_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1050])])).

fof(f7844,plain,
    ( v2_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7843,f651])).

fof(f7843,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7842,f1575])).

fof(f7842,plain,
    ( v2_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7841,f1575])).

fof(f7841,plain,
    ( ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK26(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7837,f829])).

fof(f7837,plain,
    ( ~ v3_tex_2(sK26(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK26(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f1211,f1575])).

fof(f1211,plain,(
    ! [X3] :
      ( ~ v3_tex_2(sK26(u1_struct_0(X3)),X3)
      | v2_tex_2(sK26(u1_struct_0(X3)),X3)
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(resolution,[],[f203,f286])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f7833,plain,
    ( ~ spl31_1045
    | spl31_1046
    | spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f7820,f1574,f828,f650,f7831,f7825])).

fof(f7825,plain,
    ( spl31_1045
  <=> ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1045])])).

fof(f7831,plain,
    ( spl31_1046
  <=> v2_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1046])])).

fof(f7820,plain,
    ( v2_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7819,f651])).

fof(f7819,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7818,f1575])).

fof(f7818,plain,
    ( v2_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f7817,f1575])).

fof(f7817,plain,
    ( ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK25(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f7813,f829])).

fof(f7813,plain,
    ( ~ v3_tex_2(sK25(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK25(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f1210,f1575])).

fof(f1210,plain,(
    ! [X2] :
      ( ~ v3_tex_2(sK25(u1_struct_0(X2)),X2)
      | v2_tex_2(sK25(u1_struct_0(X2)),X2)
      | ~ l1_pre_topc(X2)
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(resolution,[],[f203,f283])).

fof(f7754,plain,
    ( ~ spl31_704
    | spl31_889 ),
    inference(avatar_contradiction_clause,[],[f7753])).

fof(f7753,plain,
    ( $false
    | ~ spl31_704
    | ~ spl31_889 ),
    inference(subsumption_resolution,[],[f7628,f6540])).

fof(f6540,plain,
    ( ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_889 ),
    inference(avatar_component_clause,[],[f6539])).

fof(f6539,plain,
    ( spl31_889
  <=> ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_889])])).

fof(f7628,plain,
    ( r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f225])).

fof(f4727,plain,
    ( m1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_704 ),
    inference(avatar_component_clause,[],[f4726])).

fof(f4726,plain,
    ( spl31_704
  <=> m1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_704])])).

fof(f7752,plain,
    ( spl31_1030
    | ~ spl31_116
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7751,f4726,f866,f7703])).

fof(f7751,plain,
    ( v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_116
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7627,f867])).

fof(f867,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_116 ),
    inference(avatar_component_clause,[],[f866])).

fof(f7627,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f282])).

fof(f7750,plain,
    ( ~ spl31_1043
    | spl31_89
    | spl31_679
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7743,f4726,f4601,f650,f7748])).

fof(f7748,plain,
    ( spl31_1043
  <=> ~ v1_xboole_0(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1043])])).

fof(f4601,plain,
    ( spl31_679
  <=> ~ v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_679])])).

fof(f7743,plain,
    ( ~ v1_xboole_0(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_89
    | ~ spl31_679
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7742,f4602])).

fof(f4602,plain,
    ( ~ v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_679 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f7742,plain,
    ( v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_89
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7625,f651])).

fof(f7625,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f308])).

fof(f7741,plain,
    ( spl31_1030
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7740,f4726,f883,f726,f562,f7703])).

fof(f7740,plain,
    ( v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7739,f727])).

fof(f7739,plain,
    ( v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7738,f563])).

fof(f7738,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_120
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7622,f884])).

fof(f884,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_120 ),
    inference(avatar_component_clause,[],[f883])).

fof(f7622,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f4985])).

fof(f7737,plain,
    ( ~ spl31_1017
    | spl31_1040
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7733,f4726,f317,f7735,f7661])).

fof(f7661,plain,
    ( spl31_1017
  <=> ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1017])])).

fof(f7735,plain,
    ( spl31_1040
  <=> ! [X4] :
        ( ~ v2_tex_2(X4,sK0)
        | ~ r1_tarski(X4,u1_struct_0(sK0))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1040])])).

fof(f7733,plain,
    ( ! [X4] :
        ( ~ v2_tex_2(X4,sK0)
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4
        | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X4,u1_struct_0(sK0)) )
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7619,f318])).

fof(f7619,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(X4,sK0)
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X4)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X4
        | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X4,u1_struct_0(sK0)) )
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f2072])).

fof(f7732,plain,
    ( ~ spl31_1017
    | spl31_1026
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7731,f4726,f317,f7688,f7661])).

fof(f7688,plain,
    ( spl31_1026
  <=> v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1026])])).

fof(f7731,plain,
    ( v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7615,f318])).

fof(f7615,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f203])).

fof(f7730,plain,
    ( ~ spl31_1027
    | spl31_1038
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7726,f4726,f317,f7728,f7685])).

fof(f7685,plain,
    ( spl31_1027
  <=> ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1027])])).

fof(f7728,plain,
    ( spl31_1038
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X3,sK0)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3
        | ~ r1_tarski(X3,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1038])])).

fof(f7726,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X3,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3
        | ~ v3_tex_2(X3,sK0) )
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7614,f318])).

fof(f7614,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X3,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3
        | ~ v3_tex_2(X3,sK0) )
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f202])).

fof(f7725,plain,
    ( spl31_1016
    | spl31_1036
    | ~ spl31_1027
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7718,f4726,f317,f7685,f7723,f7658])).

fof(f7658,plain,
    ( spl31_1016
  <=> v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1016])])).

fof(f7723,plain,
    ( spl31_1036
  <=> r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1036])])).

fof(f7718,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7613,f318])).

fof(f7613,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f200])).

fof(f7717,plain,
    ( spl31_1016
    | spl31_1034
    | ~ spl31_1027
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7710,f4726,f317,f7685,f7715,f7658])).

fof(f7715,plain,
    ( spl31_1034
  <=> v2_tex_2(sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1034])])).

fof(f7710,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_704 ),
    inference(subsumption_resolution,[],[f7612,f318])).

fof(f7612,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f199])).

fof(f7709,plain,
    ( ~ spl31_1009
    | spl31_1032
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7611,f4726,f1423,f324,f7707,f7634])).

fof(f7634,plain,
    ( spl31_1009
  <=> ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1009])])).

fof(f7707,plain,
    ( spl31_1032
  <=> ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2)
        | ~ v2_tex_2(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1032])])).

fof(f7611,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v2_tex_2(X2,sK1)
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X2)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f5811])).

fof(f5811,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,u1_struct_0(sK0))
        | ~ v2_tex_2(X3,sK1)
        | ~ r1_tarski(X2,X3)
        | X2 = X3
        | ~ v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f5810,f1424])).

fof(f5810,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X3,sK1)
        | ~ r1_tarski(X2,X3)
        | X2 = X3
        | ~ v3_tex_2(X2,sK1)
        | ~ r1_tarski(X3,u1_struct_0(sK1)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5796,f325])).

fof(f5796,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_tex_2(X3,sK1)
        | ~ r1_tarski(X2,X3)
        | X2 = X3
        | ~ v3_tex_2(X2,sK1)
        | ~ r1_tarski(X3,u1_struct_0(sK1)) )
    | ~ spl31_194 ),
    inference(superposition,[],[f2072,f1424])).

fof(f7705,plain,
    ( spl31_1030
    | ~ spl31_704
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f7610,f5039,f4726,f7703])).

fof(f5039,plain,
    ( spl31_726
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_726])])).

fof(f7610,plain,
    ( v1_zfmisc_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_704
    | ~ spl31_726 ),
    inference(resolution,[],[f4727,f5040])).

fof(f5040,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X2) )
    | ~ spl31_726 ),
    inference(avatar_component_clause,[],[f5039])).

fof(f7698,plain,
    ( spl31_1010
    | ~ spl31_1027
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7609,f4726,f1906,f1423,f324,f317,f7685,f7640])).

fof(f7640,plain,
    ( spl31_1010
  <=> v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1010])])).

fof(f7609,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f4164])).

fof(f4164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X0,sK1) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4151,f318])).

fof(f4151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(duplicate_literal_removal,[],[f4150])).

fof(f4150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(equality_resolution,[],[f3640])).

fof(f7697,plain,
    ( spl31_1008
    | ~ spl31_1011
    | spl31_1028
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7608,f4726,f1906,f1423,f324,f317,f7695,f7637,f7631])).

fof(f7631,plain,
    ( spl31_1008
  <=> v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1008])])).

fof(f7637,plain,
    ( spl31_1011
  <=> ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1011])])).

fof(f7695,plain,
    ( spl31_1028
  <=> v2_tex_2(sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1028])])).

fof(f7608,plain,
    ( v2_tex_2(sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f3834])).

fof(f7690,plain,
    ( spl31_1026
    | ~ spl31_1011
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7607,f4726,f1906,f1423,f324,f317,f7637,f7688])).

fof(f7607,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f3813])).

fof(f7683,plain,
    ( spl31_1024
    | ~ spl31_1011
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7606,f4726,f1423,f324,f7637,f7681])).

fof(f7681,plain,
    ( spl31_1024
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v3_tex_2(X1,sK1)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1024])])).

fof(f7606,plain,
    ( ! [X1] :
        ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
        | ~ r1_tarski(X1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
        | ~ v3_tex_2(X1,sK1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f3529])).

fof(f3529,plain,
    ( ! [X19,X20] :
        ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X19,sK1)
        | ~ r1_tarski(X20,X19)
        | X19 = X20
        | ~ v3_tex_2(X20,sK1)
        | ~ r1_tarski(X20,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f2084,f224])).

fof(f2084,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | ~ r1_tarski(X3,X2)
        | X2 = X3
        | ~ v3_tex_2(X3,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f2083,f1424])).

fof(f2083,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_tex_2(X2,sK1)
        | ~ r1_tarski(X3,X2)
        | X2 = X3
        | ~ v3_tex_2(X3,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2075,f325])).

fof(f2075,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_tex_2(X2,sK1)
        | ~ r1_tarski(X3,X2)
        | X2 = X3
        | ~ v3_tex_2(X3,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f202,f1424])).

fof(f7679,plain,
    ( ~ spl31_1009
    | spl31_1022
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7605,f4726,f1423,f324,f7677,f7634])).

fof(f7677,plain,
    ( spl31_1022
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ v2_tex_2(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1022])])).

fof(f7605,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f2084])).

fof(f7675,plain,
    ( ~ spl31_1017
    | spl31_1018
    | ~ spl31_1021
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7604,f4726,f1225,f331,f317,f7673,f7667,f7661])).

fof(f7667,plain,
    ( spl31_1018
  <=> sK3 = sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1018])])).

fof(f7673,plain,
    ( spl31_1021
  <=> ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1021])])).

fof(f1225,plain,
    ( spl31_152
  <=> v2_tex_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_152])])).

fof(f7604,plain,
    ( ~ r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3)
    | sK3 = sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f2079])).

fof(f2079,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK3)
        | sK3 = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2078,f1226])).

fof(f1226,plain,
    ( v2_tex_2(sK3,sK0)
    | ~ spl31_152 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f2078,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK3,sK0)
        | ~ r1_tarski(X0,sK3)
        | sK3 = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_4 ),
    inference(subsumption_resolution,[],[f2062,f318])).

fof(f2062,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK3,sK0)
        | ~ r1_tarski(X0,sK3)
        | sK3 = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_4 ),
    inference(resolution,[],[f202,f332])).

fof(f7656,plain,
    ( spl31_1008
    | spl31_1014
    | ~ spl31_1011
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7603,f4726,f1423,f324,f7637,f7654,f7631])).

fof(f7654,plain,
    ( spl31_1014
  <=> r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1014])])).

fof(f7603,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f1872])).

fof(f7649,plain,
    ( spl31_1008
    | spl31_1012
    | ~ spl31_1011
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7602,f4726,f1423,f324,f7637,f7647,f7631])).

fof(f7647,plain,
    ( spl31_1012
  <=> v2_tex_2(sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1012])])).

fof(f7602,plain,
    ( ~ v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK4(sK1,sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f1855])).

fof(f7642,plain,
    ( ~ spl31_1009
    | spl31_1010
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(avatar_split_clause,[],[f7601,f4726,f1423,f324,f7640,f7634])).

fof(f7601,plain,
    ( v2_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v3_tex_2(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_704 ),
    inference(resolution,[],[f4727,f1476])).

fof(f1476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1435,f325])).

fof(f1435,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK1)
        | v2_tex_2(X0,sK1)
        | ~ v3_tex_2(X0,sK1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f203,f1424])).

fof(f7600,plain,
    ( ~ spl31_673
    | spl31_677 ),
    inference(avatar_split_clause,[],[f7597,f4590,f4574])).

fof(f4574,plain,
    ( spl31_673
  <=> ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_673])])).

fof(f4590,plain,
    ( spl31_677
  <=> ~ m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_677])])).

fof(f7597,plain,
    ( ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_677 ),
    inference(resolution,[],[f4591,f224])).

fof(f4591,plain,
    ( ~ m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_677 ),
    inference(avatar_component_clause,[],[f4590])).

fof(f7599,plain,
    ( ~ spl31_672
    | spl31_677 ),
    inference(avatar_contradiction_clause,[],[f7598])).

fof(f7598,plain,
    ( $false
    | ~ spl31_672
    | ~ spl31_677 ),
    inference(subsumption_resolution,[],[f7597,f4578])).

fof(f4578,plain,
    ( r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_672 ),
    inference(avatar_component_clause,[],[f4577])).

fof(f4577,plain,
    ( spl31_672
  <=> r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_672])])).

fof(f7516,plain,
    ( ~ spl31_875
    | ~ spl31_70
    | spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7515,f1423,f893,f650,f569,f6268])).

fof(f7515,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7514,f651])).

fof(f7514,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7513,f1424])).

fof(f7513,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7512,f894])).

fof(f894,plain,
    ( v7_struct_0(sK1)
    | ~ spl31_122 ),
    inference(avatar_component_clause,[],[f893])).

fof(f7511,plain,
    ( ~ spl31_875
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(avatar_split_clause,[],[f7510,f1650,f1574,f836,f650,f6268])).

fof(f7510,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7509,f651])).

fof(f7509,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(forward_demodulation,[],[f7508,f1575])).

fof(f7508,plain,
    ( ~ v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7507,f1651])).

fof(f1651,plain,
    ( v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_236 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f7506,plain,
    ( spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_874 ),
    inference(avatar_contradiction_clause,[],[f7505])).

fof(f7505,plain,
    ( $false
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7504,f651])).

fof(f7504,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_874 ),
    inference(forward_demodulation,[],[f7503,f1575])).

fof(f7503,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7502,f1651])).

fof(f7502,plain,
    ( ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7501,f837])).

fof(f7501,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7486,f6272])).

fof(f6272,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_874 ),
    inference(avatar_component_clause,[],[f6271])).

fof(f7500,plain,
    ( ~ spl31_70
    | spl31_89
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(avatar_contradiction_clause,[],[f7499])).

fof(f7499,plain,
    ( $false
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7498,f651])).

fof(f7498,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(forward_demodulation,[],[f7497,f1424])).

fof(f7497,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7496,f894])).

fof(f7496,plain,
    ( ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7495,f570])).

fof(f7495,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_194
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7485,f6272])).

fof(f7491,plain,
    ( ~ spl31_68
    | spl31_89
    | ~ spl31_120
    | ~ spl31_874 ),
    inference(avatar_contradiction_clause,[],[f7490])).

fof(f7490,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_89
    | ~ spl31_120
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7489,f651])).

fof(f7489,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7488,f884])).

fof(f7488,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_874 ),
    inference(subsumption_resolution,[],[f7483,f563])).

fof(f7483,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_874 ),
    inference(resolution,[],[f4913,f6272])).

fof(f7480,plain,
    ( ~ spl31_869
    | ~ spl31_70
    | spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7479,f1423,f893,f650,f569,f6248])).

fof(f7479,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7478,f651])).

fof(f7478,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7477,f1424])).

fof(f7477,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7476,f894])).

fof(f7475,plain,
    ( ~ spl31_869
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(avatar_split_clause,[],[f7474,f1650,f1574,f836,f650,f6248])).

fof(f7474,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7473,f651])).

fof(f7473,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(forward_demodulation,[],[f7472,f1575])).

fof(f7472,plain,
    ( ~ v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7471,f1651])).

fof(f7470,plain,
    ( spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_868 ),
    inference(avatar_contradiction_clause,[],[f7469])).

fof(f7469,plain,
    ( $false
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7468,f651])).

fof(f7468,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_868 ),
    inference(forward_demodulation,[],[f7467,f1575])).

fof(f7467,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7466,f1651])).

fof(f7466,plain,
    ( ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7465,f837])).

fof(f7465,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7450,f6252])).

fof(f6252,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_868 ),
    inference(avatar_component_clause,[],[f6251])).

fof(f7464,plain,
    ( ~ spl31_70
    | spl31_89
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(avatar_contradiction_clause,[],[f7463])).

fof(f7463,plain,
    ( $false
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7462,f651])).

fof(f7462,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(forward_demodulation,[],[f7461,f1424])).

fof(f7461,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7460,f894])).

fof(f7460,plain,
    ( ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7459,f570])).

fof(f7459,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_194
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7449,f6252])).

fof(f7455,plain,
    ( ~ spl31_68
    | spl31_89
    | ~ spl31_120
    | ~ spl31_868 ),
    inference(avatar_contradiction_clause,[],[f7454])).

fof(f7454,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_89
    | ~ spl31_120
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7453,f651])).

fof(f7453,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7452,f884])).

fof(f7452,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_868 ),
    inference(subsumption_resolution,[],[f7447,f563])).

fof(f7447,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_868 ),
    inference(resolution,[],[f4911,f6252])).

fof(f7445,plain,
    ( ~ spl31_1007
    | spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(avatar_split_clause,[],[f7444,f1650,f1574,f836,f650,f7438])).

fof(f7444,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7443,f651])).

fof(f7443,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(forward_demodulation,[],[f7442,f1575])).

fof(f7442,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7441,f1651])).

fof(f7440,plain,
    ( ~ spl31_1007
    | ~ spl31_70
    | spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7433,f1423,f893,f650,f569,f7438])).

fof(f7433,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_89
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7432,f651])).

fof(f7432,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f7431,f1424])).

fof(f7431,plain,
    ( ~ v1_subset_1(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7430,f894])).

fof(f7423,plain,
    ( ~ spl31_719
    | ~ spl31_116
    | ~ spl31_402
    | spl31_721 ),
    inference(avatar_split_clause,[],[f7422,f4902,f2613,f866,f4899])).

fof(f7422,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_116
    | ~ spl31_402
    | ~ spl31_721 ),
    inference(subsumption_resolution,[],[f7421,f4903])).

fof(f4903,plain,
    ( ~ v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_721 ),
    inference(avatar_component_clause,[],[f4902])).

fof(f7421,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_116
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f7397,f867])).

fof(f7419,plain,
    ( ~ spl31_711
    | ~ spl31_116
    | ~ spl31_364
    | spl31_713 ),
    inference(avatar_split_clause,[],[f7418,f4869,f2352,f866,f4866])).

fof(f7418,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_116
    | ~ spl31_364
    | ~ spl31_713 ),
    inference(subsumption_resolution,[],[f7417,f4870])).

fof(f7417,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_116
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f7394,f867])).

fof(f7415,plain,
    ( spl31_740
    | ~ spl31_2
    | ~ spl31_116
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7414,f1423,f866,f324,f5202])).

fof(f7414,plain,
    ( ! [X12] :
        ( ~ v1_subset_1(sK4(sK1,X12),u1_struct_0(sK0))
        | v1_xboole_0(sK4(sK1,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X12,sK1)
        | v3_tex_2(X12,sK1) )
    | ~ spl31_2
    | ~ spl31_116
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7391,f867])).

fof(f7376,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f7375,f1423,f883,f726,f562,f324,f3892])).

fof(f7375,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f7374,f884])).

fof(f7341,plain,
    ( spl31_1004
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7255,f6048,f373,f7339])).

fof(f7339,plain,
    ( spl31_1004
  <=> sK9 = sK27(sK27(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1004])])).

fof(f6048,plain,
    ( spl31_856
  <=> v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_856])])).

fof(f7255,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f1046])).

fof(f6049,plain,
    ( v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_856 ),
    inference(avatar_component_clause,[],[f6048])).

fof(f7334,plain,
    ( spl31_1002
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7254,f6048,f373,f7332])).

fof(f7332,plain,
    ( spl31_1002
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1002])])).

fof(f7254,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f1041])).

fof(f7327,plain,
    ( spl31_1000
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7253,f6048,f373,f7325])).

fof(f7325,plain,
    ( spl31_1000
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1000])])).

fof(f7253,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f1036])).

fof(f7320,plain,
    ( spl31_998
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7251,f6048,f373,f7318])).

fof(f7318,plain,
    ( spl31_998
  <=> sK9 = sK27(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_998])])).

fof(f7251,plain,
    ( sK9 = sK27(sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f819])).

fof(f7313,plain,
    ( spl31_996
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7250,f6048,f373,f7311])).

fof(f7311,plain,
    ( spl31_996
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_996])])).

fof(f7250,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f817])).

fof(f7306,plain,
    ( spl31_994
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7249,f6048,f373,f7304])).

fof(f7304,plain,
    ( spl31_994
  <=> sK5(k1_zfmisc_1(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_994])])).

fof(f7249,plain,
    ( sK5(k1_zfmisc_1(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f792])).

fof(f7299,plain,
    ( spl31_992
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7248,f6048,f373,f7297])).

fof(f7297,plain,
    ( spl31_992
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_992])])).

fof(f7248,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f790])).

fof(f7292,plain,
    ( spl31_990
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7247,f6048,f373,f7290])).

fof(f7290,plain,
    ( spl31_990
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_990])])).

fof(f7247,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f668])).

fof(f7285,plain,
    ( spl31_988
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7246,f6048,f373,f7283])).

fof(f7283,plain,
    ( spl31_988
  <=> sK9 = sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_988])])).

fof(f7246,plain,
    ( sK9 = sK27(sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f667])).

fof(f7278,plain,
    ( spl31_986
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7244,f6048,f373,f7276])).

fof(f7276,plain,
    ( spl31_986
  <=> sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_986])])).

fof(f7244,plain,
    ( sK5(k1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = sK9
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f663])).

fof(f7271,plain,
    ( spl31_984
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7242,f6048,f373,f7269])).

fof(f7269,plain,
    ( spl31_984
  <=> sK9 = sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_984])])).

fof(f7242,plain,
    ( sK9 = sK27(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f660])).

fof(f7264,plain,
    ( spl31_982
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7241,f6048,f373,f7262])).

fof(f7262,plain,
    ( spl31_982
  <=> sK9 = sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_982])])).

fof(f7241,plain,
    ( sK9 = sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_16
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f625])).

fof(f7257,plain,
    ( spl31_880
    | ~ spl31_856 ),
    inference(avatar_split_clause,[],[f7240,f6048,f6294])).

fof(f6294,plain,
    ( spl31_880
  <=> v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_880])])).

fof(f7240,plain,
    ( v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_856 ),
    inference(resolution,[],[f6049,f280])).

fof(f7234,plain,
    ( spl31_980
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7148,f5877,f373,f7232])).

fof(f7232,plain,
    ( spl31_980
  <=> sK9 = sK27(sK27(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_980])])).

fof(f5877,plain,
    ( spl31_830
  <=> v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_830])])).

fof(f7148,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f1046])).

fof(f5878,plain,
    ( v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_830 ),
    inference(avatar_component_clause,[],[f5877])).

fof(f7227,plain,
    ( spl31_978
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7147,f5877,f373,f7225])).

fof(f7225,plain,
    ( spl31_978
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_978])])).

fof(f7147,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f1041])).

fof(f7220,plain,
    ( spl31_976
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7146,f5877,f373,f7218])).

fof(f7218,plain,
    ( spl31_976
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_976])])).

fof(f7146,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f1036])).

fof(f7213,plain,
    ( spl31_974
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7144,f5877,f373,f7211])).

fof(f7211,plain,
    ( spl31_974
  <=> sK9 = sK27(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_974])])).

fof(f7144,plain,
    ( sK9 = sK27(sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f819])).

fof(f7206,plain,
    ( spl31_972
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7143,f5877,f373,f7204])).

fof(f7204,plain,
    ( spl31_972
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_972])])).

fof(f7143,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f817])).

fof(f7199,plain,
    ( spl31_970
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7142,f5877,f373,f7197])).

fof(f7197,plain,
    ( spl31_970
  <=> sK5(k1_zfmisc_1(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_970])])).

fof(f7142,plain,
    ( sK5(k1_zfmisc_1(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) = sK9
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f792])).

fof(f7192,plain,
    ( spl31_968
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7141,f5877,f373,f7190])).

fof(f7190,plain,
    ( spl31_968
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_968])])).

fof(f7141,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) = sK9
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f790])).

fof(f7185,plain,
    ( spl31_966
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7140,f5877,f373,f7183])).

fof(f7183,plain,
    ( spl31_966
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_966])])).

fof(f7140,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f668])).

fof(f7178,plain,
    ( spl31_964
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7139,f5877,f373,f7176])).

fof(f7176,plain,
    ( spl31_964
  <=> sK9 = sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_964])])).

fof(f7139,plain,
    ( sK9 = sK27(sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f667])).

fof(f7171,plain,
    ( spl31_962
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7137,f5877,f373,f7169])).

fof(f7169,plain,
    ( spl31_962
  <=> sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_962])])).

fof(f7137,plain,
    ( sK5(k1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) = sK9
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f663])).

fof(f7164,plain,
    ( spl31_960
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7135,f5877,f373,f7162])).

fof(f7162,plain,
    ( spl31_960
  <=> sK9 = sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_960])])).

fof(f7135,plain,
    ( sK9 = sK27(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f660])).

fof(f7157,plain,
    ( spl31_958
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7134,f5877,f373,f7155])).

fof(f7155,plain,
    ( spl31_958
  <=> sK9 = sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_958])])).

fof(f7134,plain,
    ( sK9 = sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_16
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f625])).

fof(f7150,plain,
    ( spl31_882
    | ~ spl31_830 ),
    inference(avatar_split_clause,[],[f7133,f5877,f6301])).

fof(f7133,plain,
    ( v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_830 ),
    inference(resolution,[],[f5878,f280])).

fof(f7123,plain,
    ( spl31_562
    | ~ spl31_520
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f7104,f5039,f3196,f3900])).

fof(f7104,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_520
    | ~ spl31_726 ),
    inference(resolution,[],[f7091,f3197])).

fof(f7091,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_zfmisc_1(X2) )
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f224])).

fof(f7122,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f7100,f5039,f1423,f324,f3892])).

fof(f7100,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(resolution,[],[f7091,f3321])).

fof(f7095,plain,
    ( spl31_562
    | ~ spl31_402
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f7076,f5039,f2613,f3900])).

fof(f7076,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f2614])).

fof(f7093,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f7070,f5039,f1423,f324,f3892])).

fof(f7070,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f1975])).

fof(f7068,plain,
    ( ~ spl31_719
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(avatar_split_clause,[],[f7067,f1650,f1574,f836,f811,f4899])).

fof(f7067,plain,
    ( ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7066,f1651])).

fof(f7061,plain,
    ( ~ spl31_68
    | spl31_101
    | ~ spl31_864 ),
    inference(avatar_contradiction_clause,[],[f7060])).

fof(f7060,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_864 ),
    inference(subsumption_resolution,[],[f7059,f727])).

fof(f7059,plain,
    ( v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_864 ),
    inference(subsumption_resolution,[],[f7040,f563])).

fof(f7040,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_864 ),
    inference(resolution,[],[f6238,f244])).

fof(f6238,plain,
    ( v1_xboole_0(sK15(sK0))
    | ~ spl31_864 ),
    inference(avatar_component_clause,[],[f6237])).

fof(f6237,plain,
    ( spl31_864
  <=> v1_xboole_0(sK15(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_864])])).

fof(f7039,plain,
    ( ~ spl31_711
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(avatar_split_clause,[],[f7038,f1650,f1574,f836,f811,f4866])).

fof(f7038,plain,
    ( ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_236 ),
    inference(subsumption_resolution,[],[f7037,f1651])).

fof(f7035,plain,
    ( ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_862 ),
    inference(avatar_contradiction_clause,[],[f7034])).

fof(f7034,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_862 ),
    inference(subsumption_resolution,[],[f7033,f884])).

fof(f7033,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_862 ),
    inference(subsumption_resolution,[],[f7032,f727])).

fof(f7032,plain,
    ( v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_862 ),
    inference(subsumption_resolution,[],[f7028,f563])).

fof(f7028,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl31_862 ),
    inference(resolution,[],[f4842,f6232])).

fof(f6232,plain,
    ( v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ spl31_862 ),
    inference(avatar_component_clause,[],[f6231])).

fof(f7018,plain,
    ( ~ spl31_955
    | spl31_956
    | ~ spl31_126 ),
    inference(avatar_split_clause,[],[f7005,f956,f7016,f7010])).

fof(f7010,plain,
    ( spl31_955
  <=> ~ v1_xboole_0(u1_pre_topc(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_955])])).

fof(f7016,plain,
    ( spl31_956
  <=> v1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_956])])).

fof(f956,plain,
    ( spl31_126
  <=> m1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(k1_zfmisc_1(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_126])])).

fof(f7005,plain,
    ( v1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(sK9))
    | ~ v1_xboole_0(u1_pre_topc(sK11))
    | ~ spl31_126 ),
    inference(subsumption_resolution,[],[f6937,f221])).

fof(f6937,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK9))
    | v1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(sK9))
    | ~ v1_xboole_0(u1_pre_topc(sK11))
    | ~ spl31_126 ),
    inference(resolution,[],[f308,f957])).

fof(f957,plain,
    ( m1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(k1_zfmisc_1(sK9)))
    | ~ spl31_126 ),
    inference(avatar_component_clause,[],[f956])).

fof(f7004,plain,
    ( ~ spl31_951
    | spl31_952
    | ~ spl31_170 ),
    inference(avatar_split_clause,[],[f6991,f1314,f7002,f6996])).

fof(f6996,plain,
    ( spl31_951
  <=> ~ v1_xboole_0(u1_pre_topc(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_951])])).

fof(f7002,plain,
    ( spl31_952
  <=> v1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(u1_struct_0(sK14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_952])])).

fof(f1314,plain,
    ( spl31_170
  <=> m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_170])])).

fof(f6991,plain,
    ( v1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(u1_struct_0(sK14)))
    | ~ v1_xboole_0(u1_pre_topc(sK14))
    | ~ spl31_170 ),
    inference(subsumption_resolution,[],[f6936,f221])).

fof(f6936,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK14)))
    | v1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(u1_struct_0(sK14)))
    | ~ v1_xboole_0(u1_pre_topc(sK14))
    | ~ spl31_170 ),
    inference(resolution,[],[f308,f1315])).

fof(f1315,plain,
    ( m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))))
    | ~ spl31_170 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f6990,plain,
    ( ~ spl31_947
    | spl31_948
    | ~ spl31_166 ),
    inference(avatar_split_clause,[],[f6977,f1304,f6988,f6982])).

fof(f6982,plain,
    ( spl31_947
  <=> ~ v1_xboole_0(u1_pre_topc(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_947])])).

fof(f6988,plain,
    ( spl31_948
  <=> v1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(u1_struct_0(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_948])])).

fof(f1304,plain,
    ( spl31_166
  <=> m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_166])])).

fof(f6977,plain,
    ( v1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ v1_xboole_0(u1_pre_topc(sK13))
    | ~ spl31_166 ),
    inference(subsumption_resolution,[],[f6935,f221])).

fof(f6935,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK13)))
    | v1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ v1_xboole_0(u1_pre_topc(sK13))
    | ~ spl31_166 ),
    inference(resolution,[],[f308,f1305])).

fof(f1305,plain,
    ( m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))))
    | ~ spl31_166 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f6976,plain,
    ( ~ spl31_943
    | spl31_944
    | ~ spl31_162 ),
    inference(avatar_split_clause,[],[f6963,f1294,f6974,f6968])).

fof(f6968,plain,
    ( spl31_943
  <=> ~ v1_xboole_0(u1_pre_topc(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_943])])).

fof(f6974,plain,
    ( spl31_944
  <=> v1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(u1_struct_0(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_944])])).

fof(f1294,plain,
    ( spl31_162
  <=> m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_162])])).

fof(f6963,plain,
    ( v1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(u1_struct_0(sK12)))
    | ~ v1_xboole_0(u1_pre_topc(sK12))
    | ~ spl31_162 ),
    inference(subsumption_resolution,[],[f6934,f221])).

fof(f6934,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK12)))
    | v1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(u1_struct_0(sK12)))
    | ~ v1_xboole_0(u1_pre_topc(sK12))
    | ~ spl31_162 ),
    inference(resolution,[],[f308,f1295])).

fof(f1295,plain,
    ( m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12))))
    | ~ spl31_162 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f6962,plain,
    ( ~ spl31_939
    | spl31_940
    | ~ spl31_286 ),
    inference(avatar_split_clause,[],[f6949,f1923,f6960,f6954])).

fof(f6954,plain,
    ( spl31_939
  <=> ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_939])])).

fof(f6960,plain,
    ( spl31_940
  <=> v1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_940])])).

fof(f1923,plain,
    ( spl31_286
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_286])])).

fof(f6949,plain,
    ( v1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl31_286 ),
    inference(subsumption_resolution,[],[f6933,f221])).

fof(f6933,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl31_286 ),
    inference(resolution,[],[f308,f1924])).

fof(f1924,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_286 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f6947,plain,
    ( ~ spl31_713
    | spl31_710
    | spl31_89
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f6946,f2352,f650,f4863,f4869])).

fof(f6946,plain,
    ( v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_89
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f6923,f651])).

fof(f6923,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364 ),
    inference(resolution,[],[f308,f2353])).

fof(f6908,plain,
    ( spl31_236
    | spl31_874
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f6907,f1574,f836,f6271,f1650])).

fof(f6907,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6906,f837])).

fof(f6906,plain,
    ( v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f5092,f1575])).

fof(f6903,plain,
    ( spl31_236
    | spl31_868
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f6902,f1574,f836,f6251,f1650])).

fof(f6902,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6901,f837])).

fof(f6901,plain,
    ( v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f5089,f1575])).

fof(f6898,plain,
    ( spl31_562
    | spl31_107
    | ~ spl31_110
    | ~ spl31_116
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f6897,f1574,f866,f836,f811,f3900])).

fof(f6897,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_116
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6896,f837])).

fof(f6896,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_107
    | ~ spl31_116
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6895,f812])).

fof(f6895,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_116
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6892,f867])).

fof(f6892,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f2543,f1575])).

fof(f2543,plain,(
    ! [X6] :
      ( ~ v1_zfmisc_1(u1_struct_0(X6))
      | v2_struct_0(X6)
      | ~ l1_struct_0(X6)
      | v1_zfmisc_1(sK16(X6)) ) ),
    inference(resolution,[],[f246,f282])).

fof(f6860,plain,
    ( spl31_724
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f6858,f4718,f4990])).

fof(f6858,plain,
    ( r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f225])).

fof(f6833,plain,
    ( ~ spl31_557
    | spl31_774
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_666 ),
    inference(avatar_split_clause,[],[f6623,f4553,f883,f726,f562,f5439,f3876])).

fof(f5439,plain,
    ( spl31_774
  <=> v1_xboole_0(sK20(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_774])])).

fof(f6623,plain,
    ( v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6622,f727])).

fof(f6622,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6621,f563])).

fof(f6621,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6609,f884])).

fof(f6832,plain,
    ( spl31_936
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6748,f5439,f373,f6830])).

fof(f6830,plain,
    ( spl31_936
  <=> sK9 = sK27(sK27(sK27(sK27(sK20(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_936])])).

fof(f6748,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK20(sK1)))))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f1046])).

fof(f5440,plain,
    ( v1_xboole_0(sK20(sK1))
    | ~ spl31_774 ),
    inference(avatar_component_clause,[],[f5439])).

fof(f6825,plain,
    ( spl31_934
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6747,f5439,f373,f6823])).

fof(f6823,plain,
    ( spl31_934
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK20(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_934])])).

fof(f6747,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK20(sK1)))))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f1041])).

fof(f6818,plain,
    ( spl31_932
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6746,f5439,f373,f6816])).

fof(f6816,plain,
    ( spl31_932
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK20(sK1))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_932])])).

fof(f6746,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK20(sK1))))) = sK9
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f1036])).

fof(f6811,plain,
    ( spl31_930
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6744,f5439,f373,f6809])).

fof(f6809,plain,
    ( spl31_930
  <=> sK9 = sK27(sK27(sK27(sK20(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_930])])).

fof(f6744,plain,
    ( sK9 = sK27(sK27(sK27(sK20(sK1))))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f819])).

fof(f6804,plain,
    ( spl31_928
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6743,f5439,f373,f6802])).

fof(f6802,plain,
    ( spl31_928
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK20(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_928])])).

fof(f6743,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK20(sK1)))))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f817])).

fof(f6797,plain,
    ( spl31_926
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6742,f5439,f373,f6795])).

fof(f6795,plain,
    ( spl31_926
  <=> sK5(k1_zfmisc_1(sK27(sK20(sK1)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_926])])).

fof(f6742,plain,
    ( sK5(k1_zfmisc_1(sK27(sK20(sK1)))) = sK9
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f792])).

fof(f6790,plain,
    ( spl31_924
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6741,f5439,f373,f6788])).

fof(f6788,plain,
    ( spl31_924
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK20(sK1))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_924])])).

fof(f6741,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK20(sK1))))) = sK9
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f790])).

fof(f6783,plain,
    ( spl31_922
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6740,f5439,f373,f6781])).

fof(f6781,plain,
    ( spl31_922
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK20(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_922])])).

fof(f6740,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK20(sK1))))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f668])).

fof(f6776,plain,
    ( spl31_920
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6739,f5439,f373,f6774])).

fof(f6774,plain,
    ( spl31_920
  <=> sK9 = sK27(sK27(sK20(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_920])])).

fof(f6739,plain,
    ( sK9 = sK27(sK27(sK20(sK1)))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f667])).

fof(f6769,plain,
    ( spl31_918
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6737,f5439,f373,f6767])).

fof(f6767,plain,
    ( spl31_918
  <=> sK5(k1_zfmisc_1(sK20(sK1))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_918])])).

fof(f6737,plain,
    ( sK5(k1_zfmisc_1(sK20(sK1))) = sK9
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f663])).

fof(f6762,plain,
    ( spl31_916
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6735,f5439,f373,f6760])).

fof(f6760,plain,
    ( spl31_916
  <=> sK9 = sK27(sK20(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_916])])).

fof(f6735,plain,
    ( sK9 = sK27(sK20(sK1))
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f660])).

fof(f6755,plain,
    ( spl31_914
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(avatar_split_clause,[],[f6734,f5439,f373,f6753])).

fof(f6753,plain,
    ( spl31_914
  <=> sK9 = sK20(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_914])])).

fof(f6734,plain,
    ( sK9 = sK20(sK1)
    | ~ spl31_16
    | ~ spl31_774 ),
    inference(resolution,[],[f5440,f625])).

fof(f6730,plain,
    ( ~ spl31_661
    | spl31_665 ),
    inference(avatar_split_clause,[],[f6729,f4542,f4526])).

fof(f4526,plain,
    ( spl31_661
  <=> ~ r1_tarski(sK21(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_661])])).

fof(f4542,plain,
    ( spl31_665
  <=> ~ m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_665])])).

fof(f6729,plain,
    ( ~ r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_665 ),
    inference(resolution,[],[f4543,f224])).

fof(f4543,plain,
    ( ~ m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_665 ),
    inference(avatar_component_clause,[],[f4542])).

fof(f6728,plain,
    ( spl31_912
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6644,f5357,f373,f6726])).

fof(f6726,plain,
    ( spl31_912
  <=> sK9 = sK27(sK27(sK27(sK27(sK21(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_912])])).

fof(f5357,plain,
    ( spl31_756
  <=> v1_xboole_0(sK21(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_756])])).

fof(f6644,plain,
    ( sK9 = sK27(sK27(sK27(sK27(sK21(sK1)))))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f1046])).

fof(f5358,plain,
    ( v1_xboole_0(sK21(sK1))
    | ~ spl31_756 ),
    inference(avatar_component_clause,[],[f5357])).

fof(f6721,plain,
    ( spl31_910
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6643,f5357,f373,f6719])).

fof(f6719,plain,
    ( spl31_910
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK21(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_910])])).

fof(f6643,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK21(sK1)))))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f1041])).

fof(f6714,plain,
    ( spl31_908
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6642,f5357,f373,f6712])).

fof(f6712,plain,
    ( spl31_908
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK21(sK1))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_908])])).

fof(f6642,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK21(sK1))))) = sK9
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f1036])).

fof(f6707,plain,
    ( spl31_906
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6640,f5357,f373,f6705])).

fof(f6705,plain,
    ( spl31_906
  <=> sK9 = sK27(sK27(sK27(sK21(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_906])])).

fof(f6640,plain,
    ( sK9 = sK27(sK27(sK27(sK21(sK1))))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f819])).

fof(f6700,plain,
    ( spl31_904
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6639,f5357,f373,f6698])).

fof(f6698,plain,
    ( spl31_904
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK21(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_904])])).

fof(f6639,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK21(sK1)))))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f817])).

fof(f6693,plain,
    ( spl31_902
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6638,f5357,f373,f6691])).

fof(f6691,plain,
    ( spl31_902
  <=> sK5(k1_zfmisc_1(sK27(sK21(sK1)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_902])])).

fof(f6638,plain,
    ( sK5(k1_zfmisc_1(sK27(sK21(sK1)))) = sK9
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f792])).

fof(f6686,plain,
    ( spl31_900
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6637,f5357,f373,f6684])).

fof(f6684,plain,
    ( spl31_900
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK21(sK1))))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_900])])).

fof(f6637,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK21(sK1))))) = sK9
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f790])).

fof(f6679,plain,
    ( spl31_898
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6636,f5357,f373,f6677])).

fof(f6677,plain,
    ( spl31_898
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK21(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_898])])).

fof(f6636,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK21(sK1))))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f668])).

fof(f6672,plain,
    ( spl31_896
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6635,f5357,f373,f6670])).

fof(f6670,plain,
    ( spl31_896
  <=> sK9 = sK27(sK27(sK21(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_896])])).

fof(f6635,plain,
    ( sK9 = sK27(sK27(sK21(sK1)))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f667])).

fof(f6665,plain,
    ( spl31_894
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6633,f5357,f373,f6663])).

fof(f6663,plain,
    ( spl31_894
  <=> sK5(k1_zfmisc_1(sK21(sK1))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_894])])).

fof(f6633,plain,
    ( sK5(k1_zfmisc_1(sK21(sK1))) = sK9
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f663])).

fof(f6658,plain,
    ( spl31_892
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6631,f5357,f373,f6656])).

fof(f6656,plain,
    ( spl31_892
  <=> sK9 = sK27(sK21(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_892])])).

fof(f6631,plain,
    ( sK9 = sK27(sK21(sK1))
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f660])).

fof(f6651,plain,
    ( spl31_890
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(avatar_split_clause,[],[f6630,f5357,f373,f6649])).

fof(f6649,plain,
    ( spl31_890
  <=> sK9 = sK21(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_890])])).

fof(f6630,plain,
    ( sK9 = sK21(sK1)
    | ~ spl31_16
    | ~ spl31_756 ),
    inference(resolution,[],[f5358,f625])).

fof(f6626,plain,
    ( spl31_662
    | ~ spl31_666 ),
    inference(avatar_split_clause,[],[f6619,f4553,f4537])).

fof(f4537,plain,
    ( spl31_662
  <=> r1_tarski(sK20(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_662])])).

fof(f6619,plain,
    ( r1_tarski(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f225])).

fof(f6625,plain,
    ( spl31_774
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_556
    | ~ spl31_666 ),
    inference(avatar_split_clause,[],[f6624,f4553,f3879,f883,f726,f562,f5439])).

fof(f6624,plain,
    ( v1_xboole_0(sK20(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_556
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6623,f3880])).

fof(f3880,plain,
    ( v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_556 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f6594,plain,
    ( spl31_660
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f6581,f4545,f4529])).

fof(f6581,plain,
    ( r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f225])).

fof(f6593,plain,
    ( spl31_886
    | ~ spl31_116
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f6592,f4545,f866,f6321])).

fof(f6321,plain,
    ( spl31_886
  <=> v1_zfmisc_1(sK21(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_886])])).

fof(f6592,plain,
    ( v1_zfmisc_1(sK21(sK1))
    | ~ spl31_116
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6580,f867])).

fof(f6580,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f282])).

fof(f6591,plain,
    ( spl31_886
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f6590,f4545,f883,f726,f562,f6321])).

fof(f6590,plain,
    ( v1_zfmisc_1(sK21(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6589,f727])).

fof(f6589,plain,
    ( v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6588,f563])).

fof(f6588,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6577,f884])).

fof(f6577,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f4985])).

fof(f6587,plain,
    ( spl31_756
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_568
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f6586,f4545,f3942,f883,f726,f562,f5357])).

fof(f3942,plain,
    ( spl31_568
  <=> v1_subset_1(sK21(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_568])])).

fof(f6586,plain,
    ( v1_xboole_0(sK21(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_568
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6585,f3943])).

fof(f3943,plain,
    ( v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_568 ),
    inference(avatar_component_clause,[],[f3942])).

fof(f6585,plain,
    ( v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6584,f727])).

fof(f6584,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6583,f563])).

fof(f6583,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6571,f884])).

fof(f6571,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f258])).

fof(f6554,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f6553,f1423,f873,f866])).

fof(f873,plain,
    ( spl31_118
  <=> v1_zfmisc_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_118])])).

fof(f6553,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f874,plain,
    ( v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl31_118 ),
    inference(avatar_component_clause,[],[f873])).

fof(f6552,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f6551,f1423,f876,f869])).

fof(f6551,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f6550,plain,
    ( spl31_714
    | spl31_120
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_566
    | spl31_717 ),
    inference(avatar_split_clause,[],[f6549,f4886,f3916,f2604,f562,f883,f4880])).

fof(f6549,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_566
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f5168,f3917])).

fof(f5168,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f5167,f4887])).

fof(f5167,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_68
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f5059,f563])).

fof(f5059,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_400 ),
    inference(resolution,[],[f5048,f2605])).

fof(f6548,plain,
    ( ~ spl31_715
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_400
    | spl31_717 ),
    inference(avatar_split_clause,[],[f6547,f4886,f2604,f726,f562,f886,f4883])).

fof(f6547,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_400
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f6546,f4887])).

fof(f6546,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f6545,f727])).

fof(f6545,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f4815,f563])).

fof(f4815,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400 ),
    inference(resolution,[],[f258,f2605])).

fof(f6544,plain,
    ( spl31_236
    | spl31_888
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f6537,f1574,f836,f6542,f1650])).

fof(f6542,plain,
    ( spl31_888
  <=> r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_888])])).

fof(f6537,plain,
    ( r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f6439,f837])).

fof(f6439,plain,
    ( r1_tarski(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4625,f1575])).

fof(f4625,plain,(
    ! [X11] :
      ( r1_tarski(sK22(X11),u1_struct_0(X11))
      | v7_struct_0(X11)
      | ~ l1_struct_0(X11) ) ),
    inference(resolution,[],[f4141,f225])).

fof(f6536,plain,
    ( spl31_122
    | ~ spl31_70
    | spl31_885 ),
    inference(avatar_split_clause,[],[f6535,f6311,f569,f893])).

fof(f6311,plain,
    ( spl31_885
  <=> ~ v1_zfmisc_1(sK20(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_885])])).

fof(f6535,plain,
    ( v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_885 ),
    inference(subsumption_resolution,[],[f6365,f570])).

fof(f6365,plain,
    ( ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_885 ),
    inference(resolution,[],[f6312,f1050])).

fof(f1050,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK20(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f261,f274])).

fof(f261,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(sK20(X0)) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f6312,plain,
    ( ~ v1_zfmisc_1(sK20(sK1))
    | ~ spl31_885 ),
    inference(avatar_component_clause,[],[f6311])).

fof(f6534,plain,
    ( spl31_122
    | ~ spl31_70
    | spl31_887 ),
    inference(avatar_split_clause,[],[f6533,f6318,f569,f893])).

fof(f6318,plain,
    ( spl31_887
  <=> ~ v1_zfmisc_1(sK21(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_887])])).

fof(f6533,plain,
    ( v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_887 ),
    inference(subsumption_resolution,[],[f6366,f570])).

fof(f6366,plain,
    ( ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_887 ),
    inference(resolution,[],[f6319,f1052])).

fof(f1052,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK21(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f265,f274])).

fof(f265,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(sK21(X0)) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f6319,plain,
    ( ~ v1_zfmisc_1(sK21(sK1))
    | ~ spl31_887 ),
    inference(avatar_component_clause,[],[f6318])).

fof(f6532,plain,
    ( spl31_122
    | spl31_724
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f6531,f1423,f569,f4990,f893])).

fof(f6531,plain,
    ( r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f6438,f570])).

fof(f6438,plain,
    ( r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4625,f1424])).

fof(f6530,plain,
    ( spl31_107
    | ~ spl31_110
    | ~ spl31_712 ),
    inference(avatar_contradiction_clause,[],[f6529])).

fof(f6529,plain,
    ( $false
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_712 ),
    inference(subsumption_resolution,[],[f6528,f812])).

fof(f6528,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_712 ),
    inference(subsumption_resolution,[],[f6510,f837])).

fof(f6510,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_712 ),
    inference(resolution,[],[f4873,f244])).

fof(f4873,plain,
    ( v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_712 ),
    inference(avatar_component_clause,[],[f4872])).

fof(f4872,plain,
    ( spl31_712
  <=> v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_712])])).

fof(f6489,plain,
    ( spl31_562
    | ~ spl31_520
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f6472,f5039,f3196,f3900])).

fof(f6472,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_520
    | ~ spl31_726 ),
    inference(resolution,[],[f6462,f3197])).

fof(f6462,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v1_zfmisc_1(X2) )
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f224])).

fof(f6488,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f6468,f5039,f1423,f324,f3892])).

fof(f6468,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(resolution,[],[f6462,f3321])).

fof(f6466,plain,
    ( spl31_562
    | ~ spl31_402
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f6449,f5039,f2613,f3900])).

fof(f6449,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f2614])).

fof(f6464,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f6443,f5039,f1423,f324,f3892])).

fof(f6443,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f1975])).

fof(f6378,plain,
    ( ~ spl31_725
    | spl31_703 ),
    inference(avatar_split_clause,[],[f6377,f4715,f4993])).

fof(f4993,plain,
    ( spl31_725
  <=> ~ r1_tarski(sK22(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_725])])).

fof(f4715,plain,
    ( spl31_703
  <=> ~ m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_703])])).

fof(f6377,plain,
    ( ~ r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_703 ),
    inference(resolution,[],[f4716,f224])).

fof(f4716,plain,
    ( ~ m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_703 ),
    inference(avatar_component_clause,[],[f4715])).

fof(f6376,plain,
    ( spl31_89
    | spl31_879 ),
    inference(avatar_contradiction_clause,[],[f6375])).

fof(f6375,plain,
    ( $false
    | ~ spl31_89
    | ~ spl31_879 ),
    inference(subsumption_resolution,[],[f6374,f651])).

fof(f6374,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_879 ),
    inference(resolution,[],[f6284,f288])).

fof(f6284,plain,
    ( ~ v1_zfmisc_1(sK26(u1_struct_0(sK0)))
    | ~ spl31_879 ),
    inference(avatar_component_clause,[],[f6283])).

fof(f6283,plain,
    ( spl31_879
  <=> ~ v1_zfmisc_1(sK26(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_879])])).

fof(f6373,plain,
    ( ~ spl31_663
    | spl31_667 ),
    inference(avatar_split_clause,[],[f6372,f4550,f4534])).

fof(f4534,plain,
    ( spl31_663
  <=> ~ r1_tarski(sK20(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_663])])).

fof(f4550,plain,
    ( spl31_667
  <=> ~ m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_667])])).

fof(f6372,plain,
    ( ~ r1_tarski(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_667 ),
    inference(resolution,[],[f4551,f224])).

fof(f4551,plain,
    ( ~ m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_667 ),
    inference(avatar_component_clause,[],[f4550])).

fof(f6371,plain,
    ( spl31_89
    | spl31_873 ),
    inference(avatar_contradiction_clause,[],[f6370])).

fof(f6370,plain,
    ( $false
    | ~ spl31_89
    | ~ spl31_873 ),
    inference(subsumption_resolution,[],[f6369,f651])).

fof(f6369,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_873 ),
    inference(resolution,[],[f6264,f285])).

fof(f6264,plain,
    ( ~ v1_zfmisc_1(sK25(u1_struct_0(sK0)))
    | ~ spl31_873 ),
    inference(avatar_component_clause,[],[f6263])).

fof(f6263,plain,
    ( spl31_873
  <=> ~ v1_zfmisc_1(sK25(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_873])])).

fof(f6368,plain,
    ( ~ spl31_661
    | spl31_665 ),
    inference(avatar_split_clause,[],[f6367,f4542,f4526])).

fof(f6367,plain,
    ( ~ r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_665 ),
    inference(resolution,[],[f4543,f224])).

fof(f6363,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f6362,f1423,f873,f866])).

fof(f6362,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f6361,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_568
    | ~ spl31_664
    | spl31_757 ),
    inference(avatar_split_clause,[],[f6360,f5354,f4545,f3942,f726,f562,f886])).

fof(f5354,plain,
    ( spl31_757
  <=> ~ v1_xboole_0(sK21(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_757])])).

fof(f6360,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_568
    | ~ spl31_664
    | ~ spl31_757 ),
    inference(subsumption_resolution,[],[f6359,f3943])).

fof(f6359,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_664
    | ~ spl31_757 ),
    inference(subsumption_resolution,[],[f6358,f5355])).

fof(f5355,plain,
    ( ~ v1_xboole_0(sK21(sK1))
    | ~ spl31_757 ),
    inference(avatar_component_clause,[],[f5354])).

fof(f6358,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6357,f727])).

fof(f6357,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f5504,f563])).

fof(f5504,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f258])).

fof(f6356,plain,
    ( spl31_886
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f6355,f4545,f726,f562,f886,f6321])).

fof(f6355,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f6354,f727])).

fof(f6354,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_68
    | ~ spl31_664 ),
    inference(subsumption_resolution,[],[f5507,f563])).

fof(f5507,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f4985])).

fof(f6353,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_556
    | ~ spl31_666
    | spl31_775 ),
    inference(avatar_split_clause,[],[f6352,f5436,f4553,f3879,f726,f562,f886])).

fof(f6352,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_556
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f6351,f3880])).

fof(f6351,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_666
    | ~ spl31_775 ),
    inference(subsumption_resolution,[],[f6350,f5437])).

fof(f6350,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6349,f727])).

fof(f6349,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f5526,f563])).

fof(f5526,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f258])).

fof(f6348,plain,
    ( spl31_884
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_666 ),
    inference(avatar_split_clause,[],[f6347,f4553,f726,f562,f886,f6314])).

fof(f6347,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK20(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f6346,f727])).

fof(f6346,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK20(sK1))
    | ~ spl31_68
    | ~ spl31_666 ),
    inference(subsumption_resolution,[],[f5529,f563])).

fof(f5529,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK20(sK1))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f4985])).

fof(f6345,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_702
    | spl31_811 ),
    inference(avatar_split_clause,[],[f6344,f5696,f4718,f726,f562,f886])).

fof(f6344,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_702
    | ~ spl31_811 ),
    inference(subsumption_resolution,[],[f6343,f5697])).

fof(f5697,plain,
    ( ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_811 ),
    inference(avatar_component_clause,[],[f5696])).

fof(f6343,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f6342,f727])).

fof(f6342,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5591,f563])).

fof(f5591,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f4985])).

fof(f6341,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_570
    | ~ spl31_674
    | spl31_831 ),
    inference(avatar_split_clause,[],[f6340,f5874,f4585,f3951,f726,f562,f886])).

fof(f6340,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_570
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f6339,f3952])).

fof(f3952,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_570 ),
    inference(avatar_component_clause,[],[f3951])).

fof(f6339,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_674
    | ~ spl31_831 ),
    inference(subsumption_resolution,[],[f6338,f5875])).

fof(f6338,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f6337,f727])).

fof(f6337,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f6159,f563])).

fof(f6159,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f258])).

fof(f6336,plain,
    ( spl31_882
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_674 ),
    inference(avatar_split_clause,[],[f6335,f4585,f726,f562,f886,f6301])).

fof(f6335,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f6334,f727])).

fof(f6334,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_674 ),
    inference(subsumption_resolution,[],[f6165,f563])).

fof(f6165,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f4985])).

fof(f6333,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_558
    | ~ spl31_676
    | spl31_857 ),
    inference(avatar_split_clause,[],[f6332,f6045,f4593,f3888,f726,f562,f886])).

fof(f3888,plain,
    ( spl31_558
  <=> v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_558])])).

fof(f4593,plain,
    ( spl31_676
  <=> m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_676])])).

fof(f6045,plain,
    ( spl31_857
  <=> ~ v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_857])])).

fof(f6332,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_558
    | ~ spl31_676
    | ~ spl31_857 ),
    inference(subsumption_resolution,[],[f6331,f3889])).

fof(f3889,plain,
    ( v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_558 ),
    inference(avatar_component_clause,[],[f3888])).

fof(f6331,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_676
    | ~ spl31_857 ),
    inference(subsumption_resolution,[],[f6330,f6046])).

fof(f6046,plain,
    ( ~ v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_857 ),
    inference(avatar_component_clause,[],[f6045])).

fof(f6330,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_676 ),
    inference(subsumption_resolution,[],[f6329,f727])).

fof(f6329,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_676 ),
    inference(subsumption_resolution,[],[f6184,f563])).

fof(f6184,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_676 ),
    inference(resolution,[],[f4594,f258])).

fof(f4594,plain,
    ( m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_676 ),
    inference(avatar_component_clause,[],[f4593])).

fof(f6328,plain,
    ( spl31_880
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_676 ),
    inference(avatar_split_clause,[],[f6327,f4593,f726,f562,f886,f6294])).

fof(f6327,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_676 ),
    inference(subsumption_resolution,[],[f6326,f727])).

fof(f6326,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_676 ),
    inference(subsumption_resolution,[],[f6190,f563])).

fof(f6190,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_676 ),
    inference(resolution,[],[f4594,f4985])).

fof(f6325,plain,
    ( ~ spl31_117
    | spl31_886
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5313,f4529,f6321,f869])).

fof(f5313,plain,
    ( v1_zfmisc_1(sK21(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f854])).

fof(f4530,plain,
    ( r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_660 ),
    inference(avatar_component_clause,[],[f4529])).

fof(f6324,plain,
    ( ~ spl31_117
    | spl31_884
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5395,f4537,f6314,f869])).

fof(f5395,plain,
    ( v1_zfmisc_1(sK20(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f854])).

fof(f4538,plain,
    ( r1_tarski(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_662 ),
    inference(avatar_component_clause,[],[f4537])).

fof(f6323,plain,
    ( spl31_886
    | ~ spl31_117
    | ~ spl31_664 ),
    inference(avatar_split_clause,[],[f5510,f4545,f869,f6321])).

fof(f5510,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK21(sK1))
    | ~ spl31_664 ),
    inference(resolution,[],[f4546,f282])).

fof(f6316,plain,
    ( spl31_884
    | ~ spl31_117
    | ~ spl31_666 ),
    inference(avatar_split_clause,[],[f5532,f4553,f869,f6314])).

fof(f5532,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK20(sK1))
    | ~ spl31_666 ),
    inference(resolution,[],[f4554,f282])).

fof(f6309,plain,
    ( ~ spl31_117
    | ~ spl31_702
    | spl31_811 ),
    inference(avatar_split_clause,[],[f6308,f5696,f4718,f869])).

fof(f6308,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_702
    | ~ spl31_811 ),
    inference(subsumption_resolution,[],[f5594,f5697])).

fof(f5594,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f282])).

fof(f6307,plain,
    ( ~ spl31_117
    | ~ spl31_724
    | spl31_811 ),
    inference(avatar_split_clause,[],[f6306,f5696,f4990,f869])).

fof(f6306,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_724
    | ~ spl31_811 ),
    inference(subsumption_resolution,[],[f5765,f5697])).

fof(f5765,plain,
    ( v1_zfmisc_1(sK22(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_724 ),
    inference(resolution,[],[f4991,f854])).

fof(f6305,plain,
    ( ~ spl31_117
    | spl31_882
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5833,f4569,f6301,f869])).

fof(f5833,plain,
    ( v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f854])).

fof(f6304,plain,
    ( ~ spl31_117
    | spl31_880
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f6004,f4577,f6294,f869])).

fof(f6004,plain,
    ( v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f854])).

fof(f6303,plain,
    ( spl31_882
    | ~ spl31_117
    | ~ spl31_674 ),
    inference(avatar_split_clause,[],[f6168,f4585,f869,f6301])).

fof(f6168,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_674 ),
    inference(resolution,[],[f4586,f282])).

fof(f6296,plain,
    ( spl31_880
    | ~ spl31_117
    | ~ spl31_676 ),
    inference(avatar_split_clause,[],[f6193,f4593,f869,f6294])).

fof(f6193,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_676 ),
    inference(resolution,[],[f4594,f282])).

fof(f6289,plain,
    ( ~ spl31_68
    | spl31_101
    | spl31_867 ),
    inference(avatar_contradiction_clause,[],[f6288])).

fof(f6288,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_867 ),
    inference(subsumption_resolution,[],[f6287,f727])).

fof(f6287,plain,
    ( v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_867 ),
    inference(subsumption_resolution,[],[f6286,f563])).

fof(f6286,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_867 ),
    inference(resolution,[],[f6244,f245])).

fof(f245,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK15(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f6244,plain,
    ( ~ v1_zfmisc_1(sK15(sK0))
    | ~ spl31_867 ),
    inference(avatar_component_clause,[],[f6243])).

fof(f6243,plain,
    ( spl31_867
  <=> ~ v1_zfmisc_1(sK15(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_867])])).

fof(f6285,plain,
    ( spl31_874
    | spl31_876
    | ~ spl31_879
    | spl31_89
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f6266,f5208,f650,f6283,f6277,f6271])).

fof(f6277,plain,
    ( spl31_876
  <=> v1_xboole_0(sK26(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_876])])).

fof(f6266,plain,
    ( ~ v1_zfmisc_1(sK26(u1_struct_0(sK0)))
    | v1_xboole_0(sK26(u1_struct_0(sK0)))
    | v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f6216,f651])).

fof(f6216,plain,
    ( ~ v1_zfmisc_1(sK26(u1_struct_0(sK0)))
    | v1_xboole_0(sK26(u1_struct_0(sK0)))
    | v1_subset_1(sK26(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f286])).

fof(f6265,plain,
    ( spl31_868
    | spl31_870
    | ~ spl31_873
    | spl31_89
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f6246,f5208,f650,f6263,f6257,f6251])).

fof(f6257,plain,
    ( spl31_870
  <=> v1_xboole_0(sK25(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_870])])).

fof(f6246,plain,
    ( ~ v1_zfmisc_1(sK25(u1_struct_0(sK0)))
    | v1_xboole_0(sK25(u1_struct_0(sK0)))
    | v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl31_89
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f6215,f651])).

fof(f6215,plain,
    ( ~ v1_zfmisc_1(sK25(u1_struct_0(sK0)))
    | v1_xboole_0(sK25(u1_struct_0(sK0)))
    | v1_subset_1(sK25(u1_struct_0(sK0)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f283])).

fof(f6245,plain,
    ( spl31_862
    | spl31_864
    | ~ spl31_867
    | ~ spl31_68
    | spl31_101
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f6226,f5208,f726,f562,f6243,f6237,f6231])).

fof(f6226,plain,
    ( ~ v1_zfmisc_1(sK15(sK0))
    | v1_xboole_0(sK15(sK0))
    | v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f6225,f727])).

fof(f6225,plain,
    ( ~ v1_zfmisc_1(sK15(sK0))
    | v1_xboole_0(sK15(sK0))
    | v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_742 ),
    inference(subsumption_resolution,[],[f6201,f563])).

fof(f6201,plain,
    ( ~ v1_zfmisc_1(sK15(sK0))
    | v1_xboole_0(sK15(sK0))
    | v1_subset_1(sK15(sK0),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f243])).

fof(f6223,plain,
    ( spl31_738
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_742 ),
    inference(avatar_split_clause,[],[f6197,f5208,f1423,f324,f5182])).

fof(f6197,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(sK4(sK1,X0))
        | v1_xboole_0(sK4(sK1,X0))
        | v1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_742 ),
    inference(resolution,[],[f5209,f1975])).

fof(f6063,plain,
    ( ~ spl31_851
    | spl31_860
    | ~ spl31_0
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f6062,f4577,f317,f6059,f6029])).

fof(f6029,plain,
    ( spl31_851
  <=> ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_851])])).

fof(f6059,plain,
    ( spl31_860
  <=> v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_860])])).

fof(f6062,plain,
    ( v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_672 ),
    inference(subsumption_resolution,[],[f6002,f318])).

fof(f6002,plain,
    ( v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f1216])).

fof(f1216,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X9,u1_struct_0(X8))
      | v2_tex_2(X9,X8)
      | ~ v3_tex_2(X9,X8)
      | ~ l1_pre_topc(X8) ) ),
    inference(resolution,[],[f203,f224])).

fof(f6061,plain,
    ( ~ spl31_845
    | spl31_860
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f5999,f4577,f1906,f1423,f324,f317,f6059,f6007])).

fof(f6007,plain,
    ( spl31_845
  <=> ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_845])])).

fof(f5999,plain,
    ( v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f3832])).

fof(f3832,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v2_tex_2(X2,sK0)
        | ~ v2_tex_2(X2,sK1) )
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f3813,f224])).

fof(f6054,plain,
    ( ~ spl31_847
    | spl31_858
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f5998,f4577,f1423,f324,f6052,f6016])).

fof(f6016,plain,
    ( spl31_847
  <=> ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_847])])).

fof(f6052,plain,
    ( spl31_858
  <=> ! [X0] :
        ( ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_858])])).

fof(f5998,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f3549])).

fof(f3549,plain,
    ( ! [X19,X20] :
        ( ~ r1_tarski(X20,u1_struct_0(sK0))
        | ~ r1_tarski(X20,X19)
        | X19 = X20
        | ~ v3_tex_2(X20,sK1)
        | ~ v2_tex_2(X19,sK1)
        | ~ r1_tarski(X19,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3529,f224])).

fof(f6050,plain,
    ( ~ spl31_855
    | spl31_856
    | ~ spl31_845
    | spl31_846
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f5997,f4577,f1423,f324,f6013,f6007,f6048,f6042])).

fof(f6042,plain,
    ( spl31_855
  <=> ~ v1_xboole_0(sK4(sK1,sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_855])])).

fof(f6013,plain,
    ( spl31_846
  <=> v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_846])])).

fof(f5997,plain,
    ( v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v1_xboole_0(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_xboole_0(sK4(sK1,sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f3272])).

fof(f3272,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | v3_tex_2(X2,sK1)
        | ~ v2_tex_2(X2,sK1)
        | v1_xboole_0(X2)
        | ~ v1_xboole_0(sK4(sK1,X2)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3267,f638])).

fof(f638,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | v1_xboole_0(X4)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f218,f224])).

fof(f6037,plain,
    ( ~ spl31_849
    | ~ spl31_851
    | spl31_852
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f5996,f4577,f1225,f331,f317,f6035,f6029,f6023])).

fof(f6023,plain,
    ( spl31_849
  <=> ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_849])])).

fof(f6035,plain,
    ( spl31_852
  <=> sK3 = sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_852])])).

fof(f5996,plain,
    ( sK3 = sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f2097])).

fof(f2097,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | sK3 = X1
        | ~ v3_tex_2(X1,sK0)
        | ~ r1_tarski(X1,sK3) )
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f224])).

fof(f6018,plain,
    ( spl31_844
    | ~ spl31_847
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(avatar_split_clause,[],[f5995,f4577,f1423,f324,f6016,f6010])).

fof(f6010,plain,
    ( spl31_844
  <=> v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_844])])).

fof(f5995,plain,
    ( ~ v3_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_672 ),
    inference(resolution,[],[f4578,f1715])).

fof(f1715,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v3_tex_2(X0,sK1)
        | v2_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f224])).

fof(f5994,plain,
    ( ~ spl31_841
    | spl31_842
    | spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f5984,f1574,f828,f811,f5992,f5989])).

fof(f5989,plain,
    ( spl31_841
  <=> ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_841])])).

fof(f5992,plain,
    ( spl31_842
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ r1_tarski(X2,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_842])])).

fof(f5984,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5983,f829])).

fof(f5983,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5971,f812])).

fof(f5971,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f2549,f1575])).

fof(f2549,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(sK16(X0),X0)
      | ~ r1_tarski(X1,sK16(X0))
      | sK16(X0) = X1
      | ~ v3_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f2535,f223])).

fof(f2535,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(sK16(X0),X0)
      | ~ r1_tarski(X1,sK16(X0))
      | sK16(X0) = X1
      | ~ v3_tex_2(X1,X0) ) ),
    inference(resolution,[],[f246,f202])).

fof(f5943,plain,
    ( ~ spl31_837
    | spl31_838
    | spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f5933,f1574,f828,f811,f5941,f5938])).

fof(f5938,plain,
    ( spl31_837
  <=> ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_837])])).

fof(f5941,plain,
    ( spl31_838
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ r1_tarski(X2,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_838])])).

fof(f5933,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5932,f829])).

fof(f5932,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_107
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5920,f812])).

fof(f5920,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f2288,f1575])).

fof(f2288,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(sK15(X0),X0)
      | ~ r1_tarski(X1,sK15(X0))
      | sK15(X0) = X1
      | ~ v3_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f2274,f223])).

fof(f2274,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(sK15(X0),X0)
      | ~ r1_tarski(X1,sK15(X0))
      | sK15(X0) = X1
      | ~ v3_tex_2(X1,X0) ) ),
    inference(resolution,[],[f243,f202])).

fof(f5892,plain,
    ( ~ spl31_825
    | spl31_834
    | ~ spl31_0
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5891,f4569,f317,f5888,f5858])).

fof(f5858,plain,
    ( spl31_825
  <=> ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_825])])).

fof(f5888,plain,
    ( spl31_834
  <=> v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_834])])).

fof(f5891,plain,
    ( v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_670 ),
    inference(subsumption_resolution,[],[f5831,f318])).

fof(f5831,plain,
    ( v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f1216])).

fof(f5890,plain,
    ( ~ spl31_819
    | spl31_834
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5828,f4569,f1906,f1423,f324,f317,f5888,f5836])).

fof(f5836,plain,
    ( spl31_819
  <=> ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_819])])).

fof(f5828,plain,
    ( v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f3832])).

fof(f5883,plain,
    ( ~ spl31_821
    | spl31_832
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5827,f4569,f1423,f324,f5881,f5845])).

fof(f5845,plain,
    ( spl31_821
  <=> ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_821])])).

fof(f5881,plain,
    ( spl31_832
  <=> ! [X0] :
        ( ~ r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_832])])).

fof(f5827,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f3549])).

fof(f5879,plain,
    ( ~ spl31_829
    | spl31_830
    | ~ spl31_819
    | spl31_820
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5826,f4569,f1423,f324,f5842,f5836,f5877,f5871])).

fof(f5871,plain,
    ( spl31_829
  <=> ~ v1_xboole_0(sK4(sK1,sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_829])])).

fof(f5842,plain,
    ( spl31_820
  <=> v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_820])])).

fof(f5826,plain,
    ( v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v1_xboole_0(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_xboole_0(sK4(sK1,sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f3272])).

fof(f5866,plain,
    ( ~ spl31_823
    | ~ spl31_825
    | spl31_826
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5825,f4569,f1225,f331,f317,f5864,f5858,f5852])).

fof(f5852,plain,
    ( spl31_823
  <=> ~ r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_823])])).

fof(f5864,plain,
    ( spl31_826
  <=> sK3 = sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_826])])).

fof(f5825,plain,
    ( sK3 = sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f2097])).

fof(f5847,plain,
    ( spl31_818
    | ~ spl31_821
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(avatar_split_clause,[],[f5824,f4569,f1423,f324,f5845,f5839])).

fof(f5839,plain,
    ( spl31_818
  <=> v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_818])])).

fof(f5824,plain,
    ( ~ v3_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_670 ),
    inference(resolution,[],[f4570,f1715])).

fof(f5748,plain,
    ( spl31_814
    | spl31_816
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f5741,f1906,f1574,f1423,f324,f5746,f5743])).

fof(f5743,plain,
    ( spl31_814
  <=> ! [X13] : g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_814])])).

fof(f5741,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13))))
        | ~ v2_tex_2(X14,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X14,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(duplicate_literal_removal,[],[f5740])).

fof(f5740,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13))))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X14,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X14,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f5739,f1575])).

fof(f5739,plain,
    ( ! [X14,X13] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13))))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_tex_2(X14,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tex_2(X14,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(inner_rewriting,[],[f5738])).

fof(f5738,plain,
    ( ! [X14,X13] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13))))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))))))
        | ~ v2_tex_2(X14,g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))))
        | v2_tex_2(X14,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f5716,f750])).

fof(f750,plain,(
    ! [X6] : l1_pre_topc(g1_pre_topc(X6,sK5(k1_zfmisc_1(k1_zfmisc_1(X6))))) ),
    inference(resolution,[],[f210,f215])).

fof(f5716,plain,
    ( ! [X14,X13] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13))))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))))))
        | ~ l1_pre_topc(g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))))
        | ~ v2_tex_2(X14,g1_pre_topc(X13,sK5(k1_zfmisc_1(k1_zfmisc_1(X13)))))
        | v2_tex_2(X14,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(superposition,[],[f3640,f1084])).

fof(f1084,plain,(
    ! [X0] : g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0))))),u1_pre_topc(g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ),
    inference(subsumption_resolution,[],[f1070,f750])).

fof(f1070,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0))))),u1_pre_topc(g1_pre_topc(X0,sK5(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ) ),
    inference(resolution,[],[f213,f713])).

fof(f713,plain,(
    ! [X5] : v1_pre_topc(g1_pre_topc(X5,sK5(k1_zfmisc_1(k1_zfmisc_1(X5))))) ),
    inference(resolution,[],[f209,f215])).

fof(f5707,plain,
    ( spl31_724
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5595,f4718,f4990])).

fof(f5595,plain,
    ( r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f225])).

fof(f5706,plain,
    ( ~ spl31_702
    | spl31_725 ),
    inference(avatar_contradiction_clause,[],[f5705])).

fof(f5705,plain,
    ( $false
    | ~ spl31_702
    | ~ spl31_725 ),
    inference(subsumption_resolution,[],[f5595,f4994])).

fof(f4994,plain,
    ( ~ r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_725 ),
    inference(avatar_component_clause,[],[f4993])).

fof(f5704,plain,
    ( ~ spl31_811
    | spl31_812
    | ~ spl31_68
    | spl31_121
    | spl31_669
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5691,f4718,f4561,f886,f562,f5702,f5696])).

fof(f5691,plain,
    ( v1_xboole_0(sK22(sK1))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_669
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5690,f4562])).

fof(f5690,plain,
    ( v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_121
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5689,f887])).

fof(f5689,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_68
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5592,f563])).

fof(f5592,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK22(sK1))
    | v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK22(sK1))
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f5048])).

fof(f5688,plain,
    ( ~ spl31_791
    | spl31_800
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5687,f4718,f317,f5655,f5628])).

fof(f5628,plain,
    ( spl31_791
  <=> ~ v3_tex_2(sK22(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_791])])).

fof(f5655,plain,
    ( spl31_800
  <=> v2_tex_2(sK22(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_800])])).

fof(f5687,plain,
    ( v2_tex_2(sK22(sK1),sK0)
    | ~ v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5587,f318])).

fof(f5587,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK22(sK1),sK0)
    | ~ v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f203])).

fof(f5686,plain,
    ( ~ spl31_801
    | spl31_808
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5682,f4718,f317,f5684,f5652])).

fof(f5652,plain,
    ( spl31_801
  <=> ~ v2_tex_2(sK22(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_801])])).

fof(f5684,plain,
    ( spl31_808
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X2,sK0)
        | sK22(sK1) = X2
        | ~ r1_tarski(X2,sK22(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_808])])).

fof(f5682,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK22(sK1),sK0)
        | ~ r1_tarski(X2,sK22(sK1))
        | sK22(sK1) = X2
        | ~ v3_tex_2(X2,sK0) )
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5586,f318])).

fof(f5586,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK22(sK1),sK0)
        | ~ r1_tarski(X2,sK22(sK1))
        | sK22(sK1) = X2
        | ~ v3_tex_2(X2,sK0) )
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f202])).

fof(f5681,plain,
    ( spl31_790
    | spl31_806
    | ~ spl31_801
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5674,f4718,f317,f5652,f5679,f5625])).

fof(f5625,plain,
    ( spl31_790
  <=> v3_tex_2(sK22(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_790])])).

fof(f5679,plain,
    ( spl31_806
  <=> r1_tarski(sK22(sK1),sK4(sK0,sK22(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_806])])).

fof(f5674,plain,
    ( ~ v2_tex_2(sK22(sK1),sK0)
    | r1_tarski(sK22(sK1),sK4(sK0,sK22(sK1)))
    | v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5585,f318])).

fof(f5585,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK22(sK1),sK0)
    | r1_tarski(sK22(sK1),sK4(sK0,sK22(sK1)))
    | v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f200])).

fof(f5673,plain,
    ( spl31_790
    | spl31_804
    | ~ spl31_801
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5666,f4718,f317,f5652,f5671,f5625])).

fof(f5671,plain,
    ( spl31_804
  <=> v2_tex_2(sK4(sK0,sK22(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_804])])).

fof(f5666,plain,
    ( ~ v2_tex_2(sK22(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK22(sK1)),sK0)
    | v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_702 ),
    inference(subsumption_resolution,[],[f5584,f318])).

fof(f5584,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK22(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK22(sK1)),sK0)
    | v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f199])).

fof(f5665,plain,
    ( spl31_784
    | ~ spl31_801
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5583,f4718,f1906,f1423,f324,f317,f5652,f5607])).

fof(f5607,plain,
    ( spl31_784
  <=> v2_tex_2(sK22(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_784])])).

fof(f5583,plain,
    ( ~ v2_tex_2(sK22(sK1),sK0)
    | v2_tex_2(sK22(sK1),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f4164])).

fof(f5664,plain,
    ( spl31_782
    | ~ spl31_785
    | spl31_802
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5582,f4718,f1906,f1423,f324,f317,f5662,f5604,f5598])).

fof(f5598,plain,
    ( spl31_782
  <=> v3_tex_2(sK22(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_782])])).

fof(f5604,plain,
    ( spl31_785
  <=> ~ v2_tex_2(sK22(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_785])])).

fof(f5662,plain,
    ( spl31_802
  <=> v2_tex_2(sK4(sK1,sK22(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_802])])).

fof(f5582,plain,
    ( v2_tex_2(sK4(sK1,sK22(sK1)),sK0)
    | ~ v2_tex_2(sK22(sK1),sK1)
    | v3_tex_2(sK22(sK1),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f3834])).

fof(f5657,plain,
    ( spl31_800
    | ~ spl31_785
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5581,f4718,f1906,f1423,f324,f317,f5604,f5655])).

fof(f5581,plain,
    ( ~ v2_tex_2(sK22(sK1),sK1)
    | v2_tex_2(sK22(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f3813])).

fof(f5650,plain,
    ( spl31_798
    | ~ spl31_785
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5580,f4718,f1423,f324,f5604,f5648])).

fof(f5648,plain,
    ( spl31_798
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK22(sK1))
        | ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v3_tex_2(X1,sK1)
        | sK22(sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_798])])).

fof(f5580,plain,
    ( ! [X1] :
        ( ~ v2_tex_2(sK22(sK1),sK1)
        | ~ r1_tarski(X1,sK22(sK1))
        | sK22(sK1) = X1
        | ~ v3_tex_2(X1,sK1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f3529])).

fof(f5646,plain,
    ( ~ spl31_783
    | spl31_796
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5579,f4718,f1423,f324,f5644,f5601])).

fof(f5601,plain,
    ( spl31_783
  <=> ~ v3_tex_2(sK22(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_783])])).

fof(f5644,plain,
    ( spl31_796
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK22(sK1) = X0
        | ~ r1_tarski(sK22(sK1),X0)
        | ~ v2_tex_2(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_796])])).

fof(f5579,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(sK22(sK1),X0)
        | sK22(sK1) = X0
        | ~ v3_tex_2(sK22(sK1),sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f2084])).

fof(f5642,plain,
    ( ~ spl31_791
    | spl31_792
    | ~ spl31_795
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5578,f4718,f1225,f331,f317,f5640,f5634,f5628])).

fof(f5634,plain,
    ( spl31_792
  <=> sK3 = sK22(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_792])])).

fof(f5640,plain,
    ( spl31_795
  <=> ~ r1_tarski(sK22(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_795])])).

fof(f5578,plain,
    ( ~ r1_tarski(sK22(sK1),sK3)
    | sK3 = sK22(sK1)
    | ~ v3_tex_2(sK22(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f2079])).

fof(f5623,plain,
    ( spl31_782
    | spl31_788
    | ~ spl31_785
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5577,f4718,f1423,f324,f5604,f5621,f5598])).

fof(f5621,plain,
    ( spl31_788
  <=> r1_tarski(sK22(sK1),sK4(sK1,sK22(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_788])])).

fof(f5577,plain,
    ( ~ v2_tex_2(sK22(sK1),sK1)
    | r1_tarski(sK22(sK1),sK4(sK1,sK22(sK1)))
    | v3_tex_2(sK22(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f1872])).

fof(f5616,plain,
    ( spl31_782
    | spl31_786
    | ~ spl31_785
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5576,f4718,f1423,f324,f5604,f5614,f5598])).

fof(f5614,plain,
    ( spl31_786
  <=> v2_tex_2(sK4(sK1,sK22(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_786])])).

fof(f5576,plain,
    ( ~ v2_tex_2(sK22(sK1),sK1)
    | v2_tex_2(sK4(sK1,sK22(sK1)),sK1)
    | v3_tex_2(sK22(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f1855])).

fof(f5609,plain,
    ( ~ spl31_783
    | spl31_784
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(avatar_split_clause,[],[f5575,f4718,f1423,f324,f5607,f5601])).

fof(f5575,plain,
    ( v2_tex_2(sK22(sK1),sK1)
    | ~ v3_tex_2(sK22(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_702 ),
    inference(resolution,[],[f4719,f1476])).

fof(f5568,plain,
    ( spl31_780
    | ~ spl31_14 ),
    inference(avatar_split_clause,[],[f5548,f366,f5566])).

fof(f5548,plain,
    ( g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK8),u1_pre_topc(sK8))))
    | ~ spl31_14 ),
    inference(resolution,[],[f1091,f367])).

fof(f1091,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),u1_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))) ) ),
    inference(subsumption_resolution,[],[f1077,f773])).

fof(f1077,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))
      | g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))),u1_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7))))
      | ~ l1_pre_topc(X7) ) ),
    inference(resolution,[],[f213,f774])).

fof(f5454,plain,
    ( ~ spl31_769
    | spl31_778
    | ~ spl31_0
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5453,f4537,f317,f5450,f5420])).

fof(f5420,plain,
    ( spl31_769
  <=> ~ v3_tex_2(sK20(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_769])])).

fof(f5450,plain,
    ( spl31_778
  <=> v2_tex_2(sK20(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_778])])).

fof(f5453,plain,
    ( v2_tex_2(sK20(sK1),sK0)
    | ~ v3_tex_2(sK20(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_662 ),
    inference(subsumption_resolution,[],[f5393,f318])).

fof(f5393,plain,
    ( v2_tex_2(sK20(sK1),sK0)
    | ~ v3_tex_2(sK20(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f1216])).

fof(f5452,plain,
    ( ~ spl31_763
    | spl31_778
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5391,f4537,f1906,f1423,f324,f317,f5450,f5398])).

fof(f5398,plain,
    ( spl31_763
  <=> ~ v2_tex_2(sK20(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_763])])).

fof(f5391,plain,
    ( v2_tex_2(sK20(sK1),sK0)
    | ~ v2_tex_2(sK20(sK1),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f3832])).

fof(f5445,plain,
    ( ~ spl31_765
    | spl31_776
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5390,f4537,f1423,f324,f5443,f5407])).

fof(f5407,plain,
    ( spl31_765
  <=> ~ v3_tex_2(sK20(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_765])])).

fof(f5443,plain,
    ( spl31_776
  <=> ! [X0] :
        ( ~ r1_tarski(sK20(sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK20(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_776])])).

fof(f5390,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK20(sK1),X0)
        | sK20(sK1) = X0
        | ~ v3_tex_2(sK20(sK1),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f3549])).

fof(f5441,plain,
    ( ~ spl31_773
    | spl31_774
    | ~ spl31_763
    | spl31_764
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5389,f4537,f1423,f324,f5404,f5398,f5439,f5433])).

fof(f5433,plain,
    ( spl31_773
  <=> ~ v1_xboole_0(sK4(sK1,sK20(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_773])])).

fof(f5404,plain,
    ( spl31_764
  <=> v3_tex_2(sK20(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_764])])).

fof(f5389,plain,
    ( v3_tex_2(sK20(sK1),sK1)
    | ~ v2_tex_2(sK20(sK1),sK1)
    | v1_xboole_0(sK20(sK1))
    | ~ v1_xboole_0(sK4(sK1,sK20(sK1)))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f3272])).

fof(f5428,plain,
    ( ~ spl31_767
    | ~ spl31_769
    | spl31_770
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5388,f4537,f1225,f331,f317,f5426,f5420,f5414])).

fof(f5414,plain,
    ( spl31_767
  <=> ~ r1_tarski(sK20(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_767])])).

fof(f5426,plain,
    ( spl31_770
  <=> sK3 = sK20(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_770])])).

fof(f5388,plain,
    ( sK3 = sK20(sK1)
    | ~ v3_tex_2(sK20(sK1),sK0)
    | ~ r1_tarski(sK20(sK1),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f2097])).

fof(f5409,plain,
    ( spl31_762
    | ~ spl31_765
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(avatar_split_clause,[],[f5387,f4537,f1423,f324,f5407,f5401])).

fof(f5401,plain,
    ( spl31_762
  <=> v2_tex_2(sK20(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_762])])).

fof(f5387,plain,
    ( ~ v3_tex_2(sK20(sK1),sK1)
    | v2_tex_2(sK20(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_662 ),
    inference(resolution,[],[f4538,f1715])).

fof(f5372,plain,
    ( ~ spl31_751
    | spl31_760
    | ~ spl31_0
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5371,f4529,f317,f5368,f5338])).

fof(f5338,plain,
    ( spl31_751
  <=> ~ v3_tex_2(sK21(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_751])])).

fof(f5368,plain,
    ( spl31_760
  <=> v2_tex_2(sK21(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_760])])).

fof(f5371,plain,
    ( v2_tex_2(sK21(sK1),sK0)
    | ~ v3_tex_2(sK21(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_660 ),
    inference(subsumption_resolution,[],[f5311,f318])).

fof(f5311,plain,
    ( v2_tex_2(sK21(sK1),sK0)
    | ~ v3_tex_2(sK21(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f1216])).

fof(f5370,plain,
    ( ~ spl31_745
    | spl31_760
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5309,f4529,f1906,f1423,f324,f317,f5368,f5316])).

fof(f5316,plain,
    ( spl31_745
  <=> ~ v2_tex_2(sK21(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_745])])).

fof(f5309,plain,
    ( v2_tex_2(sK21(sK1),sK0)
    | ~ v2_tex_2(sK21(sK1),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f3832])).

fof(f5363,plain,
    ( ~ spl31_747
    | spl31_758
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5308,f4529,f1423,f324,f5361,f5325])).

fof(f5325,plain,
    ( spl31_747
  <=> ~ v3_tex_2(sK21(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_747])])).

fof(f5361,plain,
    ( spl31_758
  <=> ! [X0] :
        ( ~ r1_tarski(sK21(sK1),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK21(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_758])])).

fof(f5308,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK21(sK1),X0)
        | sK21(sK1) = X0
        | ~ v3_tex_2(sK21(sK1),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f3549])).

fof(f5359,plain,
    ( ~ spl31_755
    | spl31_756
    | ~ spl31_745
    | spl31_746
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5307,f4529,f1423,f324,f5322,f5316,f5357,f5351])).

fof(f5351,plain,
    ( spl31_755
  <=> ~ v1_xboole_0(sK4(sK1,sK21(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_755])])).

fof(f5322,plain,
    ( spl31_746
  <=> v3_tex_2(sK21(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_746])])).

fof(f5307,plain,
    ( v3_tex_2(sK21(sK1),sK1)
    | ~ v2_tex_2(sK21(sK1),sK1)
    | v1_xboole_0(sK21(sK1))
    | ~ v1_xboole_0(sK4(sK1,sK21(sK1)))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f3272])).

fof(f5346,plain,
    ( ~ spl31_749
    | ~ spl31_751
    | spl31_752
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5306,f4529,f1225,f331,f317,f5344,f5338,f5332])).

fof(f5332,plain,
    ( spl31_749
  <=> ~ r1_tarski(sK21(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_749])])).

fof(f5344,plain,
    ( spl31_752
  <=> sK3 = sK21(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_752])])).

fof(f5306,plain,
    ( sK3 = sK21(sK1)
    | ~ v3_tex_2(sK21(sK1),sK0)
    | ~ r1_tarski(sK21(sK1),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f2097])).

fof(f5327,plain,
    ( spl31_744
    | ~ spl31_747
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(avatar_split_clause,[],[f5305,f4529,f1423,f324,f5325,f5319])).

fof(f5319,plain,
    ( spl31_744
  <=> v2_tex_2(sK21(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_744])])).

fof(f5305,plain,
    ( ~ v3_tex_2(sK21(sK1),sK1)
    | v2_tex_2(sK21(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_660 ),
    inference(resolution,[],[f4530,f1715])).

fof(f5242,plain,
    ( spl31_706
    | spl31_120
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_428
    | spl31_709 ),
    inference(avatar_split_clause,[],[f5241,f4853,f2734,f2343,f562,f883,f4847])).

fof(f5241,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_428
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f5176,f2735])).

fof(f5176,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f5175,f4854])).

fof(f5175,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_68
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f5056,f563])).

fof(f5056,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_362 ),
    inference(resolution,[],[f5048,f2344])).

fof(f5240,plain,
    ( ~ spl31_707
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_362
    | spl31_709 ),
    inference(avatar_split_clause,[],[f5239,f4853,f2343,f726,f562,f886,f4850])).

fof(f5239,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_362
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f5238,f4854])).

fof(f5238,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f5237,f727])).

fof(f5237,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f4812,f563])).

fof(f4812,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362 ),
    inference(resolution,[],[f258,f2344])).

fof(f5236,plain,
    ( spl31_566
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f5235,f2604,f726,f562,f886,f3916])).

fof(f5235,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK16(sK1))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f5234,f727])).

fof(f5234,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK16(sK1))
    | ~ spl31_68
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f5003,f563])).

fof(f5003,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK16(sK1))
    | ~ spl31_400 ),
    inference(resolution,[],[f4985,f2605])).

fof(f5233,plain,
    ( ~ spl31_567
    | spl31_120
    | ~ spl31_68
    | ~ spl31_400
    | spl31_715
    | spl31_717 ),
    inference(avatar_split_clause,[],[f5169,f4886,f4883,f2604,f562,f883,f3913])).

fof(f3913,plain,
    ( spl31_567
  <=> ~ v1_zfmisc_1(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_567])])).

fof(f5169,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK16(sK1))
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_715
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f5168,f4884])).

fof(f4884,plain,
    ( ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_715 ),
    inference(avatar_component_clause,[],[f4883])).

fof(f5232,plain,
    ( spl31_562
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f5231,f2613,f726,f562,f886,f3900])).

fof(f5231,plain,
    ( ~ v7_struct_0(sK0)
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f5230,f727])).

fof(f5230,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f5004,f563])).

fof(f5004,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f4985,f2614])).

fof(f5229,plain,
    ( ~ spl31_563
    | spl31_718
    | spl31_720
    | spl31_120
    | ~ spl31_68
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f5164,f2613,f562,f883,f4905,f4896,f3897])).

fof(f3897,plain,
    ( spl31_563
  <=> ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_563])])).

fof(f5164,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f5060,f563])).

fof(f5060,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f5048,f2614])).

fof(f5228,plain,
    ( ~ spl31_367
    | ~ spl31_121
    | ~ spl31_4
    | ~ spl31_68
    | spl31_87
    | spl31_101 ),
    inference(avatar_split_clause,[],[f5227,f726,f641,f562,f331,f886,f2365])).

fof(f5227,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_87
    | ~ spl31_101 ),
    inference(subsumption_resolution,[],[f5226,f642])).

fof(f5226,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_101 ),
    inference(subsumption_resolution,[],[f5225,f727])).

fof(f5225,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_68 ),
    inference(subsumption_resolution,[],[f4808,f563])).

fof(f4808,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK3)
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4 ),
    inference(resolution,[],[f258,f332])).

fof(f5224,plain,
    ( spl31_366
    | spl31_120
    | ~ spl31_4
    | ~ spl31_68
    | spl31_87
    | ~ spl31_114 ),
    inference(avatar_split_clause,[],[f5223,f863,f641,f562,f331,f883,f2362])).

fof(f5223,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_87
    | ~ spl31_114 ),
    inference(subsumption_resolution,[],[f5186,f864])).

fof(f5186,plain,
    ( v7_struct_0(sK0)
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_87 ),
    inference(subsumption_resolution,[],[f5185,f642])).

fof(f5185,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK3)
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4
    | ~ spl31_68 ),
    inference(subsumption_resolution,[],[f5052,f563])).

fof(f5052,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK3)
    | v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4 ),
    inference(resolution,[],[f5048,f332])).

fof(f5222,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5221,f1423,f876,f869])).

fof(f5221,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f5220,plain,
    ( spl31_236
    | spl31_742
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f5219,f1574,f836,f5208,f1650])).

fof(f5219,plain,
    ( ! [X2] :
        ( v1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_zfmisc_1(X2) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f5218,f1575])).

fof(f5218,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_zfmisc_1(X2) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5076,f837])).

fof(f5076,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | ~ v1_zfmisc_1(X2) )
    | ~ spl31_220 ),
    inference(superposition,[],[f5048,f1575])).

fof(f5217,plain,
    ( ~ spl31_123
    | spl31_722
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5216,f1423,f734,f569,f4924,f896])).

fof(f5216,plain,
    ( ! [X1] :
        ( ~ v1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v1_xboole_0(X1) )
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f5215,f1424])).

fof(f5215,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5214,f735])).

fof(f5214,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4831,f570])).

fof(f4831,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl31_194 ),
    inference(superposition,[],[f258,f1424])).

fof(f5213,plain,
    ( ~ spl31_123
    | spl31_726
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5212,f1423,f734,f569,f5039,f896])).

fof(f5212,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5211,f735])).

fof(f5211,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5019,f570])).

fof(f5019,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f4985,f1424])).

fof(f5210,plain,
    ( spl31_122
    | spl31_742
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5206,f1423,f569,f5208,f893])).

fof(f5206,plain,
    ( ! [X1] :
        ( v1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f5205,f1424])).

fof(f5205,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v7_struct_0(sK1)
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5075,f570])).

fof(f5075,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK1)
        | v7_struct_0(sK1)
        | v1_xboole_0(X1)
        | v1_subset_1(X1,u1_struct_0(sK1))
        | ~ v1_zfmisc_1(X1) )
    | ~ spl31_194 ),
    inference(superposition,[],[f5048,f1424])).

fof(f5204,plain,
    ( spl31_740
    | ~ spl31_121
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5200,f1423,f726,f562,f324,f886,f5202])).

fof(f5200,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X2))
        | ~ v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5199,f727])).

fof(f5199,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X2))
        | ~ v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4810,f563])).

fof(f4810,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X2))
        | ~ v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f258,f1975])).

fof(f5198,plain,
    ( ~ spl31_711
    | spl31_712
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f5197,f2352,f726,f562,f886,f4872,f4866])).

fof(f5197,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f5196,f727])).

fof(f5196,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f4813,f563])).

fof(f4813,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364 ),
    inference(resolution,[],[f258,f2353])).

fof(f5195,plain,
    ( ~ spl31_719
    | spl31_720
    | ~ spl31_121
    | ~ spl31_68
    | spl31_101
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f5194,f2613,f726,f562,f886,f4905,f4899])).

fof(f5194,plain,
    ( ~ v7_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f5193,f727])).

fof(f5193,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f4816,f563])).

fof(f4816,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_402 ),
    inference(resolution,[],[f258,f2614])).

fof(f5192,plain,
    ( spl31_560
    | ~ spl31_121
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5191,f1423,f726,f562,f324,f886,f3892])).

fof(f5191,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5190,f727])).

fof(f5190,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4998,f563])).

fof(f4998,plain,
    ( ! [X2] :
        ( ~ v7_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4985,f1975])).

fof(f5189,plain,
    ( spl31_120
    | ~ spl31_4
    | ~ spl31_68
    | spl31_87
    | ~ spl31_114
    | spl31_367 ),
    inference(avatar_split_clause,[],[f5188,f2365,f863,f641,f562,f331,f883])).

fof(f5188,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_87
    | ~ spl31_114
    | ~ spl31_367 ),
    inference(subsumption_resolution,[],[f5187,f864])).

fof(f5187,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK3)
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_87
    | ~ spl31_367 ),
    inference(subsumption_resolution,[],[f5186,f2366])).

fof(f2366,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_367 ),
    inference(avatar_component_clause,[],[f2365])).

fof(f5184,plain,
    ( spl31_738
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5180,f1423,f562,f324,f883,f5182])).

fof(f5180,plain,
    ( ! [X2] :
        ( v7_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X2))
        | v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5054,f563])).

fof(f5054,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | v1_xboole_0(sK4(sK1,X2))
        | v1_subset_1(sK4(sK1,X2),u1_struct_0(sK0))
        | ~ v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f5048,f1975])).

fof(f5179,plain,
    ( spl31_120
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_428
    | spl31_707
    | spl31_709 ),
    inference(avatar_split_clause,[],[f5178,f4853,f4850,f2734,f2343,f562,f883])).

fof(f5178,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_428
    | ~ spl31_707
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f5177,f2735])).

fof(f5177,plain,
    ( v7_struct_0(sK0)
    | ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_68
    | ~ spl31_362
    | ~ spl31_707
    | ~ spl31_709 ),
    inference(subsumption_resolution,[],[f5176,f4851])).

fof(f4851,plain,
    ( ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_707 ),
    inference(avatar_component_clause,[],[f4850])).

fof(f5174,plain,
    ( spl31_710
    | spl31_712
    | spl31_120
    | ~ spl31_68
    | ~ spl31_364
    | ~ spl31_564 ),
    inference(avatar_split_clause,[],[f5173,f3908,f2352,f562,f883,f4872,f4863])).

fof(f5173,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_364
    | ~ spl31_564 ),
    inference(subsumption_resolution,[],[f5172,f3909])).

fof(f5172,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_68
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f5057,f563])).

fof(f5057,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364 ),
    inference(resolution,[],[f5048,f2353])).

fof(f5171,plain,
    ( spl31_120
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_566
    | spl31_715
    | spl31_717 ),
    inference(avatar_split_clause,[],[f5170,f4886,f4883,f3916,f2604,f562,f883])).

fof(f5170,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_400
    | ~ spl31_566
    | ~ spl31_715
    | ~ spl31_717 ),
    inference(subsumption_resolution,[],[f5169,f3917])).

fof(f5166,plain,
    ( spl31_718
    | spl31_720
    | spl31_120
    | ~ spl31_68
    | ~ spl31_402
    | ~ spl31_562 ),
    inference(avatar_split_clause,[],[f5165,f3900,f2613,f562,f883,f4905,f4896])).

fof(f5165,plain,
    ( v7_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_402
    | ~ spl31_562 ),
    inference(subsumption_resolution,[],[f5164,f3901])).

fof(f5163,plain,
    ( spl31_736
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5122,f5039,f5161])).

fof(f5122,plain,
    ( v1_zfmisc_1(sK5(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f215])).

fof(f5156,plain,
    ( spl31_734
    | spl31_89
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5149,f5039,f650,f5154])).

fof(f5154,plain,
    ( spl31_734
  <=> v1_zfmisc_1(sK30(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_734])])).

fof(f5149,plain,
    ( v1_zfmisc_1(sK30(u1_struct_0(sK0)))
    | ~ spl31_89
    | ~ spl31_726 ),
    inference(subsumption_resolution,[],[f5120,f651])).

fof(f5120,plain,
    ( v1_zfmisc_1(sK30(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f306])).

fof(f5148,plain,
    ( spl31_732
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5117,f5039,f5146])).

fof(f5117,plain,
    ( v1_zfmisc_1(sK27(u1_struct_0(sK0)))
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f290])).

fof(f5141,plain,
    ( spl31_730
    | spl31_89
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5134,f5039,f650,f5139])).

fof(f5134,plain,
    ( v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | ~ spl31_89
    | ~ spl31_726 ),
    inference(subsumption_resolution,[],[f5113,f651])).

fof(f5113,plain,
    ( v1_zfmisc_1(sK7(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f219])).

fof(f5133,plain,
    ( spl31_728
    | ~ spl31_68
    | spl31_101
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5126,f5039,f726,f562,f5131])).

fof(f5126,plain,
    ( v1_zfmisc_1(sK16(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_726 ),
    inference(subsumption_resolution,[],[f5125,f727])).

fof(f5125,plain,
    ( v1_zfmisc_1(sK16(sK0))
    | v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_726 ),
    inference(subsumption_resolution,[],[f5109,f563])).

fof(f5109,plain,
    ( v1_zfmisc_1(sK16(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f246])).

fof(f5123,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(avatar_split_clause,[],[f5102,f5039,f1423,f324,f3892])).

fof(f5102,plain,
    ( ! [X0] :
        ( v1_zfmisc_1(sK4(sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v3_tex_2(X0,sK1) )
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_726 ),
    inference(resolution,[],[f5040,f1975])).

fof(f5094,plain,
    ( spl31_726
    | ~ spl31_70
    | spl31_103
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5035,f1423,f893,f734,f569,f5039])).

fof(f5035,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5034,f735])).

fof(f5034,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1) )
    | ~ spl31_70
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5033,f570])).

fof(f5033,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK1)
        | v2_struct_0(sK1)
        | v1_zfmisc_1(X1) )
    | ~ spl31_122
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5019,f894])).

fof(f5041,plain,
    ( ~ spl31_237
    | spl31_726
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f5037,f1574,f836,f811,f5039,f1653])).

fof(f5037,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_zfmisc_1(X2) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5036,f812])).

fof(f5036,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_zfmisc_1(X2) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f5020,f837])).

fof(f5020,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_zfmisc_1(X2) )
    | ~ spl31_220 ),
    inference(superposition,[],[f4985,f1575])).

fof(f5030,plain,
    ( spl31_560
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f5029,f1423,f883,f726,f562,f324,f3892])).

fof(f5029,plain,
    ( ! [X2] :
        ( v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5028,f727])).

fof(f5028,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f5027,f563])).

fof(f5027,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK0)
        | v1_zfmisc_1(sK4(sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1) )
    | ~ spl31_2
    | ~ spl31_120
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4998,f884])).

fof(f4995,plain,
    ( ~ spl31_725
    | spl31_703 ),
    inference(avatar_split_clause,[],[f4988,f4715,f4993])).

fof(f4988,plain,
    ( ~ r1_tarski(sK22(sK1),u1_struct_0(sK0))
    | ~ spl31_703 ),
    inference(resolution,[],[f4716,f224])).

fof(f4926,plain,
    ( ~ spl31_237
    | spl31_722
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4922,f1574,f836,f811,f4924,f1653])).

fof(f4922,plain,
    ( ! [X2] :
        ( ~ v1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f4921,f1575])).

fof(f4921,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4920,f812])).

fof(f4920,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4832,f837])).

fof(f4832,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_subset_1(X2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) )
    | ~ spl31_220 ),
    inference(superposition,[],[f258,f1575])).

fof(f4907,plain,
    ( ~ spl31_719
    | spl31_720
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f4894,f2613,f883,f726,f562,f4905,f4899])).

fof(f4894,plain,
    ( v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f4893,f727])).

fof(f4893,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f4892,f563])).

fof(f4892,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f4816,f884])).

fof(f4891,plain,
    ( ~ spl31_715
    | spl31_716
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f4878,f2604,f883,f726,f562,f4889,f4883])).

fof(f4889,plain,
    ( spl31_716
  <=> v1_xboole_0(sK16(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_716])])).

fof(f4878,plain,
    ( v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f4877,f727])).

fof(f4877,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f4876,f563])).

fof(f4876,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK16(sK1))
    | ~ v1_subset_1(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f4815,f884])).

fof(f4874,plain,
    ( ~ spl31_711
    | spl31_712
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f4861,f2352,f883,f726,f562,f4872,f4866])).

fof(f4861,plain,
    ( v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f4860,f727])).

fof(f4860,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f4859,f563])).

fof(f4859,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f4813,f884])).

fof(f4858,plain,
    ( ~ spl31_707
    | spl31_708
    | ~ spl31_68
    | spl31_101
    | ~ spl31_120
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f4845,f2343,f883,f726,f562,f4856,f4850])).

fof(f4856,plain,
    ( spl31_708
  <=> v1_xboole_0(sK15(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_708])])).

fof(f4845,plain,
    ( v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_120
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f4844,f727])).

fof(f4844,plain,
    ( v2_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_68
    | ~ spl31_120
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f4843,f563])).

fof(f4843,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(sK15(sK1))
    | ~ v1_subset_1(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_120
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f4812,f884])).

fof(f4728,plain,
    ( spl31_236
    | spl31_704
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4721,f1574,f836,f4726,f1650])).

fof(f4721,plain,
    ( m1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4629,f837])).

fof(f4629,plain,
    ( m1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4141,f1575])).

fof(f4720,plain,
    ( spl31_122
    | spl31_702
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4713,f1423,f569,f4718,f893])).

fof(f4713,plain,
    ( m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4628,f570])).

fof(f4628,plain,
    ( m1_subset_1(sK22(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4141,f1424])).

fof(f4712,plain,
    ( spl31_682
    | ~ spl31_699
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4711,f1906,f1423,f562,f324,f317,f883,f4697,f4646])).

fof(f4646,plain,
    ( spl31_682
  <=> v2_tex_2(sK22(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_682])])).

fof(f4697,plain,
    ( spl31_699
  <=> ~ v2_tex_2(sK22(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_699])])).

fof(f4711,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK0)
    | v2_tex_2(sK22(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4622,f563])).

fof(f4622,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK0)
    | v2_tex_2(sK22(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4141,f4164])).

fof(f4710,plain,
    ( spl31_680
    | ~ spl31_683
    | spl31_700
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4703,f1906,f1423,f562,f324,f317,f883,f4708,f4643,f4637])).

fof(f4637,plain,
    ( spl31_680
  <=> v3_tex_2(sK22(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_680])])).

fof(f4643,plain,
    ( spl31_683
  <=> ~ v2_tex_2(sK22(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_683])])).

fof(f4708,plain,
    ( spl31_700
  <=> v2_tex_2(sK4(sK1,sK22(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_700])])).

fof(f4703,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK4(sK1,sK22(sK0)),sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4621,f563])).

fof(f4621,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_tex_2(sK4(sK1,sK22(sK0)),sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4141,f3834])).

fof(f4702,plain,
    ( spl31_698
    | ~ spl31_683
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4695,f1906,f1423,f562,f324,f317,f883,f4643,f4700])).

fof(f4700,plain,
    ( spl31_698
  <=> v2_tex_2(sK22(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_698])])).

fof(f4695,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v2_tex_2(sK22(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4620,f563])).

fof(f4620,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v2_tex_2(sK22(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4141,f3813])).

fof(f4694,plain,
    ( spl31_696
    | ~ spl31_683
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4690,f1423,f562,f324,f883,f4643,f4692])).

fof(f4692,plain,
    ( spl31_696
  <=> ! [X8] :
        ( ~ r1_tarski(X8,sK22(sK0))
        | ~ r1_tarski(X8,u1_struct_0(sK0))
        | ~ v3_tex_2(X8,sK1)
        | sK22(sK0) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_696])])).

fof(f4690,plain,
    ( ! [X8] :
        ( v7_struct_0(sK0)
        | ~ v2_tex_2(sK22(sK0),sK1)
        | ~ r1_tarski(X8,sK22(sK0))
        | sK22(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4619,f563])).

fof(f4619,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ v2_tex_2(sK22(sK0),sK1)
        | ~ r1_tarski(X8,sK22(sK0))
        | sK22(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4141,f3529])).

fof(f4689,plain,
    ( ~ spl31_681
    | spl31_694
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4685,f1423,f562,f324,f883,f4687,f4640])).

fof(f4640,plain,
    ( spl31_681
  <=> ~ v3_tex_2(sK22(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_681])])).

fof(f4687,plain,
    ( spl31_694
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK22(sK0) = X7
        | ~ r1_tarski(sK22(sK0),X7)
        | ~ v2_tex_2(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_694])])).

fof(f4685,plain,
    ( ! [X7] :
        ( v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK22(sK0),X7)
        | sK22(sK0) = X7
        | ~ v3_tex_2(sK22(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4618,f563])).

fof(f4618,plain,
    ( ! [X7] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK22(sK0),X7)
        | sK22(sK0) = X7
        | ~ v3_tex_2(sK22(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4141,f2084])).

fof(f4684,plain,
    ( ~ spl31_689
    | spl31_690
    | ~ spl31_693
    | spl31_120
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f4665,f1225,f562,f331,f317,f883,f4682,f4676,f4670])).

fof(f4670,plain,
    ( spl31_689
  <=> ~ v3_tex_2(sK22(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_689])])).

fof(f4676,plain,
    ( spl31_690
  <=> sK3 = sK22(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_690])])).

fof(f4682,plain,
    ( spl31_693
  <=> ~ r1_tarski(sK22(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_693])])).

fof(f4665,plain,
    ( v7_struct_0(sK0)
    | ~ r1_tarski(sK22(sK0),sK3)
    | sK3 = sK22(sK0)
    | ~ v3_tex_2(sK22(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f4617,f563])).

fof(f4617,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ r1_tarski(sK22(sK0),sK3)
    | sK3 = sK22(sK0)
    | ~ v3_tex_2(sK22(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f4141,f2079])).

fof(f4664,plain,
    ( spl31_680
    | spl31_686
    | ~ spl31_683
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4657,f1423,f562,f324,f883,f4643,f4662,f4637])).

fof(f4662,plain,
    ( spl31_686
  <=> r1_tarski(sK22(sK0),sK4(sK1,sK22(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_686])])).

fof(f4657,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | r1_tarski(sK22(sK0),sK4(sK1,sK22(sK0)))
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4616,f563])).

fof(f4616,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | r1_tarski(sK22(sK0),sK4(sK1,sK22(sK0)))
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4141,f1872])).

fof(f4656,plain,
    ( spl31_680
    | spl31_684
    | ~ spl31_683
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4649,f1423,f562,f324,f883,f4643,f4654,f4637])).

fof(f4654,plain,
    ( spl31_684
  <=> v2_tex_2(sK4(sK1,sK22(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_684])])).

fof(f4649,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK22(sK0)),sK1)
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4615,f563])).

fof(f4615,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK22(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK22(sK0)),sK1)
    | v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4141,f1855])).

fof(f4648,plain,
    ( ~ spl31_681
    | spl31_682
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4635,f1423,f562,f324,f883,f4646,f4640])).

fof(f4635,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK22(sK0),sK1)
    | ~ v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4614,f563])).

fof(f4614,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_tex_2(sK22(sK0),sK1)
    | ~ v3_tex_2(sK22(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4141,f1476])).

fof(f4607,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4606,f1423,f873,f866])).

fof(f4606,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f4605,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4604,f1423,f876,f869])).

fof(f4604,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f4603,plain,
    ( spl31_236
    | ~ spl31_679
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4596,f1574,f836,f4601,f1650])).

fof(f4596,plain,
    ( ~ v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f3962,f837])).

fof(f3962,plain,
    ( ~ v1_subset_1(sK22(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f3959,f1575])).

fof(f3959,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK22(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f270,f274])).

fof(f270,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_subset_1(sK22(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f153])).

fof(f4595,plain,
    ( spl31_236
    | spl31_676
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4588,f1574,f836,f4593,f1650])).

fof(f4588,plain,
    ( m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4049,f837])).

fof(f4049,plain,
    ( m1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f3971,f1575])).

fof(f4587,plain,
    ( spl31_236
    | spl31_674
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4580,f1574,f836,f4585,f1650])).

fof(f4580,plain,
    ( m1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4109,f837])).

fof(f4109,plain,
    ( m1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4086,f1575])).

fof(f4579,plain,
    ( spl31_236
    | spl31_672
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4572,f1574,f836,f4577,f1650])).

fof(f4572,plain,
    ( r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4127,f837])).

fof(f4127,plain,
    ( r1_tarski(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4045,f1575])).

fof(f4045,plain,(
    ! [X11] :
      ( r1_tarski(sK20(X11),u1_struct_0(X11))
      | v7_struct_0(X11)
      | ~ l1_struct_0(X11) ) ),
    inference(resolution,[],[f3971,f225])).

fof(f4571,plain,
    ( spl31_236
    | spl31_670
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f4564,f1574,f836,f4569,f1650])).

fof(f4564,plain,
    ( r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f4140,f837])).

fof(f4140,plain,
    ( r1_tarski(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f4105,f1575])).

fof(f4105,plain,(
    ! [X11] :
      ( r1_tarski(sK21(X11),u1_struct_0(X11))
      | v7_struct_0(X11)
      | ~ l1_struct_0(X11) ) ),
    inference(resolution,[],[f4086,f225])).

fof(f4563,plain,
    ( spl31_122
    | ~ spl31_669
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4556,f1423,f569,f4561,f893])).

fof(f4556,plain,
    ( ~ v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3961,f570])).

fof(f3961,plain,
    ( ~ v1_subset_1(sK22(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f3959,f1424])).

fof(f4555,plain,
    ( spl31_122
    | spl31_666
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4548,f1423,f569,f4553,f893])).

fof(f4548,plain,
    ( m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4048,f570])).

fof(f4048,plain,
    ( m1_subset_1(sK20(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f3971,f1424])).

fof(f4547,plain,
    ( spl31_122
    | spl31_664
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4540,f1423,f569,f4545,f893])).

fof(f4540,plain,
    ( m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4108,f570])).

fof(f4108,plain,
    ( m1_subset_1(sK21(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4086,f1424])).

fof(f4539,plain,
    ( spl31_122
    | spl31_662
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4532,f1423,f569,f4537,f893])).

fof(f4532,plain,
    ( r1_tarski(sK20(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4126,f570])).

fof(f4126,plain,
    ( r1_tarski(sK20(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4045,f1424])).

fof(f4531,plain,
    ( spl31_122
    | spl31_660
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4524,f1423,f569,f4529,f893])).

fof(f4524,plain,
    ( r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4139,f570])).

fof(f4139,plain,
    ( r1_tarski(sK21(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f4105,f1424])).

fof(f4523,plain,
    ( ~ spl31_627
    | spl31_608
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4522,f1423,f562,f324,f883,f4337,f4402])).

fof(f4402,plain,
    ( spl31_627
  <=> ~ v3_tex_2(sK20(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_627])])).

fof(f4337,plain,
    ( spl31_608
  <=> v2_tex_2(sK20(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_608])])).

fof(f4522,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK20(sK0),sK1)
    | ~ v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4035,f563])).

fof(f4035,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_tex_2(sK20(sK0),sK1)
    | ~ v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3971,f1476])).

fof(f4521,plain,
    ( spl31_626
    | spl31_658
    | ~ spl31_609
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4514,f1423,f562,f324,f883,f4334,f4519,f4399])).

fof(f4399,plain,
    ( spl31_626
  <=> v3_tex_2(sK20(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_626])])).

fof(f4519,plain,
    ( spl31_658
  <=> v2_tex_2(sK4(sK1,sK20(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_658])])).

fof(f4334,plain,
    ( spl31_609
  <=> ~ v2_tex_2(sK20(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_609])])).

fof(f4514,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK20(sK0)),sK1)
    | v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4036,f563])).

fof(f4036,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK20(sK0)),sK1)
    | v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3971,f1855])).

fof(f4513,plain,
    ( spl31_626
    | spl31_656
    | ~ spl31_609
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4506,f1423,f562,f324,f883,f4334,f4511,f4399])).

fof(f4511,plain,
    ( spl31_656
  <=> r1_tarski(sK20(sK0),sK4(sK1,sK20(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_656])])).

fof(f4506,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | r1_tarski(sK20(sK0),sK4(sK1,sK20(sK0)))
    | v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4037,f563])).

fof(f4037,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | r1_tarski(sK20(sK0),sK4(sK1,sK20(sK0)))
    | v3_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3971,f1872])).

fof(f4505,plain,
    ( ~ spl31_637
    | spl31_638
    | ~ spl31_635
    | spl31_120
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f4504,f1225,f562,f331,f317,f883,f4427,f4439,f4433])).

fof(f4433,plain,
    ( spl31_637
  <=> ~ v3_tex_2(sK20(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_637])])).

fof(f4439,plain,
    ( spl31_638
  <=> sK3 = sK20(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_638])])).

fof(f4427,plain,
    ( spl31_635
  <=> ~ r1_tarski(sK20(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_635])])).

fof(f4504,plain,
    ( v7_struct_0(sK0)
    | ~ r1_tarski(sK20(sK0),sK3)
    | sK3 = sK20(sK0)
    | ~ v3_tex_2(sK20(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f4038,f563])).

fof(f4038,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ r1_tarski(sK20(sK0),sK3)
    | sK3 = sK20(sK0)
    | ~ v3_tex_2(sK20(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f3971,f2079])).

fof(f4503,plain,
    ( ~ spl31_627
    | spl31_654
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4499,f1423,f562,f324,f883,f4501,f4402])).

fof(f4501,plain,
    ( spl31_654
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK20(sK0) = X7
        | ~ r1_tarski(sK20(sK0),X7)
        | ~ v2_tex_2(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_654])])).

fof(f4499,plain,
    ( ! [X7] :
        ( v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK20(sK0),X7)
        | sK20(sK0) = X7
        | ~ v3_tex_2(sK20(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4039,f563])).

fof(f4039,plain,
    ( ! [X7] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK20(sK0),X7)
        | sK20(sK0) = X7
        | ~ v3_tex_2(sK20(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3971,f2084])).

fof(f4498,plain,
    ( spl31_652
    | ~ spl31_609
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4494,f1423,f562,f324,f883,f4334,f4496])).

fof(f4496,plain,
    ( spl31_652
  <=> ! [X8] :
        ( ~ r1_tarski(X8,sK20(sK0))
        | ~ r1_tarski(X8,u1_struct_0(sK0))
        | ~ v3_tex_2(X8,sK1)
        | sK20(sK0) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_652])])).

fof(f4494,plain,
    ( ! [X8] :
        ( v7_struct_0(sK0)
        | ~ v2_tex_2(sK20(sK0),sK1)
        | ~ r1_tarski(X8,sK20(sK0))
        | sK20(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4040,f563])).

fof(f4040,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ v2_tex_2(sK20(sK0),sK1)
        | ~ r1_tarski(X8,sK20(sK0))
        | sK20(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3971,f3529])).

fof(f4493,plain,
    ( spl31_610
    | ~ spl31_609
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4492,f1906,f1423,f562,f324,f317,f883,f4334,f4340])).

fof(f4340,plain,
    ( spl31_610
  <=> v2_tex_2(sK20(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_610])])).

fof(f4492,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK20(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4041,f563])).

fof(f4041,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK20(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f3971,f3813])).

fof(f4491,plain,
    ( spl31_120
    | spl31_626
    | ~ spl31_609
    | spl31_650
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4484,f1906,f1423,f562,f324,f317,f4489,f4334,f4399,f883])).

fof(f4489,plain,
    ( spl31_650
  <=> v2_tex_2(sK4(sK1,sK20(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_650])])).

fof(f4484,plain,
    ( v2_tex_2(sK4(sK1,sK20(sK0)),sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v3_tex_2(sK20(sK0),sK1)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4068,f563])).

fof(f4068,plain,
    ( v2_tex_2(sK4(sK1,sK20(sK0)),sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v3_tex_2(sK20(sK0),sK1)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f3834,f3971])).

fof(f4483,plain,
    ( ~ spl31_613
    | spl31_604
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4482,f1423,f562,f324,f883,f4323,f4353])).

fof(f4353,plain,
    ( spl31_613
  <=> ~ v3_tex_2(sK21(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_613])])).

fof(f4323,plain,
    ( spl31_604
  <=> v2_tex_2(sK21(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_604])])).

fof(f4482,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK21(sK0),sK1)
    | ~ v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4094,f563])).

fof(f4094,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_tex_2(sK21(sK0),sK1)
    | ~ v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4086,f1476])).

fof(f4481,plain,
    ( spl31_612
    | spl31_648
    | ~ spl31_605
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4474,f1423,f562,f324,f883,f4320,f4479,f4350])).

fof(f4350,plain,
    ( spl31_612
  <=> v3_tex_2(sK21(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_612])])).

fof(f4479,plain,
    ( spl31_648
  <=> v2_tex_2(sK4(sK1,sK21(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_648])])).

fof(f4320,plain,
    ( spl31_605
  <=> ~ v2_tex_2(sK21(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_605])])).

fof(f4474,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK21(sK0)),sK1)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4095,f563])).

fof(f4095,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK21(sK0)),sK1)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4086,f1855])).

fof(f4473,plain,
    ( spl31_612
    | spl31_646
    | ~ spl31_605
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4466,f1423,f562,f324,f883,f4320,f4471,f4350])).

fof(f4471,plain,
    ( spl31_646
  <=> r1_tarski(sK21(sK0),sK4(sK1,sK21(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_646])])).

fof(f4466,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | r1_tarski(sK21(sK0),sK4(sK1,sK21(sK0)))
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4096,f563])).

fof(f4096,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | r1_tarski(sK21(sK0),sK4(sK1,sK21(sK0)))
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4086,f1872])).

fof(f4465,plain,
    ( ~ spl31_623
    | spl31_624
    | ~ spl31_621
    | spl31_120
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f4464,f1225,f562,f331,f317,f883,f4378,f4390,f4384])).

fof(f4384,plain,
    ( spl31_623
  <=> ~ v3_tex_2(sK21(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_623])])).

fof(f4390,plain,
    ( spl31_624
  <=> sK3 = sK21(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_624])])).

fof(f4378,plain,
    ( spl31_621
  <=> ~ r1_tarski(sK21(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_621])])).

fof(f4464,plain,
    ( v7_struct_0(sK0)
    | ~ r1_tarski(sK21(sK0),sK3)
    | sK3 = sK21(sK0)
    | ~ v3_tex_2(sK21(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f4097,f563])).

fof(f4097,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ r1_tarski(sK21(sK0),sK3)
    | sK3 = sK21(sK0)
    | ~ v3_tex_2(sK21(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f4086,f2079])).

fof(f4463,plain,
    ( ~ spl31_613
    | spl31_644
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4459,f1423,f562,f324,f883,f4461,f4353])).

fof(f4461,plain,
    ( spl31_644
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK21(sK0) = X7
        | ~ r1_tarski(sK21(sK0),X7)
        | ~ v2_tex_2(X7,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_644])])).

fof(f4459,plain,
    ( ! [X7] :
        ( v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK21(sK0),X7)
        | sK21(sK0) = X7
        | ~ v3_tex_2(sK21(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4098,f563])).

fof(f4098,plain,
    ( ! [X7] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X7,sK1)
        | ~ r1_tarski(sK21(sK0),X7)
        | sK21(sK0) = X7
        | ~ v3_tex_2(sK21(sK0),sK1) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4086,f2084])).

fof(f4458,plain,
    ( spl31_642
    | ~ spl31_605
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4454,f1423,f562,f324,f883,f4320,f4456])).

fof(f4456,plain,
    ( spl31_642
  <=> ! [X8] :
        ( ~ r1_tarski(X8,sK21(sK0))
        | ~ r1_tarski(X8,u1_struct_0(sK0))
        | ~ v3_tex_2(X8,sK1)
        | sK21(sK0) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_642])])).

fof(f4454,plain,
    ( ! [X8] :
        ( v7_struct_0(sK0)
        | ~ v2_tex_2(sK21(sK0),sK1)
        | ~ r1_tarski(X8,sK21(sK0))
        | sK21(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4099,f563])).

fof(f4099,plain,
    ( ! [X8] :
        ( ~ l1_struct_0(sK0)
        | v7_struct_0(sK0)
        | ~ v2_tex_2(sK21(sK0),sK1)
        | ~ r1_tarski(X8,sK21(sK0))
        | sK21(sK0) = X8
        | ~ v3_tex_2(X8,sK1)
        | ~ r1_tarski(X8,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4086,f3529])).

fof(f4453,plain,
    ( spl31_606
    | ~ spl31_605
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4452,f1906,f1423,f562,f324,f317,f883,f4320,f4326])).

fof(f4326,plain,
    ( spl31_606
  <=> v2_tex_2(sK21(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_606])])).

fof(f4452,plain,
    ( v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK21(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4100,f563])).

fof(f4100,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK21(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4086,f3813])).

fof(f4451,plain,
    ( spl31_612
    | ~ spl31_605
    | spl31_640
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4444,f1906,f1423,f562,f324,f317,f883,f4449,f4320,f4350])).

fof(f4449,plain,
    ( spl31_640
  <=> v2_tex_2(sK4(sK1,sK21(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_640])])).

fof(f4444,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK4(sK1,sK21(sK0)),sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4101,f563])).

fof(f4101,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | v2_tex_2(sK4(sK1,sK21(sK0)),sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4086,f3834])).

fof(f4443,plain,
    ( spl31_608
    | ~ spl31_627
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4442,f1423,f562,f324,f883,f4402,f4337])).

fof(f4442,plain,
    ( v7_struct_0(sK0)
    | ~ v3_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4115,f563])).

fof(f4115,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v3_tex_2(sK20(sK0),sK1)
    | v2_tex_2(sK20(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4045,f1715])).

fof(f4441,plain,
    ( ~ spl31_635
    | ~ spl31_637
    | spl31_638
    | spl31_120
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f4422,f1225,f562,f331,f317,f883,f4439,f4433,f4427])).

fof(f4422,plain,
    ( v7_struct_0(sK0)
    | sK3 = sK20(sK0)
    | ~ v3_tex_2(sK20(sK0),sK0)
    | ~ r1_tarski(sK20(sK0),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f4116,f563])).

fof(f4116,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | sK3 = sK20(sK0)
    | ~ v3_tex_2(sK20(sK0),sK0)
    | ~ r1_tarski(sK20(sK0),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f4045,f2097])).

fof(f4421,plain,
    ( ~ spl31_631
    | spl31_632
    | ~ spl31_609
    | spl31_626
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4408,f1423,f562,f324,f883,f4399,f4334,f4419,f4413])).

fof(f4413,plain,
    ( spl31_631
  <=> ~ v1_xboole_0(sK4(sK1,sK20(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_631])])).

fof(f4419,plain,
    ( spl31_632
  <=> v1_xboole_0(sK20(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_632])])).

fof(f4408,plain,
    ( v7_struct_0(sK0)
    | v3_tex_2(sK20(sK0),sK1)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v1_xboole_0(sK20(sK0))
    | ~ v1_xboole_0(sK4(sK1,sK20(sK0)))
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4117,f563])).

fof(f4117,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v3_tex_2(sK20(sK0),sK1)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | v1_xboole_0(sK20(sK0))
    | ~ v1_xboole_0(sK4(sK1,sK20(sK0)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4045,f3272])).

fof(f4407,plain,
    ( ~ spl31_627
    | spl31_628
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4397,f1423,f562,f324,f883,f4405,f4402])).

fof(f4405,plain,
    ( spl31_628
  <=> ! [X0] :
        ( ~ r1_tarski(sK20(sK0),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK20(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_628])])).

fof(f4397,plain,
    ( ! [X0] :
        ( v7_struct_0(sK0)
        | ~ r1_tarski(sK20(sK0),X0)
        | sK20(sK0) = X0
        | ~ v3_tex_2(sK20(sK0),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4118,f563])).

fof(f4118,plain,
    ( ! [X0] :
        ( v7_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ r1_tarski(sK20(sK0),X0)
        | sK20(sK0) = X0
        | ~ v3_tex_2(sK20(sK0),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4045,f3549])).

fof(f4396,plain,
    ( ~ spl31_609
    | spl31_610
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4395,f1906,f1423,f562,f324,f317,f883,f4340,f4334])).

fof(f4395,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK20(sK0),sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4119,f563])).

fof(f4119,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_tex_2(sK20(sK0),sK0)
    | ~ v2_tex_2(sK20(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4045,f3832])).

fof(f4394,plain,
    ( spl31_604
    | ~ spl31_613
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4393,f1423,f562,f324,f883,f4353,f4323])).

fof(f4393,plain,
    ( v7_struct_0(sK0)
    | ~ v3_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4128,f563])).

fof(f4128,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v3_tex_2(sK21(sK0),sK1)
    | v2_tex_2(sK21(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4105,f1715])).

fof(f4392,plain,
    ( ~ spl31_621
    | ~ spl31_623
    | spl31_624
    | spl31_120
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f4373,f1225,f562,f331,f317,f883,f4390,f4384,f4378])).

fof(f4373,plain,
    ( v7_struct_0(sK0)
    | sK3 = sK21(sK0)
    | ~ v3_tex_2(sK21(sK0),sK0)
    | ~ r1_tarski(sK21(sK0),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f4129,f563])).

fof(f4129,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | sK3 = sK21(sK0)
    | ~ v3_tex_2(sK21(sK0),sK0)
    | ~ r1_tarski(sK21(sK0),sK3)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f4105,f2097])).

fof(f4372,plain,
    ( ~ spl31_617
    | spl31_618
    | ~ spl31_605
    | spl31_612
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4359,f1423,f562,f324,f883,f4350,f4320,f4370,f4364])).

fof(f4364,plain,
    ( spl31_617
  <=> ~ v1_xboole_0(sK4(sK1,sK21(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_617])])).

fof(f4370,plain,
    ( spl31_618
  <=> v1_xboole_0(sK21(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_618])])).

fof(f4359,plain,
    ( v7_struct_0(sK0)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v1_xboole_0(sK21(sK0))
    | ~ v1_xboole_0(sK4(sK1,sK21(sK0)))
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4130,f563])).

fof(f4130,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v3_tex_2(sK21(sK0),sK1)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | v1_xboole_0(sK21(sK0))
    | ~ v1_xboole_0(sK4(sK1,sK21(sK0)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4105,f3272])).

fof(f4358,plain,
    ( ~ spl31_613
    | spl31_614
    | spl31_120
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4348,f1423,f562,f324,f883,f4356,f4353])).

fof(f4356,plain,
    ( spl31_614
  <=> ! [X0] :
        ( ~ r1_tarski(sK21(sK0),X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK1)
        | sK21(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_614])])).

fof(f4348,plain,
    ( ! [X0] :
        ( v7_struct_0(sK0)
        | ~ r1_tarski(sK21(sK0),X0)
        | sK21(sK0) = X0
        | ~ v3_tex_2(sK21(sK0),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4131,f563])).

fof(f4131,plain,
    ( ! [X0] :
        ( v7_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ r1_tarski(sK21(sK0),X0)
        | sK21(sK0) = X0
        | ~ v3_tex_2(sK21(sK0),sK1)
        | ~ v2_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f4105,f3549])).

fof(f4347,plain,
    ( ~ spl31_605
    | spl31_606
    | spl31_120
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4346,f1906,f1423,f562,f324,f317,f883,f4326,f4320])).

fof(f4346,plain,
    ( v7_struct_0(sK0)
    | v2_tex_2(sK21(sK0),sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4132,f563])).

fof(f4132,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v2_tex_2(sK21(sK0),sK0)
    | ~ v2_tex_2(sK21(sK0),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4105,f3832])).

fof(f4345,plain,
    ( spl31_120
    | spl31_608
    | ~ spl31_611
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4332,f1906,f1423,f562,f324,f317,f4343,f4337,f883])).

fof(f4343,plain,
    ( spl31_611
  <=> ~ v2_tex_2(sK20(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_611])])).

fof(f4332,plain,
    ( ~ v2_tex_2(sK20(sK0),sK0)
    | v2_tex_2(sK20(sK0),sK1)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4174,f563])).

fof(f4174,plain,
    ( ~ v2_tex_2(sK20(sK0),sK0)
    | v2_tex_2(sK20(sK0),sK1)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f3971])).

fof(f4331,plain,
    ( spl31_120
    | spl31_604
    | ~ spl31_607
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4318,f1906,f1423,f562,f324,f317,f4329,f4323,f883])).

fof(f4329,plain,
    ( spl31_607
  <=> ~ v2_tex_2(sK21(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_607])])).

fof(f4318,plain,
    ( ~ v2_tex_2(sK21(sK0),sK0)
    | v2_tex_2(sK21(sK0),sK1)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4175,f563])).

fof(f4175,plain,
    ( ~ v2_tex_2(sK21(sK0),sK0)
    | v2_tex_2(sK21(sK0),sK1)
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f4086])).

fof(f4317,plain,
    ( spl31_116
    | ~ spl31_603
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | spl31_271
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4310,f1906,f1793,f1423,f324,f317,f4315,f866])).

fof(f4315,plain,
    ( spl31_603
  <=> ~ v2_tex_2(sK28(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_603])])).

fof(f1793,plain,
    ( spl31_271
  <=> ~ v2_tex_2(sK28(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_271])])).

fof(f4310,plain,
    ( ~ v2_tex_2(sK28(u1_struct_0(sK0)),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_271
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4181,f1794])).

fof(f1794,plain,
    ( ~ v2_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | ~ spl31_271 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f4181,plain,
    ( ~ v2_tex_2(sK28(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f1059])).

fof(f1059,plain,(
    ! [X0] :
      ( m1_subset_1(sK28(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f295,f280])).

fof(f295,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | m1_subset_1(sK28(X0),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc2_tex_2)).

fof(f4309,plain,
    ( spl31_116
    | ~ spl31_601
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | spl31_275
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4302,f1906,f1807,f1423,f324,f317,f4307,f866])).

fof(f4307,plain,
    ( spl31_601
  <=> ~ v2_tex_2(sK29(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_601])])).

fof(f1807,plain,
    ( spl31_275
  <=> ~ v2_tex_2(sK29(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_275])])).

fof(f4302,plain,
    ( ~ v2_tex_2(sK29(u1_struct_0(sK0)),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_275
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4182,f1808])).

fof(f1808,plain,
    ( ~ v2_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | ~ spl31_275 ),
    inference(avatar_component_clause,[],[f1807])).

fof(f4182,plain,
    ( ~ v2_tex_2(sK29(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f1160])).

fof(f1160,plain,(
    ! [X0] :
      ( m1_subset_1(sK29(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f299,f280])).

fof(f299,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | m1_subset_1(sK29(X0),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f95])).

fof(f95,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc3_tex_2)).

fof(f4301,plain,
    ( ~ spl31_599
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194
    | ~ spl31_284
    | spl31_361 ),
    inference(avatar_split_clause,[],[f4192,f2331,f1906,f1423,f726,f562,f324,f317,f4299])).

fof(f4299,plain,
    ( spl31_599
  <=> ~ v2_tex_2(sK15(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_599])])).

fof(f2331,plain,
    ( spl31_361
  <=> ~ v2_tex_2(sK15(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_361])])).

fof(f4192,plain,
    ( ~ v2_tex_2(sK15(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_361 ),
    inference(subsumption_resolution,[],[f4191,f727])).

fof(f4191,plain,
    ( ~ v2_tex_2(sK15(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_361 ),
    inference(subsumption_resolution,[],[f4190,f563])).

fof(f4190,plain,
    ( ~ v2_tex_2(sK15(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_361 ),
    inference(subsumption_resolution,[],[f4170,f2332])).

fof(f2332,plain,
    ( ~ v2_tex_2(sK15(sK0),sK1)
    | ~ spl31_361 ),
    inference(avatar_component_clause,[],[f2331])).

fof(f4170,plain,
    ( ~ v2_tex_2(sK15(sK0),sK0)
    | v2_tex_2(sK15(sK0),sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f243])).

fof(f4294,plain,
    ( ~ spl31_597
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194
    | ~ spl31_284
    | spl31_399 ),
    inference(avatar_split_clause,[],[f4195,f2592,f1906,f1423,f726,f562,f324,f317,f4292])).

fof(f4292,plain,
    ( spl31_597
  <=> ~ v2_tex_2(sK16(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_597])])).

fof(f2592,plain,
    ( spl31_399
  <=> ~ v2_tex_2(sK16(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_399])])).

fof(f4195,plain,
    ( ~ v2_tex_2(sK16(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_399 ),
    inference(subsumption_resolution,[],[f4194,f727])).

fof(f4194,plain,
    ( ~ v2_tex_2(sK16(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_399 ),
    inference(subsumption_resolution,[],[f4193,f563])).

fof(f4193,plain,
    ( ~ v2_tex_2(sK16(sK0),sK0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_399 ),
    inference(subsumption_resolution,[],[f4173,f2593])).

fof(f2593,plain,
    ( ~ v2_tex_2(sK16(sK0),sK1)
    | ~ spl31_399 ),
    inference(avatar_component_clause,[],[f2592])).

fof(f4173,plain,
    ( ~ v2_tex_2(sK16(sK0),sK0)
    | v2_tex_2(sK16(sK0),sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f246])).

fof(f4287,plain,
    ( ~ spl31_595
    | ~ spl31_0
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194
    | spl31_251
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4197,f1906,f1725,f1423,f650,f324,f317,f4285])).

fof(f4285,plain,
    ( spl31_595
  <=> ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_595])])).

fof(f1725,plain,
    ( spl31_251
  <=> ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_251])])).

fof(f4197,plain,
    ( ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194
    | ~ spl31_251
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4196,f651])).

fof(f4196,plain,
    ( ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_251
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4176,f1726])).

fof(f1726,plain,
    ( ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | ~ spl31_251 ),
    inference(avatar_component_clause,[],[f1725])).

fof(f4176,plain,
    ( ~ v2_tex_2(sK7(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f219])).

fof(f4280,plain,
    ( ~ spl31_593
    | ~ spl31_0
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194
    | spl31_259
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4199,f1906,f1752,f1423,f650,f324,f317,f4278])).

fof(f4278,plain,
    ( spl31_593
  <=> ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_593])])).

fof(f1752,plain,
    ( spl31_259
  <=> ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_259])])).

fof(f4199,plain,
    ( ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194
    | ~ spl31_259
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4198,f651])).

fof(f4198,plain,
    ( ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_259
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4178,f1753])).

fof(f1753,plain,
    ( ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | ~ spl31_259 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f4178,plain,
    ( ~ v2_tex_2(sK25(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f283])).

fof(f4273,plain,
    ( ~ spl31_591
    | ~ spl31_0
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194
    | spl31_263
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4201,f1906,f1766,f1423,f650,f324,f317,f4271])).

fof(f4271,plain,
    ( spl31_591
  <=> ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_591])])).

fof(f1766,plain,
    ( spl31_263
  <=> ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_263])])).

fof(f4201,plain,
    ( ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194
    | ~ spl31_263
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4200,f651])).

fof(f4200,plain,
    ( ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_263
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4179,f1767])).

fof(f1767,plain,
    ( ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | ~ spl31_263 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f4179,plain,
    ( ~ v2_tex_2(sK26(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f286])).

fof(f4266,plain,
    ( ~ spl31_589
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | spl31_267
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4202,f1906,f1779,f1423,f324,f317,f4264])).

fof(f4264,plain,
    ( spl31_589
  <=> ~ v2_tex_2(sK27(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_589])])).

fof(f1779,plain,
    ( spl31_267
  <=> ~ v2_tex_2(sK27(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_267])])).

fof(f4202,plain,
    ( ~ v2_tex_2(sK27(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_267
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4180,f1780])).

fof(f1780,plain,
    ( ~ v2_tex_2(sK27(u1_struct_0(sK0)),sK1)
    | ~ spl31_267 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f4180,plain,
    ( ~ v2_tex_2(sK27(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK27(u1_struct_0(sK0)),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f290])).

fof(f4259,plain,
    ( ~ spl31_587
    | ~ spl31_0
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194
    | spl31_279
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4204,f1906,f1821,f1423,f650,f324,f317,f4257])).

fof(f4257,plain,
    ( spl31_587
  <=> ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_587])])).

fof(f1821,plain,
    ( spl31_279
  <=> ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_279])])).

fof(f4204,plain,
    ( ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194
    | ~ spl31_279
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4203,f651])).

fof(f4203,plain,
    ( ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_279
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4183,f1822])).

fof(f1822,plain,
    ( ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | ~ spl31_279 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f4183,plain,
    ( ~ v2_tex_2(sK30(u1_struct_0(sK0)),sK0)
    | v2_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f306])).

fof(f4252,plain,
    ( ~ spl31_585
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | spl31_283
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4205,f1906,f1834,f1423,f324,f317,f4250])).

fof(f4250,plain,
    ( spl31_585
  <=> ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_585])])).

fof(f1834,plain,
    ( spl31_283
  <=> ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_283])])).

fof(f4205,plain,
    ( ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_283
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4185,f1835])).

fof(f1835,plain,
    ( ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl31_283 ),
    inference(avatar_component_clause,[],[f1834])).

fof(f4185,plain,
    ( ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f215])).

fof(f4245,plain,
    ( spl31_582
    | ~ spl31_297
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4238,f1423,f338,f331,f324,f2058,f4243])).

fof(f2058,plain,
    ( spl31_297
  <=> ~ v2_tex_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_297])])).

fof(f4238,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | r1_tarski(sK3,sK4(sK1,sK3))
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3251,f339])).

fof(f3251,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | r1_tarski(sK3,sK4(sK1,sK3))
    | v3_tex_2(sK3,sK1)
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194 ),
    inference(resolution,[],[f1872,f332])).

fof(f4237,plain,
    ( ~ spl31_581
    | ~ spl31_297
    | ~ spl31_2
    | spl31_7
    | spl31_87
    | ~ spl31_96
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f4230,f1423,f698,f641,f338,f324,f2058,f4235])).

fof(f4235,plain,
    ( spl31_581
  <=> ~ v1_xboole_0(sK4(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_581])])).

fof(f4230,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | ~ v1_xboole_0(sK4(sK1,sK3))
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_87
    | ~ spl31_96
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f4229,f642])).

fof(f4229,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK4(sK1,sK3))
    | ~ spl31_2
    | ~ spl31_7
    | ~ spl31_96
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3287,f339])).

fof(f3287,plain,
    ( v3_tex_2(sK3,sK1)
    | ~ v2_tex_2(sK3,sK1)
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK4(sK1,sK3))
    | ~ spl31_2
    | ~ spl31_96
    | ~ spl31_194 ),
    inference(resolution,[],[f3272,f699])).

fof(f4228,plain,
    ( spl31_578
    | ~ spl31_297
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3532,f1423,f331,f324,f2058,f4226])).

fof(f4226,plain,
    ( spl31_578
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ v3_tex_2(X0,sK1)
        | sK3 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_578])])).

fof(f3532,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(sK3,sK1)
        | ~ r1_tarski(X0,sK3)
        | sK3 = X0
        | ~ v3_tex_2(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194 ),
    inference(resolution,[],[f3529,f332])).

fof(f4224,plain,
    ( ~ spl31_297
    | spl31_576
    | ~ spl31_4
    | spl31_7
    | ~ spl31_560 ),
    inference(avatar_split_clause,[],[f4223,f3892,f338,f331,f4220,f2058])).

fof(f4220,plain,
    ( spl31_576
  <=> v1_zfmisc_1(sK4(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_576])])).

fof(f4223,plain,
    ( v1_zfmisc_1(sK4(sK1,sK3))
    | ~ v2_tex_2(sK3,sK1)
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_560 ),
    inference(subsumption_resolution,[],[f3972,f339])).

fof(f3972,plain,
    ( v1_zfmisc_1(sK4(sK1,sK3))
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_4
    | ~ spl31_560 ),
    inference(resolution,[],[f3893,f332])).

fof(f3893,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(sK4(sK1,X5))
        | ~ v2_tex_2(X5,sK1)
        | v3_tex_2(X5,sK1) )
    | ~ spl31_560 ),
    inference(avatar_component_clause,[],[f3892])).

fof(f4222,plain,
    ( spl31_576
    | ~ spl31_297
    | spl31_7
    | ~ spl31_96
    | ~ spl31_560 ),
    inference(avatar_split_clause,[],[f4215,f3892,f698,f338,f2058,f4220])).

fof(f4215,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v1_zfmisc_1(sK4(sK1,sK3))
    | ~ spl31_7
    | ~ spl31_96
    | ~ spl31_560 ),
    inference(subsumption_resolution,[],[f3994,f339])).

fof(f3994,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | v1_zfmisc_1(sK4(sK1,sK3))
    | ~ spl31_96
    | ~ spl31_560 ),
    inference(resolution,[],[f3989,f699])).

fof(f3989,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v2_tex_2(X2,sK1)
        | v3_tex_2(X2,sK1)
        | v1_zfmisc_1(sK4(sK1,X2)) )
    | ~ spl31_560 ),
    inference(resolution,[],[f3893,f224])).

fof(f4214,plain,
    ( ~ spl31_297
    | spl31_574
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4207,f1906,f1423,f338,f331,f324,f317,f4212,f2058])).

fof(f4212,plain,
    ( spl31_574
  <=> v2_tex_2(sK4(sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_574])])).

fof(f4207,plain,
    ( v2_tex_2(sK4(sK1,sK3),sK0)
    | ~ v2_tex_2(sK3,sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4059,f339])).

fof(f4059,plain,
    ( v2_tex_2(sK4(sK1,sK3),sK0)
    | ~ v2_tex_2(sK3,sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f3834,f332])).

fof(f4206,plain,
    ( spl31_296
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f4186,f1906,f1423,f1225,f331,f324,f317,f2055])).

fof(f4186,plain,
    ( v2_tex_2(sK3,sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f4165,f1226])).

fof(f4165,plain,
    ( ~ v2_tex_2(sK3,sK0)
    | v2_tex_2(sK3,sK1)
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(resolution,[],[f4164,f332])).

fof(f4188,plain,
    ( ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_194
    | ~ spl31_284
    | spl31_297 ),
    inference(avatar_contradiction_clause,[],[f4187])).

fof(f4187,plain,
    ( $false
    | ~ spl31_0
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_194
    | ~ spl31_284
    | ~ spl31_297 ),
    inference(subsumption_resolution,[],[f4186,f2059])).

fof(f2059,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | ~ spl31_297 ),
    inference(avatar_component_clause,[],[f2058])).

fof(f3970,plain,
    ( ~ spl31_573
    | spl31_553 ),
    inference(avatar_split_clause,[],[f3963,f3861,f3968])).

fof(f3968,plain,
    ( spl31_573
  <=> ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_573])])).

fof(f3861,plain,
    ( spl31_553
  <=> ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_553])])).

fof(f3963,plain,
    ( ~ r1_tarski(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl31_553 ),
    inference(resolution,[],[f3862,f224])).

fof(f3862,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_553 ),
    inference(avatar_component_clause,[],[f3861])).

fof(f3957,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3956,f1423,f873,f866])).

fof(f3956,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f3955,plain,
    ( spl31_236
    | spl31_570
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f3945,f1574,f836,f3951,f1650])).

fof(f3945,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f3935,f837])).

fof(f3935,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f3928,f1575])).

fof(f3928,plain,(
    ! [X0] :
      ( v1_subset_1(sK21(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f266,f274])).

fof(f266,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_subset_1(sK21(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f151])).

fof(f3954,plain,
    ( spl31_122
    | spl31_568
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3936,f1423,f569,f3942,f893])).

fof(f3936,plain,
    ( v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3934,f570])).

fof(f3934,plain,
    ( v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f3928,f1424])).

fof(f3953,plain,
    ( spl31_570
    | ~ spl31_110
    | ~ spl31_220
    | spl31_237 ),
    inference(avatar_split_clause,[],[f3946,f1653,f1574,f836,f3951])).

fof(f3946,plain,
    ( v1_subset_1(sK21(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_237 ),
    inference(subsumption_resolution,[],[f3945,f1654])).

fof(f3944,plain,
    ( spl31_568
    | ~ spl31_70
    | spl31_123
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3937,f1423,f896,f569,f3942])).

fof(f3937,plain,
    ( v1_subset_1(sK21(sK1),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3936,f897])).

fof(f3932,plain,
    ( spl31_107
    | ~ spl31_110
    | spl31_565 ),
    inference(avatar_contradiction_clause,[],[f3931])).

fof(f3931,plain,
    ( $false
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_565 ),
    inference(subsumption_resolution,[],[f3930,f812])).

fof(f3930,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_565 ),
    inference(subsumption_resolution,[],[f3929,f837])).

fof(f3929,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_565 ),
    inference(resolution,[],[f3906,f245])).

fof(f3906,plain,
    ( ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_565 ),
    inference(avatar_component_clause,[],[f3905])).

fof(f3905,plain,
    ( spl31_565
  <=> ~ v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_565])])).

fof(f3925,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3924,f1423,f876,f869])).

fof(f3924,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f3923,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3922,f1423,f873,f866])).

fof(f3922,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f3921,plain,
    ( spl31_236
    | spl31_558
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f3882,f1574,f836,f3888,f1650])).

fof(f3882,plain,
    ( v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f3872,f837])).

fof(f3872,plain,
    ( v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f3814,f1575])).

fof(f3814,plain,(
    ! [X0] :
      ( v1_subset_1(sK20(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f262,f274])).

fof(f262,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_subset_1(sK20(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f149])).

fof(f3920,plain,
    ( spl31_122
    | spl31_556
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3873,f1423,f569,f3879,f893])).

fof(f3873,plain,
    ( v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3871,f570])).

fof(f3871,plain,
    ( v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f3814,f1424])).

fof(f3919,plain,
    ( spl31_566
    | ~ spl31_117
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2800,f2604,f869,f3916])).

fof(f2800,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK16(sK1))
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f282])).

fof(f3918,plain,
    ( ~ spl31_117
    | spl31_566
    | ~ spl31_460 ),
    inference(avatar_split_clause,[],[f2903,f2875,f3916,f869])).

fof(f2875,plain,
    ( spl31_460
  <=> r1_tarski(sK16(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_460])])).

fof(f2903,plain,
    ( v1_zfmisc_1(sK16(sK1))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_460 ),
    inference(resolution,[],[f2876,f854])).

fof(f2876,plain,
    ( r1_tarski(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_460 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f3911,plain,
    ( spl31_564
    | ~ spl31_117
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3010,f2352,f869,f3908])).

fof(f3010,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f282])).

fof(f3910,plain,
    ( ~ spl31_117
    | spl31_564
    | ~ spl31_496 ),
    inference(avatar_split_clause,[],[f3109,f3085,f3908,f869])).

fof(f3109,plain,
    ( v1_zfmisc_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_496 ),
    inference(resolution,[],[f3086,f854])).

fof(f3903,plain,
    ( spl31_562
    | ~ spl31_117
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3121,f2613,f869,f3900])).

fof(f3121,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f282])).

fof(f3902,plain,
    ( ~ spl31_117
    | spl31_562
    | ~ spl31_520 ),
    inference(avatar_split_clause,[],[f3216,f3196,f3900,f869])).

fof(f3216,plain,
    ( v1_zfmisc_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_520 ),
    inference(resolution,[],[f3197,f854])).

fof(f3895,plain,
    ( ~ spl31_117
    | spl31_560
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3320,f1423,f324,f3892,f869])).

fof(f3320,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X12,sK1)
        | v3_tex_2(X12,sK1)
        | ~ v1_zfmisc_1(u1_struct_0(sK0))
        | v1_zfmisc_1(sK4(sK1,X12)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1975,f282])).

fof(f3894,plain,
    ( ~ spl31_117
    | spl31_560
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3334,f1423,f324,f3892,f869])).

fof(f3334,plain,
    ( ! [X5] :
        ( ~ v2_tex_2(X5,sK1)
        | v3_tex_2(X5,sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_zfmisc_1(sK4(sK1,X5))
        | ~ v1_zfmisc_1(u1_struct_0(sK0)) )
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f3321,f854])).

fof(f3890,plain,
    ( spl31_558
    | ~ spl31_110
    | ~ spl31_220
    | spl31_237 ),
    inference(avatar_split_clause,[],[f3883,f1653,f1574,f836,f3888])).

fof(f3883,plain,
    ( v1_subset_1(sK20(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_237 ),
    inference(subsumption_resolution,[],[f3882,f1654])).

fof(f3881,plain,
    ( spl31_556
    | ~ spl31_70
    | spl31_123
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f3874,f1423,f896,f569,f3879])).

fof(f3874,plain,
    ( v1_subset_1(sK20(sK1),u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f3873,f897])).

fof(f3869,plain,
    ( ~ spl31_553
    | ~ spl31_555
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292
    | spl31_499 ),
    inference(avatar_split_clause,[],[f3853,f3101,f2009,f1906,f1574,f1423,f828,f324,f3867,f3861])).

fof(f3867,plain,
    ( spl31_555
  <=> ~ v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_555])])).

fof(f3101,plain,
    ( spl31_499
  <=> ~ v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_499])])).

fof(f3853,plain,
    ( ~ v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_108
    | ~ spl31_194
    | ~ spl31_220
    | ~ spl31_284
    | ~ spl31_292
    | ~ spl31_499 ),
    inference(resolution,[],[f3807,f3102])).

fof(f3102,plain,
    ( ~ v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_499 ),
    inference(avatar_component_clause,[],[f3101])).

fof(f3802,plain,
    ( ~ spl31_549
    | spl31_550
    | ~ spl31_2
    | ~ spl31_24
    | ~ spl31_124
    | ~ spl31_144
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f3792,f1906,f1423,f1114,f937,f401,f324,f3800,f3797])).

fof(f3797,plain,
    ( spl31_549
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_549])])).

fof(f3800,plain,
    ( spl31_550
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | v2_tex_2(X0,sK11)
        | ~ v2_tex_2(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_550])])).

fof(f401,plain,
    ( spl31_24
  <=> l1_pre_topc(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_24])])).

fof(f937,plain,
    ( spl31_124
  <=> u1_struct_0(sK11) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_124])])).

fof(f1114,plain,
    ( spl31_144
  <=> g1_pre_topc(sK9,u1_pre_topc(sK11)) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_144])])).

fof(f3792,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK11) )
    | ~ spl31_2
    | ~ spl31_24
    | ~ spl31_124
    | ~ spl31_144
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3791,f938])).

fof(f938,plain,
    ( u1_struct_0(sK11) = sK9
    | ~ spl31_124 ),
    inference(avatar_component_clause,[],[f937])).

fof(f3791,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK11
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK11) )
    | ~ spl31_2
    | ~ spl31_24
    | ~ spl31_124
    | ~ spl31_144
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f3790,f1115])).

fof(f1115,plain,
    ( g1_pre_topc(sK9,u1_pre_topc(sK11)) = sK11
    | ~ spl31_144 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f3790,plain,
    ( ! [X0] :
        ( g1_pre_topc(sK9,u1_pre_topc(sK11)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK11) )
    | ~ spl31_2
    | ~ spl31_24
    | ~ spl31_124
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f3780,f402])).

fof(f402,plain,
    ( l1_pre_topc(sK11)
    | ~ spl31_24 ),
    inference(avatar_component_clause,[],[f401])).

fof(f3780,plain,
    ( ! [X0] :
        ( g1_pre_topc(sK9,u1_pre_topc(sK11)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK11)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK11)))
        | ~ v2_tex_2(X0,sK1)
        | v2_tex_2(X0,sK11) )
    | ~ spl31_2
    | ~ spl31_124
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(superposition,[],[f3622,f938])).

fof(f3598,plain,
    ( spl31_544
    | ~ spl31_547
    | ~ spl31_126
    | ~ spl31_144
    | ~ spl31_150 ),
    inference(avatar_split_clause,[],[f3570,f1138,f1114,f956,f3596,f3590])).

fof(f3590,plain,
    ( spl31_544
  <=> u1_struct_0(sK14) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_544])])).

fof(f3596,plain,
    ( spl31_547
  <=> sK11 != sK14 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_547])])).

fof(f1138,plain,
    ( spl31_150
  <=> g1_pre_topc(u1_struct_0(sK14),u1_pre_topc(sK14)) = sK14 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_150])])).

fof(f3570,plain,
    ( sK11 != sK14
    | u1_struct_0(sK14) = sK9
    | ~ spl31_126
    | ~ spl31_144
    | ~ spl31_150 ),
    inference(superposition,[],[f1323,f1139])).

fof(f1139,plain,
    ( g1_pre_topc(u1_struct_0(sK14),u1_pre_topc(sK14)) = sK14
    | ~ spl31_150 ),
    inference(avatar_component_clause,[],[f1138])).

fof(f1323,plain,
    ( ! [X10,X11] :
        ( g1_pre_topc(X10,X11) != sK11
        | sK9 = X10 )
    | ~ spl31_126
    | ~ spl31_144 ),
    inference(subsumption_resolution,[],[f1265,f957])).

fof(f1265,plain,
    ( ! [X10,X11] :
        ( g1_pre_topc(X10,X11) != sK11
        | ~ m1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(k1_zfmisc_1(sK9)))
        | sK9 = X10 )
    | ~ spl31_144 ),
    inference(superposition,[],[f207,f1115])).

fof(f3585,plain,
    ( spl31_540
    | ~ spl31_543
    | ~ spl31_126
    | ~ spl31_144
    | ~ spl31_148 ),
    inference(avatar_split_clause,[],[f3569,f1130,f1114,f956,f3583,f3577])).

fof(f3577,plain,
    ( spl31_540
  <=> u1_struct_0(sK13) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_540])])).

fof(f3583,plain,
    ( spl31_543
  <=> sK11 != sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_543])])).

fof(f1130,plain,
    ( spl31_148
  <=> g1_pre_topc(u1_struct_0(sK13),u1_pre_topc(sK13)) = sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_148])])).

fof(f3569,plain,
    ( sK11 != sK13
    | u1_struct_0(sK13) = sK9
    | ~ spl31_126
    | ~ spl31_144
    | ~ spl31_148 ),
    inference(superposition,[],[f1323,f1131])).

fof(f1131,plain,
    ( g1_pre_topc(u1_struct_0(sK13),u1_pre_topc(sK13)) = sK13
    | ~ spl31_148 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f3483,plain,
    ( spl31_538
    | ~ spl31_170 ),
    inference(avatar_split_clause,[],[f3459,f1314,f3481])).

fof(f3481,plain,
    ( spl31_538
  <=> r1_tarski(u1_pre_topc(sK14),k1_zfmisc_1(u1_struct_0(sK14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_538])])).

fof(f3459,plain,
    ( r1_tarski(u1_pre_topc(sK14),k1_zfmisc_1(u1_struct_0(sK14)))
    | ~ spl31_170 ),
    inference(resolution,[],[f1315,f225])).

fof(f3476,plain,
    ( spl31_534
    | ~ spl31_537
    | ~ spl31_170 ),
    inference(avatar_split_clause,[],[f3458,f1314,f3474,f3468])).

fof(f3468,plain,
    ( spl31_534
  <=> v1_zfmisc_1(u1_pre_topc(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_534])])).

fof(f3474,plain,
    ( spl31_537
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_537])])).

fof(f3458,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))
    | v1_zfmisc_1(u1_pre_topc(sK14))
    | ~ spl31_170 ),
    inference(resolution,[],[f1315,f282])).

fof(f3453,plain,
    ( ~ spl31_44
    | spl31_171 ),
    inference(avatar_contradiction_clause,[],[f3452])).

fof(f3452,plain,
    ( $false
    | ~ spl31_44
    | ~ spl31_171 ),
    inference(subsumption_resolution,[],[f3450,f472])).

fof(f472,plain,
    ( l1_pre_topc(sK14)
    | ~ spl31_44 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl31_44
  <=> l1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_44])])).

fof(f3450,plain,
    ( ~ l1_pre_topc(sK14)
    | ~ spl31_171 ),
    inference(resolution,[],[f1318,f214])).

fof(f1318,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))))
    | ~ spl31_171 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1317,plain,
    ( spl31_171
  <=> ~ m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_171])])).

fof(f3416,plain,
    ( spl31_532
    | ~ spl31_166 ),
    inference(avatar_split_clause,[],[f3392,f1304,f3414])).

fof(f3414,plain,
    ( spl31_532
  <=> r1_tarski(u1_pre_topc(sK13),k1_zfmisc_1(u1_struct_0(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_532])])).

fof(f3392,plain,
    ( r1_tarski(u1_pre_topc(sK13),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ spl31_166 ),
    inference(resolution,[],[f1305,f225])).

fof(f3409,plain,
    ( spl31_528
    | ~ spl31_531
    | ~ spl31_166 ),
    inference(avatar_split_clause,[],[f3391,f1304,f3407,f3401])).

fof(f3401,plain,
    ( spl31_528
  <=> v1_zfmisc_1(u1_pre_topc(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_528])])).

fof(f3407,plain,
    ( spl31_531
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_531])])).

fof(f3391,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))
    | v1_zfmisc_1(u1_pre_topc(sK13))
    | ~ spl31_166 ),
    inference(resolution,[],[f1305,f282])).

fof(f3386,plain,
    ( ~ spl31_36
    | spl31_167 ),
    inference(avatar_contradiction_clause,[],[f3385])).

fof(f3385,plain,
    ( $false
    | ~ spl31_36
    | ~ spl31_167 ),
    inference(subsumption_resolution,[],[f3383,f444])).

fof(f444,plain,
    ( l1_pre_topc(sK13)
    | ~ spl31_36 ),
    inference(avatar_component_clause,[],[f443])).

fof(f443,plain,
    ( spl31_36
  <=> l1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_36])])).

fof(f3383,plain,
    ( ~ l1_pre_topc(sK13)
    | ~ spl31_167 ),
    inference(resolution,[],[f1308,f214])).

fof(f1308,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))))
    | ~ spl31_167 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f1307,plain,
    ( spl31_167
  <=> ~ m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_167])])).

fof(f3375,plain,
    ( spl31_526
    | ~ spl31_162 ),
    inference(avatar_split_clause,[],[f3350,f1294,f3373])).

fof(f3373,plain,
    ( spl31_526
  <=> r1_tarski(u1_pre_topc(sK12),k1_zfmisc_1(u1_struct_0(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_526])])).

fof(f3350,plain,
    ( r1_tarski(u1_pre_topc(sK12),k1_zfmisc_1(u1_struct_0(sK12)))
    | ~ spl31_162 ),
    inference(resolution,[],[f1295,f225])).

fof(f3368,plain,
    ( spl31_522
    | ~ spl31_525
    | ~ spl31_162 ),
    inference(avatar_split_clause,[],[f3349,f1294,f3366,f3360])).

fof(f3360,plain,
    ( spl31_522
  <=> v1_zfmisc_1(u1_pre_topc(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_522])])).

fof(f3366,plain,
    ( spl31_525
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_525])])).

fof(f3349,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12)))
    | v1_zfmisc_1(u1_pre_topc(sK12))
    | ~ spl31_162 ),
    inference(resolution,[],[f1295,f282])).

fof(f3341,plain,
    ( ~ spl31_28
    | spl31_163 ),
    inference(avatar_contradiction_clause,[],[f3340])).

fof(f3340,plain,
    ( $false
    | ~ spl31_28
    | ~ spl31_163 ),
    inference(subsumption_resolution,[],[f3338,f416])).

fof(f416,plain,
    ( l1_pre_topc(sK12)
    | ~ spl31_28 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl31_28
  <=> l1_pre_topc(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_28])])).

fof(f3338,plain,
    ( ~ l1_pre_topc(sK12)
    | ~ spl31_163 ),
    inference(resolution,[],[f1298,f214])).

fof(f1298,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12))))
    | ~ spl31_163 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f1297,plain,
    ( spl31_163
  <=> ~ m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_163])])).

fof(f3198,plain,
    ( spl31_520
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3122,f2613,f3196])).

fof(f3122,plain,
    ( r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f225])).

fof(f3191,plain,
    ( ~ spl31_501
    | spl31_512
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3190,f2613,f317,f3165,f3128])).

fof(f3128,plain,
    ( spl31_501
  <=> ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_501])])).

fof(f3165,plain,
    ( spl31_512
  <=> v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_512])])).

fof(f3190,plain,
    ( v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f3119,f318])).

fof(f3119,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f203])).

fof(f3189,plain,
    ( spl31_500
    | spl31_518
    | ~ spl31_513
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3182,f2613,f317,f3168,f3187,f3125])).

fof(f3125,plain,
    ( spl31_500
  <=> v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_500])])).

fof(f3187,plain,
    ( spl31_518
  <=> v2_tex_2(sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_518])])).

fof(f3168,plain,
    ( spl31_513
  <=> ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_513])])).

fof(f3182,plain,
    ( ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f3118,f318])).

fof(f3118,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f199])).

fof(f3181,plain,
    ( spl31_500
    | spl31_516
    | ~ spl31_513
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3174,f2613,f317,f3168,f3179,f3125])).

fof(f3179,plain,
    ( spl31_516
  <=> r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_516])])).

fof(f3174,plain,
    ( ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f3117,f318])).

fof(f3117,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f200])).

fof(f3173,plain,
    ( ~ spl31_513
    | spl31_514
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3163,f2613,f317,f3171,f3168])).

fof(f3171,plain,
    ( spl31_514
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ r1_tarski(X0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_514])])).

fof(f3163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_402 ),
    inference(subsumption_resolution,[],[f3116,f318])).

fof(f3116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X0,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f202])).

fof(f3162,plain,
    ( ~ spl31_507
    | spl31_510
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3113,f2613,f1423,f324,f3156,f3144])).

fof(f3144,plain,
    ( spl31_507
  <=> ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_507])])).

fof(f3156,plain,
    ( spl31_510
  <=> v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_510])])).

fof(f3113,plain,
    ( v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f1476])).

fof(f3161,plain,
    ( spl31_506
    | spl31_508
    | ~ spl31_511
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3112,f2613,f1423,f324,f3159,f3153,f3147])).

fof(f3147,plain,
    ( spl31_506
  <=> v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_506])])).

fof(f3153,plain,
    ( spl31_508
  <=> v2_tex_2(sK4(sK1,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_508])])).

fof(f3159,plain,
    ( spl31_511
  <=> ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_511])])).

fof(f3112,plain,
    ( ~ v2_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK4(sK1,sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f1855])).

fof(f3142,plain,
    ( ~ spl31_501
    | spl31_502
    | ~ spl31_505
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_402 ),
    inference(avatar_split_clause,[],[f3111,f2613,f1225,f331,f317,f3140,f3134,f3128])).

fof(f3134,plain,
    ( spl31_502
  <=> sK3 = sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_502])])).

fof(f3140,plain,
    ( spl31_505
  <=> ~ r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_505])])).

fof(f3111,plain,
    ( ~ r1_tarski(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3)
    | sK3 = sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_402 ),
    inference(resolution,[],[f2614,f2079])).

fof(f3106,plain,
    ( spl31_498
    | ~ spl31_439
    | spl31_436
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f3099,f1574,f828,f2776,f2782,f3104])).

fof(f3104,plain,
    ( spl31_498
  <=> v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_498])])).

fof(f2782,plain,
    ( spl31_439
  <=> ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_439])])).

fof(f2776,plain,
    ( spl31_436
  <=> v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_436])])).

fof(f3099,plain,
    ( v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f3098,f1575])).

fof(f3098,plain,
    ( ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f3097,f1575])).

fof(f3097,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f3090,f829])).

fof(f3090,plain,
    ( v2_tex_2(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK5(k1_zfmisc_1(u1_struct_0(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f1850,f1575])).

fof(f1850,plain,(
    ! [X10] :
      ( v2_tex_2(sK4(X10,sK5(k1_zfmisc_1(u1_struct_0(X10)))),X10)
      | ~ v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(X10))),X10)
      | ~ l1_pre_topc(X10)
      | v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(X10))),X10) ) ),
    inference(resolution,[],[f199,f215])).

fof(f3087,plain,
    ( spl31_496
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3011,f2352,f3085])).

fof(f3011,plain,
    ( r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK0))
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f225])).

fof(f3080,plain,
    ( ~ spl31_477
    | spl31_488
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3079,f2352,f317,f3054,f3017])).

fof(f3017,plain,
    ( spl31_477
  <=> ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_477])])).

fof(f3054,plain,
    ( spl31_488
  <=> v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_488])])).

fof(f3079,plain,
    ( v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f3008,f318])).

fof(f3008,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f203])).

fof(f3078,plain,
    ( spl31_476
    | spl31_494
    | ~ spl31_489
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3071,f2352,f317,f3057,f3076,f3014])).

fof(f3014,plain,
    ( spl31_476
  <=> v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_476])])).

fof(f3076,plain,
    ( spl31_494
  <=> v2_tex_2(sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_494])])).

fof(f3057,plain,
    ( spl31_489
  <=> ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_489])])).

fof(f3071,plain,
    ( ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f3007,f318])).

fof(f3007,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | v2_tex_2(sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK0)
    | v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f199])).

fof(f3070,plain,
    ( spl31_476
    | spl31_492
    | ~ spl31_489
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3063,f2352,f317,f3057,f3068,f3014])).

fof(f3068,plain,
    ( spl31_492
  <=> r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_492])])).

fof(f3063,plain,
    ( ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f3006,f318])).

fof(f3006,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK4(sK0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f200])).

fof(f3062,plain,
    ( ~ spl31_489
    | spl31_490
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3052,f2352,f317,f3060,f3057])).

fof(f3060,plain,
    ( spl31_490
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ r1_tarski(X0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_490])])).

fof(f3052,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_364 ),
    inference(subsumption_resolution,[],[f3005,f318])).

fof(f3005,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
        | ~ r1_tarski(X0,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
        | sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f202])).

fof(f3051,plain,
    ( ~ spl31_483
    | spl31_486
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3002,f2352,f1423,f324,f3045,f3033])).

fof(f3033,plain,
    ( spl31_483
  <=> ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_483])])).

fof(f3045,plain,
    ( spl31_486
  <=> v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_486])])).

fof(f3002,plain,
    ( v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f1476])).

fof(f3050,plain,
    ( spl31_482
    | spl31_484
    | ~ spl31_487
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3001,f2352,f1423,f324,f3048,f3042,f3036])).

fof(f3036,plain,
    ( spl31_482
  <=> v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_482])])).

fof(f3042,plain,
    ( spl31_484
  <=> v2_tex_2(sK4(sK1,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_484])])).

fof(f3048,plain,
    ( spl31_487
  <=> ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_487])])).

fof(f3001,plain,
    ( ~ v2_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | v2_tex_2(sK4(sK1,sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f1855])).

fof(f3031,plain,
    ( ~ spl31_477
    | spl31_478
    | ~ spl31_481
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_364 ),
    inference(avatar_split_clause,[],[f3000,f2352,f1225,f331,f317,f3029,f3023,f3017])).

fof(f3023,plain,
    ( spl31_478
  <=> sK3 = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_478])])).

fof(f3029,plain,
    ( spl31_481
  <=> ~ r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_481])])).

fof(f3000,plain,
    ( ~ r1_tarski(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK3)
    | sK3 = sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_364 ),
    inference(resolution,[],[f2353,f2079])).

fof(f2959,plain,
    ( ~ spl31_473
    | spl31_474
    | ~ spl31_16
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2949,f1574,f828,f373,f2957,f2954])).

fof(f2954,plain,
    ( spl31_473
  <=> ~ v2_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_473])])).

fof(f2957,plain,
    ( spl31_474
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | sK9 = X2
        | ~ r1_tarski(X2,sK9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_474])])).

fof(f2949,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK9)
        | sK9 = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_16
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2923,f829])).

fof(f2923,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tex_2(sK9,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ r1_tarski(X2,sK9)
        | sK9 = X2
        | ~ v3_tex_2(X2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl31_16
    | ~ spl31_220 ),
    inference(superposition,[],[f2065,f1575])).

fof(f2065,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7)
        | ~ v2_tex_2(sK9,X7)
        | ~ r1_tarski(X6,sK9)
        | sK9 = X6
        | ~ v3_tex_2(X6,X7) )
    | ~ spl31_16 ),
    inference(resolution,[],[f202,f629])).

fof(f2948,plain,
    ( ~ spl31_435
    | spl31_470
    | ~ spl31_16
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f2944,f937,f401,f373,f2946,f2767])).

fof(f2767,plain,
    ( spl31_435
  <=> ~ v2_tex_2(sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_435])])).

fof(f2946,plain,
    ( spl31_470
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | ~ v3_tex_2(X0,sK11)
        | sK9 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_470])])).

fof(f2944,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | ~ v2_tex_2(sK9,sK11)
        | sK9 = X0
        | ~ v3_tex_2(X0,sK11) )
    | ~ spl31_16
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f2943,f225])).

fof(f2943,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | ~ v2_tex_2(sK9,sK11)
        | ~ r1_tarski(X0,sK9)
        | sK9 = X0
        | ~ v3_tex_2(X0,sK11) )
    | ~ spl31_16
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f2921,f402])).

fof(f2921,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
        | ~ l1_pre_topc(sK11)
        | ~ v2_tex_2(sK9,sK11)
        | ~ r1_tarski(X0,sK9)
        | sK9 = X0
        | ~ v3_tex_2(X0,sK11) )
    | ~ spl31_16
    | ~ spl31_124 ),
    inference(superposition,[],[f2065,f938])).

fof(f2940,plain,
    ( ~ spl31_467
    | ~ spl31_469
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_16
    | spl31_307 ),
    inference(avatar_split_clause,[],[f2927,f2128,f373,f345,f331,f317,f2938,f2932])).

fof(f2932,plain,
    ( spl31_467
  <=> ~ r1_tarski(sK3,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_467])])).

fof(f2938,plain,
    ( spl31_469
  <=> ~ v2_tex_2(sK9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_469])])).

fof(f2128,plain,
    ( spl31_307
  <=> sK3 != sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_307])])).

fof(f2927,plain,
    ( ~ v2_tex_2(sK9,sK0)
    | ~ r1_tarski(sK3,sK9)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_8
    | ~ spl31_16
    | ~ spl31_307 ),
    inference(subsumption_resolution,[],[f2926,f346])).

fof(f2926,plain,
    ( ~ v2_tex_2(sK9,sK0)
    | ~ r1_tarski(sK3,sK9)
    | ~ v3_tex_2(sK3,sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_16
    | ~ spl31_307 ),
    inference(subsumption_resolution,[],[f2925,f2129])).

fof(f2129,plain,
    ( sK3 != sK9
    | ~ spl31_307 ),
    inference(avatar_component_clause,[],[f2128])).

fof(f2925,plain,
    ( ~ v2_tex_2(sK9,sK0)
    | ~ r1_tarski(sK3,sK9)
    | sK3 = sK9
    | ~ v3_tex_2(sK3,sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_16 ),
    inference(subsumption_resolution,[],[f2905,f318])).

fof(f2905,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK9,sK0)
    | ~ r1_tarski(sK3,sK9)
    | sK3 = sK9
    | ~ v3_tex_2(sK3,sK0)
    | ~ spl31_4
    | ~ spl31_16 ),
    inference(resolution,[],[f2065,f332])).

fof(f2900,plain,
    ( ~ spl31_463
    | spl31_464
    | spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2887,f1574,f828,f650,f2898,f2892])).

fof(f2892,plain,
    ( spl31_463
  <=> ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_463])])).

fof(f2898,plain,
    ( spl31_464
  <=> v2_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_464])])).

fof(f2887,plain,
    ( v2_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_89
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2886,f651])).

fof(f2886,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f2885,f1575])).

fof(f2885,plain,
    ( v2_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f2884,f1575])).

fof(f2884,plain,
    ( ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2880,f829])).

fof(f2880,plain,
    ( ~ v3_tex_2(sK7(u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK7(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_220 ),
    inference(superposition,[],[f1208,f1575])).

fof(f1208,plain,(
    ! [X0] :
      ( ~ v3_tex_2(sK7(u1_struct_0(X0)),X0)
      | v2_tex_2(sK7(u1_struct_0(X0)),X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f203,f219])).

fof(f2877,plain,
    ( spl31_460
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2801,f2604,f2875])).

fof(f2801,plain,
    ( r1_tarski(sK16(sK1),u1_struct_0(sK0))
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f225])).

fof(f2870,plain,
    ( ~ spl31_441
    | spl31_452
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2869,f2604,f317,f2844,f2807])).

fof(f2807,plain,
    ( spl31_441
  <=> ~ v3_tex_2(sK16(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_441])])).

fof(f2844,plain,
    ( spl31_452
  <=> v2_tex_2(sK16(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_452])])).

fof(f2869,plain,
    ( v2_tex_2(sK16(sK1),sK0)
    | ~ v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f2798,f318])).

fof(f2798,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK16(sK1),sK0)
    | ~ v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f203])).

fof(f2868,plain,
    ( spl31_440
    | spl31_458
    | ~ spl31_453
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2861,f2604,f317,f2847,f2866,f2804])).

fof(f2804,plain,
    ( spl31_440
  <=> v3_tex_2(sK16(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_440])])).

fof(f2866,plain,
    ( spl31_458
  <=> v2_tex_2(sK4(sK0,sK16(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_458])])).

fof(f2847,plain,
    ( spl31_453
  <=> ~ v2_tex_2(sK16(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_453])])).

fof(f2861,plain,
    ( ~ v2_tex_2(sK16(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK16(sK1)),sK0)
    | v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f2797,f318])).

fof(f2797,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK16(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK16(sK1)),sK0)
    | v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f199])).

fof(f2860,plain,
    ( spl31_440
    | spl31_456
    | ~ spl31_453
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2853,f2604,f317,f2847,f2858,f2804])).

fof(f2858,plain,
    ( spl31_456
  <=> r1_tarski(sK16(sK1),sK4(sK0,sK16(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_456])])).

fof(f2853,plain,
    ( ~ v2_tex_2(sK16(sK1),sK0)
    | r1_tarski(sK16(sK1),sK4(sK0,sK16(sK1)))
    | v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f2796,f318])).

fof(f2796,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK16(sK1),sK0)
    | r1_tarski(sK16(sK1),sK4(sK0,sK16(sK1)))
    | v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f200])).

fof(f2852,plain,
    ( ~ spl31_453
    | spl31_454
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2842,f2604,f317,f2850,f2847])).

fof(f2850,plain,
    ( spl31_454
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | sK16(sK1) = X0
        | ~ r1_tarski(X0,sK16(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_454])])).

fof(f2842,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK16(sK1),sK0)
        | ~ r1_tarski(X0,sK16(sK1))
        | sK16(sK1) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_400 ),
    inference(subsumption_resolution,[],[f2795,f318])).

fof(f2795,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK16(sK1),sK0)
        | ~ r1_tarski(X0,sK16(sK1))
        | sK16(sK1) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f202])).

fof(f2841,plain,
    ( ~ spl31_447
    | spl31_450
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2794,f2604,f1423,f324,f2835,f2823])).

fof(f2823,plain,
    ( spl31_447
  <=> ~ v3_tex_2(sK16(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_447])])).

fof(f2835,plain,
    ( spl31_450
  <=> v2_tex_2(sK16(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_450])])).

fof(f2794,plain,
    ( v2_tex_2(sK16(sK1),sK1)
    | ~ v3_tex_2(sK16(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f1476])).

fof(f2840,plain,
    ( spl31_446
    | spl31_448
    | ~ spl31_451
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2793,f2604,f1423,f324,f2838,f2832,f2826])).

fof(f2826,plain,
    ( spl31_446
  <=> v3_tex_2(sK16(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_446])])).

fof(f2832,plain,
    ( spl31_448
  <=> v2_tex_2(sK4(sK1,sK16(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_448])])).

fof(f2838,plain,
    ( spl31_451
  <=> ~ v2_tex_2(sK16(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_451])])).

fof(f2793,plain,
    ( ~ v2_tex_2(sK16(sK1),sK1)
    | v2_tex_2(sK4(sK1,sK16(sK1)),sK1)
    | v3_tex_2(sK16(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f1855])).

fof(f2821,plain,
    ( ~ spl31_441
    | spl31_442
    | ~ spl31_445
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_400 ),
    inference(avatar_split_clause,[],[f2792,f2604,f1225,f331,f317,f2819,f2813,f2807])).

fof(f2813,plain,
    ( spl31_442
  <=> sK3 = sK16(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_442])])).

fof(f2819,plain,
    ( spl31_445
  <=> ~ r1_tarski(sK16(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_445])])).

fof(f2792,plain,
    ( ~ r1_tarski(sK16(sK1),sK3)
    | sK3 = sK16(sK1)
    | ~ v3_tex_2(sK16(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_400 ),
    inference(resolution,[],[f2605,f2079])).

fof(f2787,plain,
    ( ~ spl31_437
    | spl31_438
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2774,f1574,f828,f2785,f2779])).

fof(f2779,plain,
    ( spl31_437
  <=> ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_437])])).

fof(f2785,plain,
    ( spl31_438
  <=> v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_438])])).

fof(f2774,plain,
    ( v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f2773,f1575])).

fof(f2773,plain,
    ( ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2755,f829])).

fof(f2755,plain,
    ( ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f1217,f1575])).

fof(f1217,plain,(
    ! [X10] :
      ( ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(X10))),X10)
      | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(X10))),X10)
      | ~ l1_pre_topc(X10) ) ),
    inference(resolution,[],[f203,f215])).

fof(f2772,plain,
    ( ~ spl31_433
    | spl31_434
    | ~ spl31_24
    | ~ spl31_104
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f2759,f937,f797,f401,f2770,f2764])).

fof(f2764,plain,
    ( spl31_433
  <=> ~ v3_tex_2(sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_433])])).

fof(f2770,plain,
    ( spl31_434
  <=> v2_tex_2(sK9,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_434])])).

fof(f797,plain,
    ( spl31_104
  <=> sK5(k1_zfmisc_1(sK9)) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_104])])).

fof(f2759,plain,
    ( v2_tex_2(sK9,sK11)
    | ~ v3_tex_2(sK9,sK11)
    | ~ spl31_24
    | ~ spl31_104
    | ~ spl31_124 ),
    inference(forward_demodulation,[],[f2758,f798])).

fof(f798,plain,
    ( sK5(k1_zfmisc_1(sK9)) = sK9
    | ~ spl31_104 ),
    inference(avatar_component_clause,[],[f797])).

fof(f2758,plain,
    ( v2_tex_2(sK5(k1_zfmisc_1(sK9)),sK11)
    | ~ v3_tex_2(sK9,sK11)
    | ~ spl31_24
    | ~ spl31_104
    | ~ spl31_124 ),
    inference(forward_demodulation,[],[f2757,f938])).

fof(f2757,plain,
    ( ~ v3_tex_2(sK9,sK11)
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK11))),sK11)
    | ~ spl31_24
    | ~ spl31_104
    | ~ spl31_124 ),
    inference(forward_demodulation,[],[f2756,f798])).

fof(f2756,plain,
    ( ~ v3_tex_2(sK5(k1_zfmisc_1(sK9)),sK11)
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK11))),sK11)
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f2753,f402])).

fof(f2753,plain,
    ( ~ v3_tex_2(sK5(k1_zfmisc_1(sK9)),sK11)
    | v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK11))),sK11)
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f1217,f938])).

fof(f2752,plain,
    ( ~ spl31_70
    | spl31_103
    | spl31_429 ),
    inference(avatar_contradiction_clause,[],[f2751])).

fof(f2751,plain,
    ( $false
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_429 ),
    inference(subsumption_resolution,[],[f2750,f735])).

fof(f2750,plain,
    ( v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_429 ),
    inference(subsumption_resolution,[],[f2749,f570])).

fof(f2749,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_429 ),
    inference(resolution,[],[f2732,f245])).

fof(f2732,plain,
    ( ~ v1_zfmisc_1(sK15(sK1))
    | ~ spl31_429 ),
    inference(avatar_component_clause,[],[f2731])).

fof(f2731,plain,
    ( spl31_429
  <=> ~ v1_zfmisc_1(sK15(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_429])])).

fof(f2746,plain,
    ( ~ spl31_117
    | spl31_119
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2745,f1423,f876,f869])).

fof(f2745,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_119
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f877,f1424])).

fof(f2744,plain,
    ( spl31_428
    | ~ spl31_117
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2658,f2343,f869,f2734])).

fof(f2658,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK15(sK1))
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f282])).

fof(f2743,plain,
    ( spl31_430
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2659,f2343,f2741])).

fof(f2741,plain,
    ( spl31_430
  <=> r1_tarski(sK15(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_430])])).

fof(f2659,plain,
    ( r1_tarski(sK15(sK1),u1_struct_0(sK0))
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f225])).

fof(f2736,plain,
    ( spl31_428
    | ~ spl31_116
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2729,f2343,f866,f2734])).

fof(f2729,plain,
    ( v1_zfmisc_1(sK15(sK1))
    | ~ spl31_116
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f2658,f867])).

fof(f2728,plain,
    ( ~ spl31_409
    | spl31_420
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2727,f2343,f317,f2702,f2665])).

fof(f2665,plain,
    ( spl31_409
  <=> ~ v3_tex_2(sK15(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_409])])).

fof(f2702,plain,
    ( spl31_420
  <=> v2_tex_2(sK15(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_420])])).

fof(f2727,plain,
    ( v2_tex_2(sK15(sK1),sK0)
    | ~ v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f2656,f318])).

fof(f2656,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK15(sK1),sK0)
    | ~ v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f203])).

fof(f2726,plain,
    ( spl31_408
    | spl31_426
    | ~ spl31_421
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2719,f2343,f317,f2705,f2724,f2662])).

fof(f2662,plain,
    ( spl31_408
  <=> v3_tex_2(sK15(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_408])])).

fof(f2724,plain,
    ( spl31_426
  <=> v2_tex_2(sK4(sK0,sK15(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_426])])).

fof(f2705,plain,
    ( spl31_421
  <=> ~ v2_tex_2(sK15(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_421])])).

fof(f2719,plain,
    ( ~ v2_tex_2(sK15(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK15(sK1)),sK0)
    | v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f2655,f318])).

fof(f2655,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK15(sK1),sK0)
    | v2_tex_2(sK4(sK0,sK15(sK1)),sK0)
    | v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f199])).

fof(f2718,plain,
    ( spl31_408
    | spl31_424
    | ~ spl31_421
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2711,f2343,f317,f2705,f2716,f2662])).

fof(f2716,plain,
    ( spl31_424
  <=> r1_tarski(sK15(sK1),sK4(sK0,sK15(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_424])])).

fof(f2711,plain,
    ( ~ v2_tex_2(sK15(sK1),sK0)
    | r1_tarski(sK15(sK1),sK4(sK0,sK15(sK1)))
    | v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f2654,f318])).

fof(f2654,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK15(sK1),sK0)
    | r1_tarski(sK15(sK1),sK4(sK0,sK15(sK1)))
    | v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f200])).

fof(f2710,plain,
    ( ~ spl31_421
    | spl31_422
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2700,f2343,f317,f2708,f2705])).

fof(f2708,plain,
    ( spl31_422
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | sK15(sK1) = X0
        | ~ r1_tarski(X0,sK15(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_422])])).

fof(f2700,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK15(sK1),sK0)
        | ~ r1_tarski(X0,sK15(sK1))
        | sK15(sK1) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_0
    | ~ spl31_362 ),
    inference(subsumption_resolution,[],[f2653,f318])).

fof(f2653,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_tex_2(sK15(sK1),sK0)
        | ~ r1_tarski(X0,sK15(sK1))
        | sK15(sK1) = X0
        | ~ v3_tex_2(X0,sK0) )
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f202])).

fof(f2699,plain,
    ( ~ spl31_415
    | spl31_418
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2652,f2343,f1423,f324,f2693,f2681])).

fof(f2681,plain,
    ( spl31_415
  <=> ~ v3_tex_2(sK15(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_415])])).

fof(f2693,plain,
    ( spl31_418
  <=> v2_tex_2(sK15(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_418])])).

fof(f2652,plain,
    ( v2_tex_2(sK15(sK1),sK1)
    | ~ v3_tex_2(sK15(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f1476])).

fof(f2698,plain,
    ( spl31_414
    | spl31_416
    | ~ spl31_419
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2651,f2343,f1423,f324,f2696,f2690,f2684])).

fof(f2684,plain,
    ( spl31_414
  <=> v3_tex_2(sK15(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_414])])).

fof(f2690,plain,
    ( spl31_416
  <=> v2_tex_2(sK4(sK1,sK15(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_416])])).

fof(f2696,plain,
    ( spl31_419
  <=> ~ v2_tex_2(sK15(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_419])])).

fof(f2651,plain,
    ( ~ v2_tex_2(sK15(sK1),sK1)
    | v2_tex_2(sK4(sK1,sK15(sK1)),sK1)
    | v3_tex_2(sK15(sK1),sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f1855])).

fof(f2679,plain,
    ( ~ spl31_409
    | spl31_410
    | ~ spl31_413
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_362 ),
    inference(avatar_split_clause,[],[f2650,f2343,f1225,f331,f317,f2677,f2671,f2665])).

fof(f2671,plain,
    ( spl31_410
  <=> sK3 = sK15(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_410])])).

fof(f2677,plain,
    ( spl31_413
  <=> ~ r1_tarski(sK15(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_413])])).

fof(f2650,plain,
    ( ~ r1_tarski(sK15(sK1),sK3)
    | sK3 = sK15(sK1)
    | ~ v3_tex_2(sK15(sK1),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152
    | ~ spl31_362 ),
    inference(resolution,[],[f2344,f2079])).

fof(f2649,plain,
    ( spl31_404
    | ~ spl31_407
    | ~ spl31_28
    | ~ spl31_146 ),
    inference(avatar_split_clause,[],[f2636,f1122,f415,f2647,f2641])).

fof(f2641,plain,
    ( spl31_404
  <=> v1_xboole_0(u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_404])])).

fof(f2647,plain,
    ( spl31_407
  <=> ~ v2_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_407])])).

fof(f1122,plain,
    ( spl31_146
  <=> g1_pre_topc(u1_struct_0(sK12),u1_pre_topc(sK12)) = sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_146])])).

fof(f2636,plain,
    ( ~ v2_struct_0(sK12)
    | v1_xboole_0(u1_struct_0(sK12))
    | ~ spl31_28
    | ~ spl31_146 ),
    inference(subsumption_resolution,[],[f2621,f416])).

fof(f2621,plain,
    ( ~ v2_struct_0(sK12)
    | v1_xboole_0(u1_struct_0(sK12))
    | ~ l1_pre_topc(sK12)
    | ~ spl31_146 ),
    inference(superposition,[],[f993,f1123])).

fof(f1123,plain,
    ( g1_pre_topc(u1_struct_0(sK12),u1_pre_topc(sK12)) = sK12
    | ~ spl31_146 ),
    inference(avatar_component_clause,[],[f1122])).

fof(f2615,plain,
    ( spl31_402
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2608,f1574,f836,f811,f2613])).

fof(f2608,plain,
    ( m1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2607,f812])).

fof(f2607,plain,
    ( m1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2548,f837])).

fof(f2548,plain,
    ( m1_subset_1(sK16(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f246,f1575])).

fof(f2606,plain,
    ( spl31_400
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2599,f1423,f734,f569,f2604])).

fof(f2599,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2598,f735])).

fof(f2598,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2547,f570])).

fof(f2547,plain,
    ( m1_subset_1(sK16(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f246,f1424])).

fof(f2597,plain,
    ( ~ spl31_395
    | spl31_398
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2596,f1423,f726,f562,f324,f2589,f2577])).

fof(f2577,plain,
    ( spl31_395
  <=> ~ v3_tex_2(sK16(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_395])])).

fof(f2589,plain,
    ( spl31_398
  <=> v2_tex_2(sK16(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_398])])).

fof(f2596,plain,
    ( v2_tex_2(sK16(sK0),sK1)
    | ~ v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2595,f727])).

fof(f2595,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK16(sK0),sK1)
    | ~ v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2541,f563])).

fof(f2541,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK16(sK0),sK1)
    | ~ v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f246,f1476])).

fof(f2594,plain,
    ( spl31_394
    | spl31_396
    | ~ spl31_399
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2575,f1423,f726,f562,f324,f2592,f2586,f2580])).

fof(f2580,plain,
    ( spl31_394
  <=> v3_tex_2(sK16(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_394])])).

fof(f2586,plain,
    ( spl31_396
  <=> v2_tex_2(sK4(sK1,sK16(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_396])])).

fof(f2575,plain,
    ( ~ v2_tex_2(sK16(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK16(sK0)),sK1)
    | v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2574,f727])).

fof(f2574,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK16(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK16(sK0)),sK1)
    | v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2540,f563])).

fof(f2540,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK16(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK16(sK0)),sK1)
    | v3_tex_2(sK16(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f246,f1855])).

fof(f2573,plain,
    ( ~ spl31_389
    | spl31_390
    | ~ spl31_393
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | spl31_101
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2554,f1225,f726,f562,f331,f317,f2571,f2565,f2559])).

fof(f2559,plain,
    ( spl31_389
  <=> ~ v3_tex_2(sK16(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_389])])).

fof(f2565,plain,
    ( spl31_390
  <=> sK3 = sK16(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_390])])).

fof(f2571,plain,
    ( spl31_393
  <=> ~ r1_tarski(sK16(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_393])])).

fof(f2554,plain,
    ( ~ r1_tarski(sK16(sK0),sK3)
    | sK3 = sK16(sK0)
    | ~ v3_tex_2(sK16(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2553,f727])).

fof(f2553,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tarski(sK16(sK0),sK3)
    | sK3 = sK16(sK0)
    | ~ v3_tex_2(sK16(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2539,f563])).

fof(f2539,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK16(sK0),sK3)
    | sK3 = sK16(sK0)
    | ~ v3_tex_2(sK16(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f246,f2079])).

fof(f2534,plain,
    ( spl31_120
    | ~ spl31_68
    | ~ spl31_116 ),
    inference(avatar_split_clause,[],[f2531,f866,f562,f883])).

fof(f2531,plain,
    ( v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_116 ),
    inference(subsumption_resolution,[],[f2530,f563])).

fof(f2530,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl31_116 ),
    inference(resolution,[],[f867,f273])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc6_struct_0)).

fof(f2533,plain,
    ( ~ spl31_68
    | ~ spl31_116
    | spl31_121 ),
    inference(avatar_contradiction_clause,[],[f2532])).

fof(f2532,plain,
    ( $false
    | ~ spl31_68
    | ~ spl31_116
    | ~ spl31_121 ),
    inference(subsumption_resolution,[],[f2531,f887])).

fof(f2528,plain,
    ( ~ spl31_89
    | spl31_91
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2527,f1423,f657,f650])).

fof(f657,plain,
    ( spl31_91
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_91])])).

fof(f2527,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_91
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f658,f1424])).

fof(f658,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_91 ),
    inference(avatar_component_clause,[],[f657])).

fof(f2526,plain,
    ( ~ spl31_107
    | spl31_205
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2525,f1906,f1483,f811])).

fof(f1483,plain,
    ( spl31_205
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_205])])).

fof(f2525,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_205
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1484,f1907])).

fof(f1484,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_205 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f2524,plain,
    ( ~ spl31_107
    | spl31_233
    | ~ spl31_292 ),
    inference(avatar_split_clause,[],[f2523,f2009,f1636,f811])).

fof(f1636,plain,
    ( spl31_233
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_233])])).

fof(f2523,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_233
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f1637,f2010])).

fof(f1637,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_233 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f2522,plain,
    ( spl31_386
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2436,f644,f373,f2520])).

fof(f2520,plain,
    ( spl31_386
  <=> sK9 = sK27(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_386])])).

fof(f644,plain,
    ( spl31_86
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_86])])).

fof(f2436,plain,
    ( sK9 = sK27(sK3)
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f660])).

fof(f645,plain,
    ( v1_xboole_0(sK3)
    | ~ spl31_86 ),
    inference(avatar_component_clause,[],[f644])).

fof(f2515,plain,
    ( spl31_384
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2438,f644,f373,f2513])).

fof(f2513,plain,
    ( spl31_384
  <=> sK5(k1_zfmisc_1(sK3)) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_384])])).

fof(f2438,plain,
    ( sK5(k1_zfmisc_1(sK3)) = sK9
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f663])).

fof(f2508,plain,
    ( spl31_382
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2440,f644,f373,f2506])).

fof(f2506,plain,
    ( spl31_382
  <=> sK9 = sK27(sK27(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_382])])).

fof(f2440,plain,
    ( sK9 = sK27(sK27(sK3))
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f667])).

fof(f2501,plain,
    ( spl31_380
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2441,f644,f373,f2499])).

fof(f2499,plain,
    ( spl31_380
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_380])])).

fof(f2441,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK3)))
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f668])).

fof(f2494,plain,
    ( spl31_378
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2442,f644,f373,f2492])).

fof(f2492,plain,
    ( spl31_378
  <=> sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_378])])).

fof(f2442,plain,
    ( sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK3)))) = sK9
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f790])).

fof(f2487,plain,
    ( spl31_376
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2443,f644,f373,f2485])).

fof(f2485,plain,
    ( spl31_376
  <=> sK5(k1_zfmisc_1(sK27(sK3))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_376])])).

fof(f2443,plain,
    ( sK5(k1_zfmisc_1(sK27(sK3))) = sK9
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f792])).

fof(f2480,plain,
    ( spl31_374
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2444,f644,f373,f2478])).

fof(f2478,plain,
    ( spl31_374
  <=> sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_374])])).

fof(f2444,plain,
    ( sK9 = sK27(sK27(sK5(k1_zfmisc_1(sK3))))
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f817])).

fof(f2473,plain,
    ( spl31_372
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2445,f644,f373,f2471])).

fof(f2471,plain,
    ( spl31_372
  <=> sK9 = sK27(sK27(sK27(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_372])])).

fof(f2445,plain,
    ( sK9 = sK27(sK27(sK27(sK3)))
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f819])).

fof(f2466,plain,
    ( spl31_370
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2447,f644,f373,f2464])).

fof(f2464,plain,
    ( spl31_370
  <=> sK5(k1_zfmisc_1(sK27(sK27(sK3)))) = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_370])])).

fof(f2447,plain,
    ( sK5(k1_zfmisc_1(sK27(sK27(sK3)))) = sK9
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f1036])).

fof(f2459,plain,
    ( spl31_368
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2448,f644,f373,f2457])).

fof(f2457,plain,
    ( spl31_368
  <=> sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_368])])).

fof(f2448,plain,
    ( sK9 = sK27(sK5(k1_zfmisc_1(sK27(sK3))))
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f1041])).

fof(f2452,plain,
    ( spl31_306
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2435,f644,f373,f2131])).

fof(f2131,plain,
    ( spl31_306
  <=> sK3 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_306])])).

fof(f2435,plain,
    ( sK3 = sK9
    | ~ spl31_16
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f625])).

fof(f2451,plain,
    ( ~ spl31_16
    | ~ spl31_86
    | spl31_307 ),
    inference(avatar_contradiction_clause,[],[f2450])).

fof(f2450,plain,
    ( $false
    | ~ spl31_16
    | ~ spl31_86
    | ~ spl31_307 ),
    inference(subsumption_resolution,[],[f2435,f2129])).

fof(f2449,plain,
    ( spl31_114
    | ~ spl31_86 ),
    inference(avatar_split_clause,[],[f2434,f644,f863])).

fof(f2434,plain,
    ( v1_zfmisc_1(sK3)
    | ~ spl31_86 ),
    inference(resolution,[],[f645,f280])).

fof(f2432,plain,
    ( spl31_236
    | ~ spl31_117
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2416,f1574,f836,f869,f1650])).

fof(f2416,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1615,f837])).

fof(f1615,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f273,f1575])).

fof(f2431,plain,
    ( ~ spl31_237
    | spl31_116
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2430,f1574,f836,f866,f1653])).

fof(f2430,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1614,f837])).

fof(f1614,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f256,f1575])).

fof(f256,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc7_struct_0)).

fof(f2429,plain,
    ( ~ spl31_123
    | spl31_116
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2428,f1423,f569,f866,f896])).

fof(f2428,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1440,f570])).

fof(f1440,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f256,f1424])).

fof(f2427,plain,
    ( spl31_122
    | ~ spl31_117
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2419,f1423,f569,f869,f893])).

fof(f2419,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1441,f570])).

fof(f1441,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v7_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f273,f1424])).

fof(f2426,plain,
    ( spl31_116
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2425,f1423,f873,f866])).

fof(f2425,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_118
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f874,f1424])).

fof(f2424,plain,
    ( spl31_114
    | ~ spl31_117
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2423,f1423,f705,f869,f863])).

fof(f705,plain,
    ( spl31_98
  <=> r1_tarski(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_98])])).

fof(f2423,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK3)
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f902,f1424])).

fof(f902,plain,
    ( v1_zfmisc_1(sK3)
    | ~ v1_zfmisc_1(u1_struct_0(sK1))
    | ~ spl31_98 ),
    inference(resolution,[],[f854,f706])).

fof(f706,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_98 ),
    inference(avatar_component_clause,[],[f705])).

fof(f2422,plain,
    ( ~ spl31_117
    | spl31_114
    | ~ spl31_96 ),
    inference(avatar_split_clause,[],[f901,f698,f863,f869])).

fof(f901,plain,
    ( v1_zfmisc_1(sK3)
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_96 ),
    inference(resolution,[],[f854,f699])).

fof(f2421,plain,
    ( ~ spl31_117
    | ~ spl31_70
    | spl31_123
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2420,f1423,f896,f569,f869])).

fof(f2420,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_70
    | ~ spl31_123
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2419,f897])).

fof(f2418,plain,
    ( ~ spl31_117
    | ~ spl31_110
    | ~ spl31_220
    | spl31_237 ),
    inference(avatar_split_clause,[],[f2417,f1653,f1574,f836,f869])).

fof(f2417,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_110
    | ~ spl31_220
    | ~ spl31_237 ),
    inference(subsumption_resolution,[],[f2416,f1654])).

fof(f2415,plain,
    ( ~ spl31_103
    | spl31_116
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2414,f1423,f569,f866,f734])).

fof(f2414,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1442,f570])).

fof(f1442,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f720,f1424])).

fof(f720,plain,(
    ! [X4] :
      ( v1_zfmisc_1(u1_struct_0(X4))
      | ~ v2_struct_0(X4)
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f242,f280])).

fof(f2413,plain,
    ( ~ spl31_107
    | spl31_116
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2412,f1574,f836,f866,f811])).

fof(f2412,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1616,f837])).

fof(f1616,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f720,f1575])).

fof(f2411,plain,
    ( spl31_88
    | ~ spl31_90
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2410,f1423,f654,f647])).

fof(f647,plain,
    ( spl31_88
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_88])])).

fof(f654,plain,
    ( spl31_90
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_90])])).

fof(f2410,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_90
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f655,f1424])).

fof(f655,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_90 ),
    inference(avatar_component_clause,[],[f654])).

fof(f2409,plain,
    ( spl31_106
    | ~ spl31_204
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2408,f1906,f1480,f808])).

fof(f808,plain,
    ( spl31_106
  <=> v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_106])])).

fof(f1480,plain,
    ( spl31_204
  <=> v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_204])])).

fof(f2408,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_204
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1481,f1907])).

fof(f1481,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_204 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f2407,plain,
    ( spl31_106
    | ~ spl31_232
    | ~ spl31_292 ),
    inference(avatar_split_clause,[],[f2406,f2009,f1633,f808])).

fof(f1633,plain,
    ( spl31_232
  <=> v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_232])])).

fof(f2406,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_232
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f1634,f2010])).

fof(f1634,plain,
    ( v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_232 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f2405,plain,
    ( spl31_88
    | ~ spl31_107
    | ~ spl31_234
    | ~ spl31_292 ),
    inference(avatar_split_clause,[],[f2404,f2009,f1644,f811,f647])).

fof(f1644,plain,
    ( spl31_234
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_234])])).

fof(f2404,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_234
    | ~ spl31_292 ),
    inference(forward_demodulation,[],[f1884,f2010])).

fof(f1884,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_234 ),
    inference(resolution,[],[f1645,f205])).

fof(f1645,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_234 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f2402,plain,
    ( ~ spl31_107
    | spl31_88
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2401,f1574,f836,f647,f811])).

fof(f2401,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1612,f837])).

fof(f1612,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f242,f1575])).

fof(f2400,plain,
    ( ~ spl31_107
    | ~ spl31_110
    | spl31_117
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2399,f1574,f869,f836,f811])).

fof(f2399,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_117
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2398,f837])).

fof(f2398,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_117
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1616,f870])).

fof(f870,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_117 ),
    inference(avatar_component_clause,[],[f869])).

fof(f2397,plain,
    ( ~ spl31_107
    | spl31_88
    | ~ spl31_286 ),
    inference(avatar_split_clause,[],[f1983,f1923,f647,f811])).

fof(f1983,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_286 ),
    inference(resolution,[],[f1924,f205])).

fof(f2395,plain,
    ( spl31_106
    | spl31_364
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2346,f1574,f836,f2352,f808])).

fof(f2346,plain,
    ( m1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2287,f837])).

fof(f2287,plain,
    ( m1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f243,f1575])).

fof(f2394,plain,
    ( spl31_102
    | ~ spl31_107
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(avatar_split_clause,[],[f805,f352,f324,f811,f731])).

fof(f731,plain,
    ( spl31_102
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_102])])).

fof(f352,plain,
    ( spl31_10
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_10])])).

fof(f805,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(subsumption_resolution,[],[f804,f325])).

fof(f804,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_10 ),
    inference(superposition,[],[f211,f353])).

fof(f353,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl31_10 ),
    inference(avatar_component_clause,[],[f352])).

fof(f211,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc7_pre_topc)).

fof(f2393,plain,
    ( ~ spl31_103
    | ~ spl31_70
    | spl31_119 ),
    inference(avatar_split_clause,[],[f2392,f876,f569,f734])).

fof(f2392,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_119 ),
    inference(subsumption_resolution,[],[f889,f570])).

fof(f889,plain,
    ( ~ v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_119 ),
    inference(resolution,[],[f877,f720])).

fof(f2391,plain,
    ( spl31_102
    | ~ spl31_107
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2390,f1906,f1423,f324,f811,f731])).

fof(f2390,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1477,f1907])).

fof(f1477,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | v2_struct_0(sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1436,f325])).

fof(f1436,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f211,f1424])).

fof(f2389,plain,
    ( ~ spl31_103
    | spl31_88
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2388,f1423,f569,f647,f734])).

fof(f2388,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1438,f570])).

fof(f1438,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f242,f1424])).

fof(f2387,plain,
    ( ~ spl31_103
    | ~ spl31_70
    | spl31_117
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2386,f1423,f869,f569,f734])).

fof(f2386,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_117
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2385,f570])).

fof(f2385,plain,
    ( ~ v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl31_117
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1442,f870])).

fof(f2384,plain,
    ( spl31_102
    | ~ spl31_107
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2383,f1906,f1423,f324,f811,f731])).

fof(f2383,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1949,f1424])).

fof(f1949,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_2
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f1917,f325])).

fof(f1917,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_284 ),
    inference(superposition,[],[f211,f1907])).

fof(f2382,plain,
    ( spl31_102
    | spl31_362
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2337,f1423,f569,f2343,f731])).

fof(f2337,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2286,f570])).

fof(f2286,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f243,f1424])).

fof(f2381,plain,
    ( spl31_86
    | ~ spl31_89
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2380,f1423,f705,f650,f644])).

fof(f2380,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f766,f1424])).

fof(f766,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_98 ),
    inference(resolution,[],[f638,f706])).

fof(f2379,plain,
    ( ~ spl31_89
    | ~ spl31_367
    | ~ spl31_12
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2378,f1423,f359,f2365,f650])).

fof(f359,plain,
    ( spl31_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_12])])).

fof(f2378,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_12
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f2377,f1424])).

fof(f2377,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl31_12
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1181,f1424])).

fof(f1181,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl31_12 ),
    inference(resolution,[],[f305,f360])).

fof(f360,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_12 ),
    inference(avatar_component_clause,[],[f359])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',cc4_subset_1)).

fof(f2376,plain,
    ( ~ spl31_367
    | ~ spl31_89
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2375,f1423,f705,f650,f2365])).

fof(f2375,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f2374,f1424])).

fof(f2374,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_98
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1187,f1424])).

fof(f1187,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl31_98 ),
    inference(resolution,[],[f1179,f706])).

fof(f1179,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X9,X8)
      | ~ v1_subset_1(X9,X8)
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f305,f224])).

fof(f2373,plain,
    ( spl31_88
    | ~ spl31_107
    | ~ spl31_158
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2372,f1906,f1423,f1284,f811,f647])).

fof(f1284,plain,
    ( spl31_158
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_158])])).

fof(f2372,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_158
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f2371,f1424])).

fof(f2371,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_158
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f2370,f1907])).

fof(f2370,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl31_158
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1328,f1424])).

fof(f1328,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl31_158 ),
    inference(resolution,[],[f1285,f205])).

fof(f1285,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl31_158 ),
    inference(avatar_component_clause,[],[f1284])).

fof(f2369,plain,
    ( ~ spl31_89
    | spl31_86
    | ~ spl31_96 ),
    inference(avatar_split_clause,[],[f765,f698,f644,f650])).

fof(f765,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_96 ),
    inference(resolution,[],[f638,f699])).

fof(f2368,plain,
    ( ~ spl31_367
    | ~ spl31_89
    | ~ spl31_4 ),
    inference(avatar_split_clause,[],[f1180,f331,f650,f2365])).

fof(f1180,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl31_4 ),
    inference(resolution,[],[f305,f332])).

fof(f2367,plain,
    ( ~ spl31_89
    | ~ spl31_367
    | ~ spl31_96 ),
    inference(avatar_split_clause,[],[f1186,f698,f2365,f650])).

fof(f1186,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_96 ),
    inference(resolution,[],[f1179,f699])).

fof(f2360,plain,
    ( spl31_102
    | ~ spl31_89
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2359,f1423,f569,f650,f731])).

fof(f2359,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1439,f570])).

fof(f1439,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f248,f1424])).

fof(f248,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',fc2_struct_0)).

fof(f2358,plain,
    ( spl31_88
    | ~ spl31_107
    | ~ spl31_198
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2357,f1906,f1459,f811,f647])).

fof(f1459,plain,
    ( spl31_198
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_198])])).

fof(f2357,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_198
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1558,f1907])).

fof(f1558,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_198 ),
    inference(resolution,[],[f1460,f205])).

fof(f1460,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_198 ),
    inference(avatar_component_clause,[],[f1459])).

fof(f2356,plain,
    ( spl31_106
    | ~ spl31_89
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2355,f1574,f836,f650,f808])).

fof(f2355,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1613,f837])).

fof(f1613,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f248,f1575])).

fof(f2354,plain,
    ( spl31_364
    | spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f2347,f1574,f836,f811,f2352])).

fof(f2347,plain,
    ( m1_subset_1(sK15(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_107
    | ~ spl31_110
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f2346,f812])).

fof(f2345,plain,
    ( spl31_362
    | ~ spl31_70
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2338,f1423,f734,f569,f2343])).

fof(f2338,plain,
    ( m1_subset_1(sK15(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_70
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2337,f735])).

fof(f2336,plain,
    ( ~ spl31_357
    | spl31_360
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2335,f1423,f726,f562,f324,f2328,f2316])).

fof(f2316,plain,
    ( spl31_357
  <=> ~ v3_tex_2(sK15(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_357])])).

fof(f2328,plain,
    ( spl31_360
  <=> v2_tex_2(sK15(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_360])])).

fof(f2335,plain,
    ( v2_tex_2(sK15(sK0),sK1)
    | ~ v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2334,f727])).

fof(f2334,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK15(sK0),sK1)
    | ~ v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2280,f563])).

fof(f2280,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK15(sK0),sK1)
    | ~ v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f243,f1476])).

fof(f2333,plain,
    ( spl31_356
    | spl31_358
    | ~ spl31_361
    | ~ spl31_2
    | ~ spl31_68
    | spl31_101
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2314,f1423,f726,f562,f324,f2331,f2325,f2319])).

fof(f2319,plain,
    ( spl31_356
  <=> v3_tex_2(sK15(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_356])])).

fof(f2325,plain,
    ( spl31_358
  <=> v2_tex_2(sK4(sK1,sK15(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_358])])).

fof(f2314,plain,
    ( ~ v2_tex_2(sK15(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK15(sK0)),sK1)
    | v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2313,f727])).

fof(f2313,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK15(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK15(sK0)),sK1)
    | v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_68
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2279,f563])).

fof(f2279,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK15(sK0),sK1)
    | v2_tex_2(sK4(sK1,sK15(sK0)),sK1)
    | v3_tex_2(sK15(sK0),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f243,f1855])).

fof(f2312,plain,
    ( ~ spl31_351
    | spl31_352
    | ~ spl31_355
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | spl31_101
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2293,f1225,f726,f562,f331,f317,f2310,f2304,f2298])).

fof(f2298,plain,
    ( spl31_351
  <=> ~ v3_tex_2(sK15(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_351])])).

fof(f2304,plain,
    ( spl31_352
  <=> sK3 = sK15(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_352])])).

fof(f2310,plain,
    ( spl31_355
  <=> ~ r1_tarski(sK15(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_355])])).

fof(f2293,plain,
    ( ~ r1_tarski(sK15(sK0),sK3)
    | sK3 = sK15(sK0)
    | ~ v3_tex_2(sK15(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_101
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2292,f727])).

fof(f2292,plain,
    ( v2_struct_0(sK0)
    | ~ r1_tarski(sK15(sK0),sK3)
    | sK3 = sK15(sK0)
    | ~ v3_tex_2(sK15(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_68
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2278,f563])).

fof(f2278,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ r1_tarski(sK15(sK0),sK3)
    | sK3 = sK15(sK0)
    | ~ v3_tex_2(sK15(sK0),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f243,f2079])).

fof(f2271,plain,
    ( ~ spl31_345
    | spl31_346
    | ~ spl31_349
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2098,f1225,f331,f317,f2269,f2263,f2257])).

fof(f2257,plain,
    ( spl31_345
  <=> ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_345])])).

fof(f2263,plain,
    ( spl31_346
  <=> sK3 = sK5(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_346])])).

fof(f2269,plain,
    ( spl31_349
  <=> ~ r1_tarski(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_349])])).

fof(f2098,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK3)
    | sK3 = sK5(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f215])).

fof(f2252,plain,
    ( ~ spl31_339
    | spl31_340
    | ~ spl31_343
    | ~ spl31_0
    | ~ spl31_4
    | spl31_89
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2233,f1225,f650,f331,f317,f2250,f2244,f2238])).

fof(f2238,plain,
    ( spl31_339
  <=> ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_339])])).

fof(f2244,plain,
    ( spl31_340
  <=> sK3 = sK30(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_340])])).

fof(f2250,plain,
    ( spl31_343
  <=> ~ r1_tarski(sK30(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_343])])).

fof(f2233,plain,
    ( ~ r1_tarski(sK30(u1_struct_0(sK0)),sK3)
    | sK3 = sK30(u1_struct_0(sK0))
    | ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_89
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2096,f651])).

fof(f2096,plain,
    ( ~ r1_tarski(sK30(u1_struct_0(sK0)),sK3)
    | sK3 = sK30(u1_struct_0(sK0))
    | ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f306])).

fof(f2232,plain,
    ( ~ spl31_333
    | spl31_334
    | ~ spl31_337
    | ~ spl31_0
    | ~ spl31_4
    | spl31_117
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2213,f1225,f869,f331,f317,f2230,f2224,f2218])).

fof(f2218,plain,
    ( spl31_333
  <=> ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_333])])).

fof(f2224,plain,
    ( spl31_334
  <=> sK3 = sK29(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_334])])).

fof(f2230,plain,
    ( spl31_337
  <=> ~ r1_tarski(sK29(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_337])])).

fof(f2213,plain,
    ( ~ r1_tarski(sK29(u1_struct_0(sK0)),sK3)
    | sK3 = sK29(u1_struct_0(sK0))
    | ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_117
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2095,f870])).

fof(f2095,plain,
    ( ~ r1_tarski(sK29(u1_struct_0(sK0)),sK3)
    | sK3 = sK29(u1_struct_0(sK0))
    | ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f1160])).

fof(f2212,plain,
    ( ~ spl31_327
    | spl31_328
    | ~ spl31_331
    | ~ spl31_0
    | ~ spl31_4
    | spl31_117
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2193,f1225,f869,f331,f317,f2210,f2204,f2198])).

fof(f2198,plain,
    ( spl31_327
  <=> ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_327])])).

fof(f2204,plain,
    ( spl31_328
  <=> sK3 = sK28(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_328])])).

fof(f2210,plain,
    ( spl31_331
  <=> ~ r1_tarski(sK28(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_331])])).

fof(f2193,plain,
    ( ~ r1_tarski(sK28(u1_struct_0(sK0)),sK3)
    | sK3 = sK28(u1_struct_0(sK0))
    | ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_117
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2094,f870])).

fof(f2094,plain,
    ( ~ r1_tarski(sK28(u1_struct_0(sK0)),sK3)
    | sK3 = sK28(u1_struct_0(sK0))
    | ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK0)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f1059])).

fof(f2192,plain,
    ( ~ spl31_321
    | spl31_322
    | ~ spl31_325
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2093,f1225,f331,f317,f2190,f2184,f2178])).

fof(f2178,plain,
    ( spl31_321
  <=> ~ v3_tex_2(sK27(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_321])])).

fof(f2184,plain,
    ( spl31_322
  <=> sK3 = sK27(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_322])])).

fof(f2190,plain,
    ( spl31_325
  <=> ~ r1_tarski(sK27(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_325])])).

fof(f2093,plain,
    ( ~ r1_tarski(sK27(u1_struct_0(sK0)),sK3)
    | sK3 = sK27(u1_struct_0(sK0))
    | ~ v3_tex_2(sK27(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f290])).

fof(f2173,plain,
    ( ~ spl31_315
    | spl31_316
    | ~ spl31_319
    | ~ spl31_0
    | ~ spl31_4
    | spl31_89
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2154,f1225,f650,f331,f317,f2171,f2165,f2159])).

fof(f2159,plain,
    ( spl31_315
  <=> ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_315])])).

fof(f2165,plain,
    ( spl31_316
  <=> sK3 = sK26(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_316])])).

fof(f2171,plain,
    ( spl31_319
  <=> ~ r1_tarski(sK26(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_319])])).

fof(f2154,plain,
    ( ~ r1_tarski(sK26(u1_struct_0(sK0)),sK3)
    | sK3 = sK26(u1_struct_0(sK0))
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_89
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2092,f651])).

fof(f2092,plain,
    ( ~ r1_tarski(sK26(u1_struct_0(sK0)),sK3)
    | sK3 = sK26(u1_struct_0(sK0))
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f286])).

fof(f2153,plain,
    ( ~ spl31_309
    | spl31_310
    | ~ spl31_313
    | ~ spl31_0
    | ~ spl31_4
    | spl31_89
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2134,f1225,f650,f331,f317,f2151,f2145,f2139])).

fof(f2139,plain,
    ( spl31_309
  <=> ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_309])])).

fof(f2145,plain,
    ( spl31_310
  <=> sK3 = sK25(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_310])])).

fof(f2151,plain,
    ( spl31_313
  <=> ~ r1_tarski(sK25(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_313])])).

fof(f2134,plain,
    ( ~ r1_tarski(sK25(u1_struct_0(sK0)),sK3)
    | sK3 = sK25(u1_struct_0(sK0))
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_89
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2091,f651])).

fof(f2091,plain,
    ( ~ r1_tarski(sK25(u1_struct_0(sK0)),sK3)
    | sK3 = sK25(u1_struct_0(sK0))
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f283])).

fof(f2133,plain,
    ( ~ spl31_305
    | spl31_306
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_16
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2120,f1225,f373,f331,f317,f2131,f2125])).

fof(f2125,plain,
    ( spl31_305
  <=> ~ v3_tex_2(sK9,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_305])])).

fof(f2120,plain,
    ( sK3 = sK9
    | ~ v3_tex_2(sK9,sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_16
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2090,f690])).

fof(f2090,plain,
    ( ~ r1_tarski(sK9,sK3)
    | sK3 = sK9
    | ~ v3_tex_2(sK9,sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_16
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f629])).

fof(f2119,plain,
    ( ~ spl31_299
    | spl31_300
    | ~ spl31_303
    | ~ spl31_0
    | ~ spl31_4
    | spl31_89
    | ~ spl31_152 ),
    inference(avatar_split_clause,[],[f2100,f1225,f650,f331,f317,f2117,f2111,f2105])).

fof(f2105,plain,
    ( spl31_299
  <=> ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_299])])).

fof(f2111,plain,
    ( spl31_300
  <=> sK3 = sK7(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_300])])).

fof(f2117,plain,
    ( spl31_303
  <=> ~ r1_tarski(sK7(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_303])])).

fof(f2100,plain,
    ( ~ r1_tarski(sK7(u1_struct_0(sK0)),sK3)
    | sK3 = sK7(u1_struct_0(sK0))
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_89
    | ~ spl31_152 ),
    inference(subsumption_resolution,[],[f2089,f651])).

fof(f2089,plain,
    ( ~ r1_tarski(sK7(u1_struct_0(sK0)),sK3)
    | sK3 = sK7(u1_struct_0(sK0))
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_152 ),
    inference(resolution,[],[f2079,f219])).

fof(f2060,plain,
    ( spl31_294
    | ~ spl31_297
    | ~ spl31_2
    | ~ spl31_4
    | spl31_7
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f2047,f1423,f338,f331,f324,f2058,f2052])).

fof(f2052,plain,
    ( spl31_294
  <=> v2_tex_2(sK4(sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_294])])).

fof(f2047,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v2_tex_2(sK4(sK1,sK3),sK1)
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_7
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f2035,f339])).

fof(f2035,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v2_tex_2(sK4(sK1,sK3),sK1)
    | v3_tex_2(sK3,sK1)
    | ~ spl31_2
    | ~ spl31_4
    | ~ spl31_194 ),
    inference(resolution,[],[f1855,f332])).

fof(f2013,plain,
    ( spl31_222
    | ~ spl31_230
    | ~ spl31_234 ),
    inference(avatar_split_clause,[],[f2012,f1644,f1626,f1591])).

fof(f1591,plain,
    ( spl31_222
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_222])])).

fof(f1626,plain,
    ( spl31_230
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_230])])).

fof(f2012,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 )
    | ~ spl31_230
    | ~ spl31_234 ),
    inference(subsumption_resolution,[],[f2001,f1645])).

fof(f2001,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X3 )
    | ~ spl31_230 ),
    inference(superposition,[],[f208,f1627])).

fof(f1627,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_230 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f2011,plain,
    ( spl31_292
    | ~ spl31_196
    | ~ spl31_198
    | ~ spl31_230
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f2004,f1906,f1626,f1459,f1452,f2009])).

fof(f1452,plain,
    ( spl31_196
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_196])])).

fof(f2004,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_196
    | ~ spl31_198
    | ~ spl31_230
    | ~ spl31_284 ),
    inference(trivial_inequality_removal,[],[f1998])).

fof(f1998,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_196
    | ~ spl31_198
    | ~ spl31_230
    | ~ spl31_284 ),
    inference(superposition,[],[f1909,f1627])).

fof(f1909,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK0) = X3 )
    | ~ spl31_196
    | ~ spl31_198
    | ~ spl31_284 ),
    inference(backward_demodulation,[],[f1907,f1594])).

fof(f1594,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X3 )
    | ~ spl31_196
    | ~ spl31_198 ),
    inference(subsumption_resolution,[],[f1578,f1460])).

fof(f1578,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_pre_topc(sK1) = X3 )
    | ~ spl31_196 ),
    inference(superposition,[],[f208,f1453])).

fof(f1453,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl31_196 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f1954,plain,
    ( spl31_286
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f1953,f1906,f1423,f324,f1923])).

fof(f1953,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1952,f1424])).

fof(f1952,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl31_2
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f1918,f325])).

fof(f1918,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_284 ),
    inference(superposition,[],[f214,f1907])).

fof(f1944,plain,
    ( spl31_288
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f1943,f1906,f1423,f324,f1930])).

fof(f1930,plain,
    ( spl31_288
  <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_288])])).

fof(f1943,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_194
    | ~ spl31_284 ),
    inference(forward_demodulation,[],[f1942,f1424])).

fof(f1942,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_2
    | ~ spl31_284 ),
    inference(subsumption_resolution,[],[f1914,f325])).

fof(f1914,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_284 ),
    inference(superposition,[],[f775,f1907])).

fof(f775,plain,(
    ! [X2] :
      ( r1_tarski(u1_pre_topc(X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f214,f225])).

fof(f1939,plain,
    ( ~ spl31_291
    | spl31_175
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f1912,f1906,f1340,f1937])).

fof(f1937,plain,
    ( spl31_291
  <=> ~ v1_zfmisc_1(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_291])])).

fof(f1340,plain,
    ( spl31_175
  <=> ~ v1_zfmisc_1(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_175])])).

fof(f1912,plain,
    ( ~ v1_zfmisc_1(u1_pre_topc(sK0))
    | ~ spl31_175
    | ~ spl31_284 ),
    inference(backward_demodulation,[],[f1907,f1341])).

fof(f1341,plain,
    ( ~ v1_zfmisc_1(u1_pre_topc(sK1))
    | ~ spl31_175 ),
    inference(avatar_component_clause,[],[f1340])).

fof(f1932,plain,
    ( spl31_288
    | ~ spl31_202
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f1911,f1906,f1473,f1930])).

fof(f1473,plain,
    ( spl31_202
  <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_202])])).

fof(f1911,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_202
    | ~ spl31_284 ),
    inference(backward_demodulation,[],[f1907,f1474])).

fof(f1474,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_202 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1925,plain,
    ( spl31_286
    | ~ spl31_198
    | ~ spl31_284 ),
    inference(avatar_split_clause,[],[f1910,f1906,f1459,f1923])).

fof(f1910,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_198
    | ~ spl31_284 ),
    inference(backward_demodulation,[],[f1907,f1460])).

fof(f1908,plain,
    ( spl31_284
    | ~ spl31_196
    | ~ spl31_198 ),
    inference(avatar_split_clause,[],[f1901,f1459,f1452,f1906])).

fof(f1901,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl31_196
    | ~ spl31_198 ),
    inference(equality_resolution,[],[f1594])).

fof(f1891,plain,
    ( spl31_218
    | ~ spl31_160
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1432,f1423,f1290,f1552])).

fof(f1552,plain,
    ( spl31_218
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_218])])).

fof(f1290,plain,
    ( spl31_160
  <=> ! [X3,X2] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_160])])).

fof(f1432,plain,
    ( ! [X2,X3] :
        ( u1_struct_0(sK0) = X2
        | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) )
    | ~ spl31_160
    | ~ spl31_194 ),
    inference(backward_demodulation,[],[f1424,f1291])).

fof(f1291,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X2 )
    | ~ spl31_160 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f1839,plain,
    ( ~ spl31_281
    | spl31_282
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1716,f1423,f324,f1837,f1831])).

fof(f1831,plain,
    ( spl31_281
  <=> ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_281])])).

fof(f1837,plain,
    ( spl31_282
  <=> v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_282])])).

fof(f1716,plain,
    ( v2_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ v3_tex_2(sK5(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f215])).

fof(f1826,plain,
    ( ~ spl31_277
    | spl31_278
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1813,f1423,f650,f324,f1824,f1818])).

fof(f1818,plain,
    ( spl31_277
  <=> ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_277])])).

fof(f1824,plain,
    ( spl31_278
  <=> v2_tex_2(sK30(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_278])])).

fof(f1813,plain,
    ( v2_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1714,f651])).

fof(f1714,plain,
    ( v2_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK30(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f306])).

fof(f1812,plain,
    ( ~ spl31_273
    | spl31_274
    | ~ spl31_2
    | spl31_117
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1799,f1423,f869,f324,f1810,f1804])).

fof(f1804,plain,
    ( spl31_273
  <=> ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_273])])).

fof(f1810,plain,
    ( spl31_274
  <=> v2_tex_2(sK29(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_274])])).

fof(f1799,plain,
    ( v2_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_117
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1713,f870])).

fof(f1713,plain,
    ( v2_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK29(u1_struct_0(sK0)),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f1160])).

fof(f1798,plain,
    ( ~ spl31_269
    | spl31_270
    | ~ spl31_2
    | spl31_117
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1785,f1423,f869,f324,f1796,f1790])).

fof(f1790,plain,
    ( spl31_269
  <=> ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_269])])).

fof(f1796,plain,
    ( spl31_270
  <=> v2_tex_2(sK28(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_270])])).

fof(f1785,plain,
    ( v2_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_117
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1712,f870])).

fof(f1712,plain,
    ( v2_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK28(u1_struct_0(sK0)),sK1)
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f1059])).

fof(f1784,plain,
    ( ~ spl31_265
    | spl31_266
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1711,f1423,f324,f1782,f1776])).

fof(f1776,plain,
    ( spl31_265
  <=> ~ v3_tex_2(sK27(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_265])])).

fof(f1782,plain,
    ( spl31_266
  <=> v2_tex_2(sK27(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_266])])).

fof(f1711,plain,
    ( v2_tex_2(sK27(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK27(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f290])).

fof(f1771,plain,
    ( ~ spl31_261
    | spl31_262
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1758,f1423,f650,f324,f1769,f1763])).

fof(f1763,plain,
    ( spl31_261
  <=> ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_261])])).

fof(f1769,plain,
    ( spl31_262
  <=> v2_tex_2(sK26(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_262])])).

fof(f1758,plain,
    ( v2_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1710,f651])).

fof(f1710,plain,
    ( v2_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK26(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f286])).

fof(f1757,plain,
    ( ~ spl31_257
    | spl31_258
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1744,f1423,f650,f324,f1755,f1749])).

fof(f1749,plain,
    ( spl31_257
  <=> ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_257])])).

fof(f1755,plain,
    ( spl31_258
  <=> v2_tex_2(sK25(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_258])])).

fof(f1744,plain,
    ( v2_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1709,f651])).

fof(f1709,plain,
    ( v2_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK25(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f283])).

fof(f1743,plain,
    ( ~ spl31_253
    | spl31_254
    | ~ spl31_2
    | ~ spl31_16
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1708,f1423,f373,f324,f1741,f1735])).

fof(f1735,plain,
    ( spl31_253
  <=> ~ v3_tex_2(sK9,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_253])])).

fof(f1741,plain,
    ( spl31_254
  <=> v2_tex_2(sK9,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_254])])).

fof(f1708,plain,
    ( v2_tex_2(sK9,sK1)
    | ~ v3_tex_2(sK9,sK1)
    | ~ spl31_2
    | ~ spl31_16
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f629])).

fof(f1730,plain,
    ( ~ spl31_249
    | spl31_250
    | ~ spl31_2
    | spl31_89
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1717,f1423,f650,f324,f1728,f1722])).

fof(f1722,plain,
    ( spl31_249
  <=> ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_249])])).

fof(f1728,plain,
    ( spl31_250
  <=> v2_tex_2(sK7(u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_250])])).

fof(f1717,plain,
    ( v2_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | ~ spl31_2
    | ~ spl31_89
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1707,f651])).

fof(f1707,plain,
    ( v2_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | ~ v3_tex_2(sK7(u1_struct_0(sK0)),sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(resolution,[],[f1476,f219])).

fof(f1700,plain,
    ( spl31_246
    | ~ spl31_238
    | ~ spl31_240 ),
    inference(avatar_split_clause,[],[f1693,f1669,f1661,f1698])).

fof(f1698,plain,
    ( spl31_246
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_246])])).

fof(f1661,plain,
    ( spl31_238
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_238])])).

fof(f1669,plain,
    ( spl31_240
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_240])])).

fof(f1693,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_238
    | ~ spl31_240 ),
    inference(subsumption_resolution,[],[f1692,f1662])).

fof(f1662,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_238 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f1692,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_240 ),
    inference(resolution,[],[f1670,f213])).

fof(f1670,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_240 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f1691,plain,
    ( spl31_244
    | ~ spl31_238 ),
    inference(avatar_split_clause,[],[f1690,f1661,f1685])).

fof(f1685,plain,
    ( spl31_244
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_244])])).

fof(f1690,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_238 ),
    inference(resolution,[],[f1662,f223])).

fof(f1689,plain,
    ( spl31_234
    | ~ spl31_154
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1688,f1574,f1274,f1644])).

fof(f1274,plain,
    ( spl31_154
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_154])])).

fof(f1688,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_154
    | ~ spl31_220 ),
    inference(forward_demodulation,[],[f1275,f1575])).

fof(f1275,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl31_154 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1687,plain,
    ( spl31_244
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1680,f1574,f828,f1685])).

fof(f1680,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1620,f829])).

fof(f1620,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f821,f1575])).

fof(f821,plain,(
    ! [X0] :
      ( l1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f773,f223])).

fof(f1679,plain,
    ( spl31_242
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1672,f1574,f828,f1677])).

fof(f1677,plain,
    ( spl31_242
  <=> r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_242])])).

fof(f1672,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1619,f829])).

fof(f1619,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f775,f1575])).

fof(f1671,plain,
    ( spl31_240
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1664,f1574,f828,f1669])).

fof(f1664,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1618,f829])).

fof(f1618,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f774,f1575])).

fof(f1663,plain,
    ( spl31_238
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1656,f1574,f828,f1661])).

fof(f1656,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1617,f829])).

fof(f1617,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f773,f1575])).

fof(f1655,plain,
    ( ~ spl31_237
    | ~ spl31_110
    | spl31_117
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1648,f1574,f869,f836,f1653])).

fof(f1648,plain,
    ( ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_110
    | ~ spl31_117
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1647,f837])).

fof(f1647,plain,
    ( ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v7_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_117
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1614,f870])).

fof(f1646,plain,
    ( spl31_234
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1639,f1574,f828,f1644])).

fof(f1639,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1611,f829])).

fof(f1611,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f214,f1575])).

fof(f1638,plain,
    ( ~ spl31_233
    | spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1631,f1574,f828,f811,f1636])).

fof(f1631,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl31_107
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1630,f812])).

fof(f1630,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108
    | ~ spl31_220 ),
    inference(subsumption_resolution,[],[f1610,f829])).

fof(f1610,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_220 ),
    inference(superposition,[],[f211,f1575])).

fof(f1628,plain,
    ( spl31_230
    | ~ spl31_140
    | ~ spl31_220 ),
    inference(avatar_split_clause,[],[f1608,f1574,f1097,f1626])).

fof(f1097,plain,
    ( spl31_140
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_140])])).

fof(f1608,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_140
    | ~ spl31_220 ),
    inference(backward_demodulation,[],[f1575,f1098])).

fof(f1098,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_140 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1606,plain,
    ( ~ spl31_171
    | spl31_228
    | ~ spl31_150 ),
    inference(avatar_split_clause,[],[f1581,f1138,f1604,f1317])).

fof(f1604,plain,
    ( spl31_228
  <=> ! [X9,X8] :
        ( g1_pre_topc(X8,X9) != sK14
        | u1_pre_topc(sK14) = X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_228])])).

fof(f1581,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(X8,X9) != sK14
        | ~ m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))))
        | u1_pre_topc(sK14) = X9 )
    | ~ spl31_150 ),
    inference(superposition,[],[f208,f1139])).

fof(f1602,plain,
    ( ~ spl31_167
    | spl31_226
    | ~ spl31_148 ),
    inference(avatar_split_clause,[],[f1580,f1130,f1600,f1307])).

fof(f1600,plain,
    ( spl31_226
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK13
        | u1_pre_topc(sK13) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_226])])).

fof(f1580,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK13
        | ~ m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))))
        | u1_pre_topc(sK13) = X7 )
    | ~ spl31_148 ),
    inference(superposition,[],[f208,f1131])).

fof(f1598,plain,
    ( ~ spl31_163
    | spl31_224
    | ~ spl31_146 ),
    inference(avatar_split_clause,[],[f1579,f1122,f1596,f1297])).

fof(f1596,plain,
    ( spl31_224
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK12
        | u1_pre_topc(sK12) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_224])])).

fof(f1579,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK12
        | ~ m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12))))
        | u1_pre_topc(sK12) = X5 )
    | ~ spl31_146 ),
    inference(superposition,[],[f208,f1123])).

fof(f1593,plain,
    ( ~ spl31_155
    | spl31_222
    | ~ spl31_140 ),
    inference(avatar_split_clause,[],[f1577,f1097,f1591,f1277])).

fof(f1277,plain,
    ( spl31_155
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_155])])).

fof(f1577,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 )
    | ~ spl31_140 ),
    inference(superposition,[],[f208,f1098])).

fof(f1576,plain,
    ( spl31_220
    | ~ spl31_180
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1569,f1423,f1377,f1574])).

fof(f1377,plain,
    ( spl31_180
  <=> u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_180])])).

fof(f1569,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_180
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1378,f1424])).

fof(f1378,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_180 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1554,plain,
    ( ~ spl31_199
    | spl31_218
    | ~ spl31_196 ),
    inference(avatar_split_clause,[],[f1550,f1452,f1552,f1456])).

fof(f1456,plain,
    ( spl31_199
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_199])])).

fof(f1550,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_struct_0(sK0) = X2 )
    | ~ spl31_196 ),
    inference(superposition,[],[f207,f1453])).

fof(f1547,plain,
    ( spl31_208
    | ~ spl31_202 ),
    inference(avatar_split_clause,[],[f1542,f1473,f1501])).

fof(f1501,plain,
    ( spl31_208
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_208])])).

fof(f1542,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_202 ),
    inference(resolution,[],[f1474,f712])).

fof(f712,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k1_zfmisc_1(X3))
      | v1_pre_topc(g1_pre_topc(X3,X4)) ) ),
    inference(resolution,[],[f209,f224])).

fof(f1546,plain,
    ( spl31_206
    | ~ spl31_202 ),
    inference(avatar_split_clause,[],[f1541,f1473,f1493])).

fof(f1493,plain,
    ( spl31_206
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_206])])).

fof(f1541,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_202 ),
    inference(resolution,[],[f1474,f749])).

fof(f749,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k1_zfmisc_1(X4))
      | l1_pre_topc(g1_pre_topc(X4,X5)) ) ),
    inference(resolution,[],[f210,f224])).

fof(f1540,plain,
    ( ~ spl31_217
    | spl31_191
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1533,f1423,f1407,f1538])).

fof(f1538,plain,
    ( spl31_217
  <=> u1_struct_0(sK0) != u1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_217])])).

fof(f1407,plain,
    ( spl31_191
  <=> u1_struct_0(sK1) != u1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_191])])).

fof(f1533,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK14)
    | ~ spl31_191
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1408,f1424])).

fof(f1408,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK14)
    | ~ spl31_191 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1532,plain,
    ( ~ spl31_215
    | spl31_187
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1525,f1423,f1394,f1530])).

fof(f1530,plain,
    ( spl31_215
  <=> u1_struct_0(sK0) != u1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_215])])).

fof(f1394,plain,
    ( spl31_187
  <=> u1_struct_0(sK1) != u1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_187])])).

fof(f1525,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK13)
    | ~ spl31_187
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1395,f1424])).

fof(f1395,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK13)
    | ~ spl31_187 ),
    inference(avatar_component_clause,[],[f1394])).

fof(f1524,plain,
    ( ~ spl31_213
    | spl31_183
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1517,f1423,f1381,f1522])).

fof(f1522,plain,
    ( spl31_213
  <=> u1_struct_0(sK0) != u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_213])])).

fof(f1381,plain,
    ( spl31_183
  <=> u1_struct_0(sK1) != u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_183])])).

fof(f1517,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK12)
    | ~ spl31_183
    | ~ spl31_194 ),
    inference(forward_demodulation,[],[f1382,f1424])).

fof(f1382,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK12)
    | ~ spl31_183 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f1516,plain,
    ( ~ spl31_201
    | ~ spl31_2
    | spl31_175
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1515,f1423,f1340,f324,f1466])).

fof(f1466,plain,
    ( spl31_201
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_201])])).

fof(f1515,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_175
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1514,f325])).

fof(f1514,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_175
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1447,f1341])).

fof(f1447,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f857,f1424])).

fof(f857,plain,(
    ! [X8] :
      ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8)))
      | v1_zfmisc_1(u1_pre_topc(X8))
      | ~ l1_pre_topc(X8) ) ),
    inference(resolution,[],[f282,f214])).

fof(f1513,plain,
    ( spl31_210
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1506,f1423,f324,f1511])).

fof(f1511,plain,
    ( spl31_210
  <=> l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_210])])).

fof(f1506,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1446,f325])).

fof(f1446,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f821,f1424])).

fof(f1505,plain,
    ( spl31_202
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1504,f1423,f324,f1473])).

fof(f1504,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1445,f325])).

fof(f1445,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f775,f1424])).

fof(f1503,plain,
    ( spl31_208
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1496,f1423,f324,f1501])).

fof(f1496,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1444,f325])).

fof(f1444,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f774,f1424])).

fof(f1495,plain,
    ( spl31_206
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1488,f1423,f324,f1493])).

fof(f1488,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1443,f325])).

fof(f1443,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f773,f1424])).

fof(f1487,plain,
    ( spl31_198
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1486,f1423,f324,f1459])).

fof(f1486,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_2
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1437,f325])).

fof(f1437,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_194 ),
    inference(superposition,[],[f214,f1424])).

fof(f1485,plain,
    ( ~ spl31_205
    | ~ spl31_2
    | spl31_103
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1478,f1423,f734,f324,f1483])).

fof(f1478,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)))
    | ~ spl31_2
    | ~ spl31_103
    | ~ spl31_194 ),
    inference(subsumption_resolution,[],[f1477,f735])).

fof(f1475,plain,
    ( spl31_202
    | ~ spl31_178
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1434,f1423,f1356,f1473])).

fof(f1356,plain,
    ( spl31_178
  <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_178])])).

fof(f1434,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_178
    | ~ spl31_194 ),
    inference(backward_demodulation,[],[f1424,f1357])).

fof(f1357,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_178 ),
    inference(avatar_component_clause,[],[f1356])).

fof(f1468,plain,
    ( ~ spl31_201
    | spl31_177
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1433,f1423,f1349,f1466])).

fof(f1349,plain,
    ( spl31_177
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_177])])).

fof(f1433,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl31_177
    | ~ spl31_194 ),
    inference(backward_demodulation,[],[f1424,f1350])).

fof(f1350,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_177 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1461,plain,
    ( spl31_198
    | ~ spl31_158
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1431,f1423,f1284,f1459])).

fof(f1431,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl31_158
    | ~ spl31_194 ),
    inference(backward_demodulation,[],[f1424,f1285])).

fof(f1454,plain,
    ( spl31_196
    | ~ spl31_10
    | ~ spl31_194 ),
    inference(avatar_split_clause,[],[f1426,f1423,f352,f1452])).

fof(f1426,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl31_10
    | ~ spl31_194 ),
    inference(backward_demodulation,[],[f1424,f353])).

fof(f1425,plain,
    ( spl31_194
    | ~ spl31_160 ),
    inference(avatar_split_clause,[],[f1371,f1290,f1423])).

fof(f1371,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl31_160 ),
    inference(equality_resolution,[],[f1291])).

fof(f1418,plain,
    ( spl31_190
    | ~ spl31_193
    | ~ spl31_150
    | ~ spl31_160 ),
    inference(avatar_split_clause,[],[f1370,f1290,f1138,f1416,f1410])).

fof(f1410,plain,
    ( spl31_190
  <=> u1_struct_0(sK1) = u1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_190])])).

fof(f1416,plain,
    ( spl31_193
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK14 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_193])])).

fof(f1370,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK14
    | u1_struct_0(sK1) = u1_struct_0(sK14)
    | ~ spl31_150
    | ~ spl31_160 ),
    inference(superposition,[],[f1291,f1139])).

fof(f1405,plain,
    ( spl31_186
    | ~ spl31_189
    | ~ spl31_148
    | ~ spl31_160 ),
    inference(avatar_split_clause,[],[f1369,f1290,f1130,f1403,f1397])).

fof(f1397,plain,
    ( spl31_186
  <=> u1_struct_0(sK1) = u1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_186])])).

fof(f1403,plain,
    ( spl31_189
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_189])])).

fof(f1369,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK13
    | u1_struct_0(sK1) = u1_struct_0(sK13)
    | ~ spl31_148
    | ~ spl31_160 ),
    inference(superposition,[],[f1291,f1131])).

fof(f1392,plain,
    ( spl31_182
    | ~ spl31_185
    | ~ spl31_146
    | ~ spl31_160 ),
    inference(avatar_split_clause,[],[f1368,f1290,f1122,f1390,f1384])).

fof(f1384,plain,
    ( spl31_182
  <=> u1_struct_0(sK1) = u1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_182])])).

fof(f1390,plain,
    ( spl31_185
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_185])])).

fof(f1368,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != sK12
    | u1_struct_0(sK1) = u1_struct_0(sK12)
    | ~ spl31_146
    | ~ spl31_160 ),
    inference(superposition,[],[f1291,f1123])).

fof(f1379,plain,
    ( spl31_180
    | ~ spl31_140
    | ~ spl31_160 ),
    inference(avatar_split_clause,[],[f1372,f1290,f1097,f1377])).

fof(f1372,plain,
    ( u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_140
    | ~ spl31_160 ),
    inference(trivial_inequality_removal,[],[f1366])).

fof(f1366,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_140
    | ~ spl31_160 ),
    inference(superposition,[],[f1291,f1098])).

fof(f1358,plain,
    ( spl31_178
    | ~ spl31_158 ),
    inference(avatar_split_clause,[],[f1333,f1284,f1356])).

fof(f1333,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl31_158 ),
    inference(resolution,[],[f1285,f225])).

fof(f1351,plain,
    ( spl31_174
    | ~ spl31_177
    | ~ spl31_158 ),
    inference(avatar_split_clause,[],[f1332,f1284,f1349,f1343])).

fof(f1343,plain,
    ( spl31_174
  <=> v1_zfmisc_1(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_174])])).

fof(f1332,plain,
    ( ~ v1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(u1_pre_topc(sK1))
    | ~ spl31_158 ),
    inference(resolution,[],[f1285,f282])).

fof(f1327,plain,
    ( ~ spl31_2
    | spl31_159 ),
    inference(avatar_contradiction_clause,[],[f1326])).

fof(f1326,plain,
    ( $false
    | ~ spl31_2
    | ~ spl31_159 ),
    inference(subsumption_resolution,[],[f1324,f325])).

fof(f1324,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl31_159 ),
    inference(resolution,[],[f1288,f214])).

fof(f1288,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl31_159 ),
    inference(avatar_component_clause,[],[f1287])).

fof(f1287,plain,
    ( spl31_159
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_159])])).

fof(f1322,plain,
    ( ~ spl31_171
    | spl31_172
    | ~ spl31_150 ),
    inference(avatar_split_clause,[],[f1264,f1138,f1320,f1317])).

fof(f1320,plain,
    ( spl31_172
  <=> ! [X9,X8] :
        ( g1_pre_topc(X8,X9) != sK14
        | u1_struct_0(sK14) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_172])])).

fof(f1264,plain,
    ( ! [X8,X9] :
        ( g1_pre_topc(X8,X9) != sK14
        | ~ m1_subset_1(u1_pre_topc(sK14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))))
        | u1_struct_0(sK14) = X8 )
    | ~ spl31_150 ),
    inference(superposition,[],[f207,f1139])).

fof(f1312,plain,
    ( ~ spl31_167
    | spl31_168
    | ~ spl31_148 ),
    inference(avatar_split_clause,[],[f1263,f1130,f1310,f1307])).

fof(f1310,plain,
    ( spl31_168
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK13
        | u1_struct_0(sK13) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_168])])).

fof(f1263,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK13
        | ~ m1_subset_1(u1_pre_topc(sK13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))))
        | u1_struct_0(sK13) = X6 )
    | ~ spl31_148 ),
    inference(superposition,[],[f207,f1131])).

fof(f1302,plain,
    ( ~ spl31_163
    | spl31_164
    | ~ spl31_146 ),
    inference(avatar_split_clause,[],[f1262,f1122,f1300,f1297])).

fof(f1300,plain,
    ( spl31_164
  <=> ! [X5,X4] :
        ( g1_pre_topc(X4,X5) != sK12
        | u1_struct_0(sK12) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_164])])).

fof(f1262,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(X4,X5) != sK12
        | ~ m1_subset_1(u1_pre_topc(sK12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK12))))
        | u1_struct_0(sK12) = X4 )
    | ~ spl31_146 ),
    inference(superposition,[],[f207,f1123])).

fof(f1292,plain,
    ( ~ spl31_159
    | spl31_160
    | ~ spl31_10 ),
    inference(avatar_split_clause,[],[f1261,f352,f1290,f1287])).

fof(f1261,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X2 )
    | ~ spl31_10 ),
    inference(superposition,[],[f207,f353])).

fof(f1282,plain,
    ( ~ spl31_155
    | spl31_156
    | ~ spl31_140 ),
    inference(avatar_split_clause,[],[f1260,f1097,f1280,f1277])).

fof(f1280,plain,
    ( spl31_156
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_156])])).

fof(f1260,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X0 )
    | ~ spl31_140 ),
    inference(superposition,[],[f207,f1098])).

fof(f1227,plain,
    ( spl31_152
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_8 ),
    inference(avatar_split_clause,[],[f1220,f345,f331,f317,f1225])).

fof(f1220,plain,
    ( v2_tex_2(sK3,sK0)
    | ~ spl31_0
    | ~ spl31_4
    | ~ spl31_8 ),
    inference(subsumption_resolution,[],[f1219,f346])).

fof(f1219,plain,
    ( v2_tex_2(sK3,sK0)
    | ~ v3_tex_2(sK3,sK0)
    | ~ spl31_0
    | ~ spl31_4 ),
    inference(subsumption_resolution,[],[f1206,f318])).

fof(f1206,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK3,sK0)
    | ~ v3_tex_2(sK3,sK0)
    | ~ spl31_4 ),
    inference(resolution,[],[f203,f332])).

fof(f1140,plain,
    ( spl31_150
    | ~ spl31_38
    | ~ spl31_44 ),
    inference(avatar_split_clause,[],[f1133,f471,f450,f1138])).

fof(f450,plain,
    ( spl31_38
  <=> v1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_38])])).

fof(f1133,plain,
    ( g1_pre_topc(u1_struct_0(sK14),u1_pre_topc(sK14)) = sK14
    | ~ spl31_38
    | ~ spl31_44 ),
    inference(subsumption_resolution,[],[f1083,f472])).

fof(f1083,plain,
    ( ~ l1_pre_topc(sK14)
    | g1_pre_topc(u1_struct_0(sK14),u1_pre_topc(sK14)) = sK14
    | ~ spl31_38 ),
    inference(resolution,[],[f213,f451])).

fof(f451,plain,
    ( v1_pre_topc(sK14)
    | ~ spl31_38 ),
    inference(avatar_component_clause,[],[f450])).

fof(f1132,plain,
    ( spl31_148
    | ~ spl31_30
    | ~ spl31_36 ),
    inference(avatar_split_clause,[],[f1125,f443,f422,f1130])).

fof(f422,plain,
    ( spl31_30
  <=> v1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_30])])).

fof(f1125,plain,
    ( g1_pre_topc(u1_struct_0(sK13),u1_pre_topc(sK13)) = sK13
    | ~ spl31_30
    | ~ spl31_36 ),
    inference(subsumption_resolution,[],[f1082,f444])).

fof(f1082,plain,
    ( ~ l1_pre_topc(sK13)
    | g1_pre_topc(u1_struct_0(sK13),u1_pre_topc(sK13)) = sK13
    | ~ spl31_30 ),
    inference(resolution,[],[f213,f423])).

fof(f423,plain,
    ( v1_pre_topc(sK13)
    | ~ spl31_30 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1124,plain,
    ( spl31_146
    | ~ spl31_26
    | ~ spl31_28 ),
    inference(avatar_split_clause,[],[f1117,f415,f408,f1122])).

fof(f408,plain,
    ( spl31_26
  <=> v1_pre_topc(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_26])])).

fof(f1117,plain,
    ( g1_pre_topc(u1_struct_0(sK12),u1_pre_topc(sK12)) = sK12
    | ~ spl31_26
    | ~ spl31_28 ),
    inference(subsumption_resolution,[],[f1081,f416])).

fof(f1081,plain,
    ( ~ l1_pre_topc(sK12)
    | g1_pre_topc(u1_struct_0(sK12),u1_pre_topc(sK12)) = sK12
    | ~ spl31_26 ),
    inference(resolution,[],[f213,f409])).

fof(f409,plain,
    ( v1_pre_topc(sK12)
    | ~ spl31_26 ),
    inference(avatar_component_clause,[],[f408])).

fof(f1116,plain,
    ( spl31_144
    | ~ spl31_20
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f1109,f937,f401,f387,f1114])).

fof(f387,plain,
    ( spl31_20
  <=> v1_pre_topc(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_20])])).

fof(f1109,plain,
    ( g1_pre_topc(sK9,u1_pre_topc(sK11)) = sK11
    | ~ spl31_20
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(forward_demodulation,[],[f1108,f938])).

fof(f1108,plain,
    ( g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11)) = sK11
    | ~ spl31_20
    | ~ spl31_24 ),
    inference(subsumption_resolution,[],[f1080,f402])).

fof(f1080,plain,
    ( ~ l1_pre_topc(sK11)
    | g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11)) = sK11
    | ~ spl31_20 ),
    inference(resolution,[],[f213,f388])).

fof(f388,plain,
    ( v1_pre_topc(sK11)
    | ~ spl31_20 ),
    inference(avatar_component_clause,[],[f387])).

fof(f1107,plain,
    ( spl31_142
    | ~ spl31_128
    | ~ spl31_130 ),
    inference(avatar_split_clause,[],[f1100,f972,f964,f1105])).

fof(f1105,plain,
    ( spl31_142
  <=> g1_pre_topc(sK9,u1_pre_topc(sK11)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11))),u1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_142])])).

fof(f964,plain,
    ( spl31_128
  <=> l1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_128])])).

fof(f972,plain,
    ( spl31_130
  <=> v1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_130])])).

fof(f1100,plain,
    ( g1_pre_topc(sK9,u1_pre_topc(sK11)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11))),u1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11))))
    | ~ spl31_128
    | ~ spl31_130 ),
    inference(subsumption_resolution,[],[f1079,f965])).

fof(f965,plain,
    ( l1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_128 ),
    inference(avatar_component_clause,[],[f964])).

fof(f1079,plain,
    ( ~ l1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | g1_pre_topc(sK9,u1_pre_topc(sK11)) = g1_pre_topc(u1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11))),u1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11))))
    | ~ spl31_130 ),
    inference(resolution,[],[f213,f973])).

fof(f973,plain,
    ( v1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_130 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1099,plain,
    ( spl31_140
    | ~ spl31_108
    | ~ spl31_112 ),
    inference(avatar_split_clause,[],[f1092,f845,f828,f1097])).

fof(f845,plain,
    ( spl31_112
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_112])])).

fof(f1092,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_108
    | ~ spl31_112 ),
    inference(subsumption_resolution,[],[f1078,f829])).

fof(f1078,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl31_112 ),
    inference(resolution,[],[f213,f846])).

fof(f846,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_112 ),
    inference(avatar_component_clause,[],[f845])).

fof(f1022,plain,
    ( ~ spl31_137
    | spl31_138
    | ~ spl31_132 ),
    inference(avatar_split_clause,[],[f1008,f980,f1020,f1014])).

fof(f1014,plain,
    ( spl31_137
  <=> ~ v1_zfmisc_1(k1_zfmisc_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_137])])).

fof(f1020,plain,
    ( spl31_138
  <=> v1_zfmisc_1(u1_pre_topc(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_138])])).

fof(f980,plain,
    ( spl31_132
  <=> r1_tarski(u1_pre_topc(sK11),k1_zfmisc_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_132])])).

fof(f1008,plain,
    ( v1_zfmisc_1(u1_pre_topc(sK11))
    | ~ v1_zfmisc_1(k1_zfmisc_1(sK9))
    | ~ spl31_132 ),
    inference(resolution,[],[f981,f854])).

fof(f981,plain,
    ( r1_tarski(u1_pre_topc(sK11),k1_zfmisc_1(sK9))
    | ~ spl31_132 ),
    inference(avatar_component_clause,[],[f980])).

fof(f992,plain,
    ( spl31_134
    | ~ spl31_128 ),
    inference(avatar_split_clause,[],[f991,f964,f988])).

fof(f988,plain,
    ( spl31_134
  <=> l1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_134])])).

fof(f991,plain,
    ( l1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_128 ),
    inference(resolution,[],[f965,f223])).

fof(f990,plain,
    ( spl31_134
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f983,f937,f401,f988])).

fof(f983,plain,
    ( l1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f950,f402])).

fof(f950,plain,
    ( l1_struct_0(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f821,f938])).

fof(f982,plain,
    ( spl31_132
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f975,f937,f401,f980])).

fof(f975,plain,
    ( r1_tarski(u1_pre_topc(sK11),k1_zfmisc_1(sK9))
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f949,f402])).

fof(f949,plain,
    ( r1_tarski(u1_pre_topc(sK11),k1_zfmisc_1(sK9))
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f775,f938])).

fof(f974,plain,
    ( spl31_130
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f967,f937,f401,f972])).

fof(f967,plain,
    ( v1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f948,f402])).

fof(f948,plain,
    ( v1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f774,f938])).

fof(f966,plain,
    ( spl31_128
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f959,f937,f401,f964])).

fof(f959,plain,
    ( l1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f947,f402])).

fof(f947,plain,
    ( l1_pre_topc(g1_pre_topc(sK9,u1_pre_topc(sK11)))
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f773,f938])).

fof(f958,plain,
    ( spl31_126
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(avatar_split_clause,[],[f951,f937,f401,f956])).

fof(f951,plain,
    ( m1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(k1_zfmisc_1(sK9)))
    | ~ spl31_24
    | ~ spl31_124 ),
    inference(subsumption_resolution,[],[f941,f402])).

fof(f941,plain,
    ( m1_subset_1(u1_pre_topc(sK11),k1_zfmisc_1(k1_zfmisc_1(sK9)))
    | ~ l1_pre_topc(sK11)
    | ~ spl31_124 ),
    inference(superposition,[],[f214,f938])).

fof(f939,plain,
    ( spl31_124
    | ~ spl31_16
    | ~ spl31_22
    | ~ spl31_74 ),
    inference(avatar_split_clause,[],[f932,f583,f394,f373,f937])).

fof(f394,plain,
    ( spl31_22
  <=> v2_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_22])])).

fof(f583,plain,
    ( spl31_74
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_74])])).

fof(f932,plain,
    ( u1_struct_0(sK11) = sK9
    | ~ spl31_16
    | ~ spl31_22
    | ~ spl31_74 ),
    inference(subsumption_resolution,[],[f931,f584])).

fof(f584,plain,
    ( l1_struct_0(sK11)
    | ~ spl31_74 ),
    inference(avatar_component_clause,[],[f583])).

fof(f931,plain,
    ( ~ l1_struct_0(sK11)
    | u1_struct_0(sK11) = sK9
    | ~ spl31_16
    | ~ spl31_22 ),
    inference(resolution,[],[f718,f395])).

fof(f395,plain,
    ( v2_struct_0(sK11)
    | ~ spl31_22 ),
    inference(avatar_component_clause,[],[f394])).

fof(f718,plain,
    ( ! [X1] :
        ( ~ v2_struct_0(X1)
        | ~ l1_struct_0(X1)
        | u1_struct_0(X1) = sK9 )
    | ~ spl31_16 ),
    inference(resolution,[],[f242,f625])).

fof(f898,plain,
    ( ~ spl31_123
    | ~ spl31_70
    | spl31_119 ),
    inference(avatar_split_clause,[],[f891,f876,f569,f896])).

fof(f891,plain,
    ( ~ v7_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_119 ),
    inference(subsumption_resolution,[],[f890,f570])).

fof(f890,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v7_struct_0(sK1)
    | ~ spl31_119 ),
    inference(resolution,[],[f877,f256])).

fof(f888,plain,
    ( ~ spl31_121
    | ~ spl31_68
    | spl31_117 ),
    inference(avatar_split_clause,[],[f881,f869,f562,f886])).

fof(f881,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_117 ),
    inference(subsumption_resolution,[],[f880,f563])).

fof(f880,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl31_117 ),
    inference(resolution,[],[f870,f256])).

fof(f878,plain,
    ( spl31_114
    | ~ spl31_119
    | ~ spl31_12 ),
    inference(avatar_split_clause,[],[f856,f359,f876,f863])).

fof(f856,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK1))
    | v1_zfmisc_1(sK3)
    | ~ spl31_12 ),
    inference(resolution,[],[f282,f360])).

fof(f871,plain,
    ( spl31_114
    | ~ spl31_117
    | ~ spl31_4 ),
    inference(avatar_split_clause,[],[f855,f331,f869,f863])).

fof(f855,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_zfmisc_1(sK3)
    | ~ spl31_4 ),
    inference(resolution,[],[f282,f332])).

fof(f847,plain,
    ( spl31_112
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(avatar_split_clause,[],[f840,f352,f324,f845])).

fof(f840,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(subsumption_resolution,[],[f839,f325])).

fof(f839,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_10 ),
    inference(superposition,[],[f774,f353])).

fof(f838,plain,
    ( spl31_110
    | ~ spl31_108 ),
    inference(avatar_split_clause,[],[f831,f828,f836])).

fof(f831,plain,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_108 ),
    inference(resolution,[],[f829,f223])).

fof(f830,plain,
    ( spl31_108
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(avatar_split_clause,[],[f823,f352,f324,f828])).

fof(f823,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_2
    | ~ spl31_10 ),
    inference(subsumption_resolution,[],[f822,f325])).

fof(f822,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl31_10 ),
    inference(superposition,[],[f773,f353])).

fof(f813,plain,
    ( ~ spl31_107
    | ~ spl31_2
    | ~ spl31_10
    | spl31_103 ),
    inference(avatar_split_clause,[],[f806,f734,f352,f324,f811])).

fof(f806,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl31_2
    | ~ spl31_10
    | ~ spl31_103 ),
    inference(subsumption_resolution,[],[f805,f735])).

fof(f799,plain,
    ( spl31_104
    | ~ spl31_16 ),
    inference(avatar_split_clause,[],[f791,f373,f797])).

fof(f791,plain,
    ( sK5(k1_zfmisc_1(sK9)) = sK9
    | ~ spl31_16 ),
    inference(resolution,[],[f663,f374])).

fof(f736,plain,
    ( ~ spl31_103
    | ~ spl31_70
    | spl31_91 ),
    inference(avatar_split_clause,[],[f729,f657,f569,f734])).

fof(f729,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl31_70
    | ~ spl31_91 ),
    inference(subsumption_resolution,[],[f716,f570])).

fof(f716,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v2_struct_0(sK1)
    | ~ spl31_91 ),
    inference(resolution,[],[f242,f658])).

fof(f728,plain,
    ( ~ spl31_101
    | ~ spl31_68
    | spl31_89 ),
    inference(avatar_split_clause,[],[f721,f650,f562,f726])).

fof(f721,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl31_68
    | ~ spl31_89 ),
    inference(subsumption_resolution,[],[f715,f563])).

fof(f715,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v2_struct_0(sK0)
    | ~ spl31_89 ),
    inference(resolution,[],[f242,f651])).

fof(f707,plain,
    ( spl31_98
    | ~ spl31_12 ),
    inference(avatar_split_clause,[],[f688,f359,f705])).

fof(f688,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1))
    | ~ spl31_12 ),
    inference(resolution,[],[f225,f360])).

fof(f700,plain,
    ( spl31_96
    | ~ spl31_4 ),
    inference(avatar_split_clause,[],[f687,f331,f698])).

fof(f687,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl31_4 ),
    inference(resolution,[],[f225,f332])).

fof(f686,plain,
    ( ~ spl31_95
    | ~ spl31_92 ),
    inference(avatar_split_clause,[],[f679,f673,f684])).

fof(f684,plain,
    ( spl31_95
  <=> ~ v1_subset_1(sK9,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_95])])).

fof(f673,plain,
    ( spl31_92
  <=> sK9 = sK27(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_92])])).

fof(f679,plain,
    ( ~ v1_subset_1(sK9,sK9)
    | ~ spl31_92 ),
    inference(superposition,[],[f291,f674])).

fof(f674,plain,
    ( sK9 = sK27(sK9)
    | ~ spl31_92 ),
    inference(avatar_component_clause,[],[f673])).

fof(f675,plain,
    ( spl31_92
    | ~ spl31_16 ),
    inference(avatar_split_clause,[],[f666,f373,f673])).

fof(f666,plain,
    ( sK9 = sK27(sK9)
    | ~ spl31_16 ),
    inference(resolution,[],[f660,f374])).

fof(f659,plain,
    ( spl31_86
    | ~ spl31_91
    | ~ spl31_12 ),
    inference(avatar_split_clause,[],[f634,f359,f657,f644])).

fof(f634,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK3)
    | ~ spl31_12 ),
    inference(resolution,[],[f218,f360])).

fof(f652,plain,
    ( spl31_86
    | ~ spl31_89
    | ~ spl31_4 ),
    inference(avatar_split_clause,[],[f633,f331,f650,f644])).

fof(f633,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3)
    | ~ spl31_4 ),
    inference(resolution,[],[f218,f332])).

fof(f624,plain,
    ( spl31_84
    | ~ spl31_22
    | ~ spl31_74 ),
    inference(avatar_split_clause,[],[f617,f583,f394,f622])).

fof(f622,plain,
    ( spl31_84
  <=> v7_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_84])])).

fof(f617,plain,
    ( v7_struct_0(sK11)
    | ~ spl31_22
    | ~ spl31_74 ),
    inference(subsumption_resolution,[],[f616,f584])).

fof(f616,plain,
    ( ~ l1_struct_0(sK11)
    | v7_struct_0(sK11)
    | ~ spl31_22 ),
    inference(resolution,[],[f274,f395])).

fof(f615,plain,
    ( spl31_82
    | ~ spl31_16 ),
    inference(avatar_split_clause,[],[f607,f373,f613])).

fof(f613,plain,
    ( spl31_82
  <=> v1_zfmisc_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_82])])).

fof(f607,plain,
    ( v1_zfmisc_1(sK9)
    | ~ spl31_16 ),
    inference(resolution,[],[f280,f374])).

fof(f606,plain,
    ( spl31_80
    | ~ spl31_44 ),
    inference(avatar_split_clause,[],[f557,f471,f604])).

fof(f604,plain,
    ( spl31_80
  <=> l1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_80])])).

fof(f557,plain,
    ( l1_struct_0(sK14)
    | ~ spl31_44 ),
    inference(resolution,[],[f223,f472])).

fof(f599,plain,
    ( spl31_78
    | ~ spl31_36 ),
    inference(avatar_split_clause,[],[f556,f443,f597])).

fof(f597,plain,
    ( spl31_78
  <=> l1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_78])])).

fof(f556,plain,
    ( l1_struct_0(sK13)
    | ~ spl31_36 ),
    inference(resolution,[],[f223,f444])).

fof(f592,plain,
    ( spl31_76
    | ~ spl31_28 ),
    inference(avatar_split_clause,[],[f555,f415,f590])).

fof(f590,plain,
    ( spl31_76
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_76])])).

fof(f555,plain,
    ( l1_struct_0(sK12)
    | ~ spl31_28 ),
    inference(resolution,[],[f223,f416])).

fof(f585,plain,
    ( spl31_74
    | ~ spl31_24 ),
    inference(avatar_split_clause,[],[f554,f401,f583])).

fof(f554,plain,
    ( l1_struct_0(sK11)
    | ~ spl31_24 ),
    inference(resolution,[],[f223,f402])).

fof(f578,plain,
    ( spl31_72
    | ~ spl31_14 ),
    inference(avatar_split_clause,[],[f553,f366,f576])).

fof(f576,plain,
    ( spl31_72
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_72])])).

fof(f553,plain,
    ( l1_struct_0(sK8)
    | ~ spl31_14 ),
    inference(resolution,[],[f223,f367])).

fof(f571,plain,
    ( spl31_70
    | ~ spl31_2 ),
    inference(avatar_split_clause,[],[f552,f324,f569])).

fof(f552,plain,
    ( l1_struct_0(sK1)
    | ~ spl31_2 ),
    inference(resolution,[],[f223,f325])).

fof(f564,plain,
    ( spl31_68
    | ~ spl31_0 ),
    inference(avatar_split_clause,[],[f551,f317,f562])).

fof(f551,plain,
    ( l1_struct_0(sK0)
    | ~ spl31_0 ),
    inference(resolution,[],[f223,f318])).

fof(f550,plain,(
    ~ spl31_67 ),
    inference(avatar_split_clause,[],[f278,f548])).

fof(f548,plain,
    ( spl31_67
  <=> ~ v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_67])])).

fof(f278,plain,(
    ~ v1_xboole_0(sK24) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc2_realset1)).

fof(f543,plain,(
    ~ spl31_65 ),
    inference(avatar_split_clause,[],[f279,f541])).

fof(f541,plain,
    ( spl31_65
  <=> ~ v1_zfmisc_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_65])])).

fof(f279,plain,(
    ~ v1_zfmisc_1(sK24) ),
    inference(cnf_transformation,[],[f86])).

fof(f536,plain,(
    ~ spl31_63 ),
    inference(avatar_split_clause,[],[f276,f534])).

fof(f534,plain,
    ( spl31_63
  <=> ~ v1_xboole_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_63])])).

fof(f276,plain,(
    ~ v1_xboole_0(sK23) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_realset1)).

fof(f529,plain,(
    spl31_60 ),
    inference(avatar_split_clause,[],[f277,f527])).

fof(f527,plain,
    ( spl31_60
  <=> v1_zfmisc_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_60])])).

fof(f277,plain,(
    v1_zfmisc_1(sK23) ),
    inference(cnf_transformation,[],[f78])).

fof(f522,plain,(
    spl31_58 ),
    inference(avatar_split_clause,[],[f253,f520])).

fof(f520,plain,
    ( spl31_58
  <=> l1_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_58])])).

fof(f253,plain,(
    l1_struct_0(sK19) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc10_struct_0)).

fof(f515,plain,(
    ~ spl31_57 ),
    inference(avatar_split_clause,[],[f254,f513])).

fof(f513,plain,
    ( spl31_57
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_57])])).

fof(f254,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f74])).

fof(f508,plain,(
    ~ spl31_55 ),
    inference(avatar_split_clause,[],[f255,f506])).

fof(f506,plain,
    ( spl31_55
  <=> ~ v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_55])])).

fof(f255,plain,(
    ~ v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f74])).

fof(f501,plain,(
    spl31_52 ),
    inference(avatar_split_clause,[],[f250,f499])).

fof(f499,plain,
    ( spl31_52
  <=> l1_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_52])])).

fof(f250,plain,(
    l1_struct_0(sK18) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc9_struct_0)).

fof(f494,plain,(
    ~ spl31_51 ),
    inference(avatar_split_clause,[],[f251,f492])).

fof(f492,plain,
    ( spl31_51
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_51])])).

fof(f251,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f105])).

fof(f487,plain,(
    spl31_48 ),
    inference(avatar_split_clause,[],[f252,f485])).

fof(f485,plain,
    ( spl31_48
  <=> v7_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_48])])).

fof(f252,plain,(
    v7_struct_0(sK18) ),
    inference(cnf_transformation,[],[f105])).

fof(f480,plain,(
    spl31_46 ),
    inference(avatar_split_clause,[],[f249,f478])).

fof(f478,plain,
    ( spl31_46
  <=> l1_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_46])])).

fof(f249,plain,(
    l1_struct_0(sK17) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',existence_l1_struct_0)).

fof(f473,plain,(
    spl31_44 ),
    inference(avatar_split_clause,[],[f238,f471])).

fof(f238,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc2_tex_1)).

fof(f466,plain,(
    ~ spl31_43 ),
    inference(avatar_split_clause,[],[f239,f464])).

fof(f464,plain,
    ( spl31_43
  <=> ~ v2_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_43])])).

fof(f239,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f89])).

fof(f459,plain,(
    ~ spl31_41 ),
    inference(avatar_split_clause,[],[f240,f457])).

fof(f457,plain,
    ( spl31_41
  <=> ~ v7_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_41])])).

fof(f240,plain,(
    ~ v7_struct_0(sK14) ),
    inference(cnf_transformation,[],[f89])).

fof(f452,plain,(
    spl31_38 ),
    inference(avatar_split_clause,[],[f241,f450])).

fof(f241,plain,(
    v1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f89])).

fof(f445,plain,(
    spl31_36 ),
    inference(avatar_split_clause,[],[f234,f443])).

fof(f234,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_tex_1)).

fof(f438,plain,(
    ~ spl31_35 ),
    inference(avatar_split_clause,[],[f235,f436])).

fof(f436,plain,
    ( spl31_35
  <=> ~ v2_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_35])])).

fof(f235,plain,(
    ~ v2_struct_0(sK13) ),
    inference(cnf_transformation,[],[f81])).

fof(f431,plain,(
    spl31_32 ),
    inference(avatar_split_clause,[],[f236,f429])).

fof(f429,plain,
    ( spl31_32
  <=> v7_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_32])])).

fof(f236,plain,(
    v7_struct_0(sK13) ),
    inference(cnf_transformation,[],[f81])).

fof(f424,plain,(
    spl31_30 ),
    inference(avatar_split_clause,[],[f237,f422])).

fof(f237,plain,(
    v1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f81])).

fof(f417,plain,(
    spl31_28 ),
    inference(avatar_split_clause,[],[f232,f415])).

fof(f232,plain,(
    l1_pre_topc(sK12) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_pre_topc)).

fof(f410,plain,(
    spl31_26 ),
    inference(avatar_split_clause,[],[f233,f408])).

fof(f233,plain,(
    v1_pre_topc(sK12) ),
    inference(cnf_transformation,[],[f77])).

fof(f403,plain,(
    spl31_24 ),
    inference(avatar_split_clause,[],[f229,f401])).

fof(f229,plain,(
    l1_pre_topc(sK11) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc11_pre_topc)).

fof(f396,plain,(
    spl31_22 ),
    inference(avatar_split_clause,[],[f230,f394])).

fof(f230,plain,(
    v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f75])).

fof(f389,plain,(
    spl31_20 ),
    inference(avatar_split_clause,[],[f231,f387])).

fof(f231,plain,(
    v1_pre_topc(sK11) ),
    inference(cnf_transformation,[],[f75])).

fof(f382,plain,(
    ~ spl31_19 ),
    inference(avatar_split_clause,[],[f228,f380])).

fof(f380,plain,
    ( spl31_19
  <=> ~ v1_xboole_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_19])])).

fof(f228,plain,(
    ~ v1_xboole_0(sK10) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc2_xboole_0)).

fof(f375,plain,(
    spl31_16 ),
    inference(avatar_split_clause,[],[f227,f373])).

fof(f227,plain,(
    v1_xboole_0(sK9) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',rc1_xboole_0)).

fof(f368,plain,(
    spl31_14 ),
    inference(avatar_split_clause,[],[f222,f366])).

fof(f222,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',existence_l1_pre_topc)).

fof(f361,plain,(
    spl31_12 ),
    inference(avatar_split_clause,[],[f190,f359])).

fof(f190,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f115])).

fof(f115,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t45_tex_2.p',t45_tex_2)).

fof(f354,plain,(
    spl31_10 ),
    inference(avatar_split_clause,[],[f191,f352])).

fof(f191,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f116])).

fof(f347,plain,(
    spl31_8 ),
    inference(avatar_split_clause,[],[f311,f345])).

fof(f311,plain,(
    v3_tex_2(sK3,sK0) ),
    inference(definition_unfolding,[],[f193,f192])).

fof(f192,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f116])).

fof(f193,plain,(
    v3_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f116])).

fof(f340,plain,(
    ~ spl31_7 ),
    inference(avatar_split_clause,[],[f194,f338])).

fof(f194,plain,(
    ~ v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f116])).

fof(f333,plain,(
    spl31_4 ),
    inference(avatar_split_clause,[],[f310,f331])).

fof(f310,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f195,f192])).

fof(f195,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f116])).

fof(f326,plain,(
    spl31_2 ),
    inference(avatar_split_clause,[],[f196,f324])).

fof(f196,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f116])).

fof(f319,plain,(
    spl31_0 ),
    inference(avatar_split_clause,[],[f197,f317])).

fof(f197,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f116])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t95_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:22 EDT 2019

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       : 4104 (21016 expanded)
%              Number of leaves         : 1047 (8344 expanded)
%              Depth                    :   17
%              Number of atoms          : 13132 (57730 expanded)
%              Number of equality atoms : 1677 (7373 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :   21 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f160,f167,f174,f181,f188,f195,f202,f209,f216,f225,f232,f240,f248,f260,f268,f278,f288,f298,f308,f318,f328,f338,f348,f360,f370,f379,f388,f398,f418,f440,f449,f456,f465,f472,f481,f488,f497,f504,f513,f520,f528,f540,f549,f558,f568,f577,f586,f597,f609,f616,f625,f634,f647,f658,f667,f686,f695,f705,f719,f721,f734,f746,f757,f766,f775,f782,f791,f800,f811,f822,f833,f844,f867,f884,f887,f903,f913,f920,f929,f942,f951,f960,f969,f976,f985,f994,f1005,f1027,f1042,f1051,f1066,f1079,f1095,f1110,f1125,f1134,f1149,f1152,f1162,f1173,f1189,f1198,f1206,f1243,f1252,f1263,f1280,f1291,f1302,f1312,f1328,f1341,f1351,f1360,f1379,f1394,f1403,f1413,f1420,f1430,f1439,f1450,f1462,f1504,f1514,f1521,f1531,f1538,f1545,f1552,f1559,f1568,f1579,f1591,f1594,f1612,f1626,f1637,f1648,f1662,f1679,f1686,f1703,f1713,f1724,f1742,f1758,f1768,f1778,f1787,f1794,f1801,f1812,f1819,f1830,f1840,f1849,f1865,f1876,f1887,f1945,f1955,f1971,f1981,f1991,f2009,f2019,f2114,f2127,f2140,f2147,f2159,f2170,f2183,f2199,f2216,f2221,f2234,f2285,f2321,f2328,f2341,f2360,f2367,f2388,f2397,f2409,f2430,f2448,f2455,f2462,f2546,f2556,f2566,f2582,f2599,f2609,f2620,f2632,f2702,f2717,f2729,f2741,f2754,f2767,f2776,f2783,f2790,f2797,f2810,f2826,f2851,f2873,f2886,f2902,f2918,f2937,f3132,f3139,f3146,f3153,f3160,f3173,f3180,f3196,f3230,f3247,f3257,f3264,f3270,f3280,f3289,f3314,f3321,f3335,f3352,f3365,f3387,f3400,f3407,f3416,f3423,f3436,f3442,f3449,f3458,f3465,f3472,f3479,f3486,f3493,f3500,f3507,f3522,f3532,f3547,f3559,f3574,f3584,f3597,f3613,f3629,f3642,f3646,f3648,f3655,f3666,f3681,f3693,f3788,f3801,f3812,f3822,f3835,f3847,f3867,f3877,f3884,f3891,f3898,f3905,f3918,f3927,f3940,f3954,f3966,f4024,f4048,f4055,f4067,f4083,f4090,f4097,f4104,f4129,f4148,f4157,f4164,f4171,f4191,f4200,f4202,f4205,f4215,f4250,f4261,f4271,f4292,f4305,f4315,f4328,f4335,f4342,f4351,f4366,f4385,f4388,f4395,f4410,f4422,f4433,f4435,f4495,f4505,f4597,f4619,f4630,f4639,f4655,f4674,f4692,f4703,f4723,f4735,f4753,f4760,f4761,f4771,f4787,f4791,f4798,f4808,f4824,f4831,f4843,f4854,f4861,f4873,f4880,f4898,f4907,f4925,f4936,f4948,f5048,f5050,f5075,f5077,f5092,f5107,f5111,f5126,f5140,f5148,f5151,f5177,f5185,f5188,f5281,f5288,f5299,f5301,f5337,f5418,f5454,f5458,f5465,f5484,f5492,f5495,f5533,f5540,f5547,f5551,f5568,f5612,f5619,f5628,f5635,f5640,f5647,f5654,f5666,f5673,f5689,f5696,f5703,f5715,f5722,f5729,f5736,f5740,f5757,f5840,f5873,f5898,f5982,f6018,f6025,f6032,f6061,f6070,f6077,f6084,f6094,f6100,f6119,f6126,f6133,f6140,f6147,f6154,f6161,f6168,f6175,f6186,f6196,f6203,f6210,f6217,f6224,f6231,f6238,f6245,f6252,f6269,f6279,f6282,f6307,f6315,f6318,f6336,f6417,f6459,f6488,f6496,f6504,f6511,f6522,f6529,f6536,f6554,f6576,f6597,f6604,f6605,f6606,f6699,f6741,f6868,f6898,f6906,f6913,f6951,f6958,f6997,f7017,f7035,f7076,f7083,f7090,f7097,f7104,f7111,f7118,f7128,f7135,f7142,f7149,f7156,f7165,f7172,f7179,f7268,f7275,f7319,f7326,f7333,f7340,f7347,f7356,f7363,f7370,f7377,f7463,f7491,f7500,f7501,f7522,f7538,f7568,f7597,f7645,f7661,f7668,f7698,f7759,f7760,f7776,f7808,f7838,f7867,f7875,f7882,f7908,f7915,f7922,f7947,f7957,f7967,f7980,f7987,f8012,f8027,f8038,f8045,f8069,f8093,f8100,f8107,f8114,f8121,f8128,f8132,f8133,f8140,f8147,f8151,f8152,f8153,f8154,f8155,f8162,f8170,f8200,f8219,f8276,f8300,f8315,f8322,f8351,f8367,f8374,f8378,f8380,f8401,f8402,f8409,f8416,f8423,f8451,f8459,f8462,f8580,f8587,f8594,f8643,f8650,f8657,f8664,f8676,f8683,f8690,f8697,f8704,f8711,f8718,f8723,f8738,f8745,f8752,f8759,f8782,f8792,f8824,f8831,f8838,f8846,f8856,f8864,f8902,f8909,f8913,f8949,f9015,f9016,f9043,f9050,f9086,f9348,f9350,f9384,f9402,f9410,f9425,f9487,f9499,f9503,f9527,f9535,f9542,f9657,f9664,f9680,f9694,f9701,f9708,f9863,f9992,f9999,f10001,f10028,f10035,f10045,f10055,f10059,f10063,f10067,f10091,f10098,f10105,f10128,f10156,f10162,f10165,f10169,f10170,f10177,f10184,f10191,f10198,f10202,f10203,f10210,f10217,f10224,f10231,f10235,f10239,f10240,f10241,f10248,f10255,f10256,f10266,f10276,f10290,f10297,f10304,f10308,f10332,f10333,f10340,f10351,f10414,f10421,f10428,f10429,f10553,f10560,f10618,f10747,f10753,f10762,f10916,f10917,f10918,f10919,f10940,f10947,f10964,f10979,f10986,f10993,f11004,f11011,f11077,f11166,f11170,f11180,f11214,f11248,f11275,f11296,f11300,f11468,f11518,f11528,f11560,f11562,f11569,f11613,f11678,f11679,f11698,f11705,f11712,f11719,f11726,f11739,f11764,f11771,f11778,f11787,f11794,f11839,f11846,f11853,f11860,f11927,f11934,f11941,f11948,f11955,f11962,f11969,f11976,f12006,f12011,f12025,f12080,f12091,f12098,f12105,f12112,f12125,f12169,f12217,f12224,f12252,f12259,f12266,f12273,f12305,f12330,f12337,f12344,f12373,f12380,f12413,f12420,f12421,f12422,f12423,f12494,f12501,f12538,f12564,f12571,f12578,f12580,f12589,f12596,f12603,f12611,f12643,f12651,f12658,f12705,f12712,f12766,f12773,f12780,f12787,f12794,f12802,f12809,f12816,f12827,f12834,f12969,f12976,f13034,f13041,f13176,f13183,f13241,f13248,f13259,f13266,f13273,f13301,f13308,f13315,f13322,f13329,f13336,f13343,f13350,f13361,f13368,f13375,f13382,f13415,f13423,f13431,f13438,f13445,f13452,f13469,f13506,f13556,f13563,f13593,f13611,f13756,f13763,f13770,f13777,f13809,f13838,f13845,f13852,f13859,f13860,f13861,f13868,f13872,f13879,f13883,f13927,f13928,f13929,f13930,f13931,f13932,f13933,f13940,f13947,f13954,f13962,f14004,f14005,f14038,f14071,f14168,f14175,f14177,f14184,f14203,f14222,f14229,f14236,f14304,f14317,f14324,f14334,f14341,f14348,f14355,f14357,f14364,f14400,f14431,f14438,f14445,f14453,f14562,f14611,f14618,f14625,f14632,f14642,f14651,f14664,f14671,f14678,f14743,f14774,f14784,f14800,f14814,f14838,f14845,f14852,f14877,f14989,f14996,f15003,f15016,f15023,f15073,f15113,f15121,f15131,f15149,f15168,f15181,f15202,f15209,f15214,f15218,f15231,f15268,f15327,f15330,f15368,f15375,f15399,f15406,f15407,f15417,f15454,f15544,f15575,f15607,f15614,f15690,f15707])).

fof(f15707,plain,
    ( ~ spl7_153
    | spl7_1848
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_82
    | ~ spl7_266
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f15696,f5040,f1529,f518,f200,f165,f158,f151,f15705,f882])).

fof(f882,plain,
    ( spl7_153
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f15705,plain,
    ( spl7_1848
  <=> k4_tmap_1(sK0,sK1) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1848])])).

fof(f151,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f158,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f165,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f200,plain,
    ( spl7_14
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f518,plain,
    ( spl7_82
  <=> m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f1529,plain,
    ( spl7_266
  <=> k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_266])])).

fof(f5040,plain,
    ( spl7_788
  <=> v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_788])])).

fof(f15696,plain,
    ( k4_tmap_1(sK0,sK1) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_82
    | ~ spl7_266
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f15695,f1530])).

fof(f1530,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl7_266 ),
    inference(avatar_component_clause,[],[f1529])).

fof(f15695,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_82
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f15694,f4971])).

fof(f4971,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),X0) = k7_relat_1(k3_struct_0(sK0),X0)
    | ~ spl7_4 ),
    inference(resolution,[],[f4970,f166])).

fof(f166,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f4970,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X0),k3_struct_0(X0),X1) = k7_relat_1(k3_struct_0(X0),X1) ) ),
    inference(subsumption_resolution,[],[f4952,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_l1_pre_topc)).

fof(f4952,plain,(
    ! [X0,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X0),k3_struct_0(X0),X1) = k7_relat_1(k3_struct_0(X0),X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f2985,f112])).

fof(f112,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k3_struct_0)).

fof(f2985,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(k3_struct_0(X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_partfun1(X3,X4,k3_struct_0(X5),X6) = k7_relat_1(k3_struct_0(X5),X6)
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f1265,f114])).

fof(f1265,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ l1_struct_0(X5)
      | k2_partfun1(X6,X7,k3_struct_0(X5),X8) = k7_relat_1(k3_struct_0(X5),X8)
      | ~ m1_subset_1(k3_struct_0(X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f140,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',redefinition_k2_partfun1)).

fof(f15694,plain,
    ( k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_82
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f15693,f519])).

fof(f519,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f518])).

fof(f15693,plain,
    ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f15691,f5041])).

fof(f5041,plain,
    ( v1_funct_1(k3_struct_0(sK0))
    | ~ spl7_788 ),
    inference(avatar_component_clause,[],[f5040])).

fof(f15691,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f7523,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7523,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k2_tmap_1(sK0,sK0,X0,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f4359,f201])).

fof(f201,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f4359,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f4358,f152])).

fof(f152,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f151])).

fof(f4358,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f4357,f166])).

fof(f4357,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | k2_tmap_1(sK0,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f2539,f159])).

fof(f159,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f2539,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | k2_tmap_1(sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X1,u1_struct_0(X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f2538,f152])).

fof(f2538,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | k2_tmap_1(sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f2537,f166])).

fof(f2537,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | k2_tmap_1(sK0,X2,X1,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X2),X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f119,f159])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',d4_tmap_1)).

fof(f15690,plain,
    ( spl7_1844
    | spl7_1846
    | ~ spl7_20
    | spl7_181 ),
    inference(avatar_split_clause,[],[f15636,f1019,f223,f15688,f15682])).

fof(f15682,plain,
    ( spl7_1844
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1844])])).

fof(f15688,plain,
    ( spl7_1846
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1846])])).

fof(f223,plain,
    ( spl7_20
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f1019,plain,
    ( spl7_181
  <=> ~ v1_xboole_0(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_181])])).

fof(f15636,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k3_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_20
    | ~ spl7_181 ),
    inference(resolution,[],[f4017,f1020])).

fof(f1020,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK0))
    | ~ spl7_181 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f4017,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | o_0_0_xboole_0 = sK4(k1_zfmisc_1(X0))
        | k1_funct_1(k6_partfun1(X0),sK4(sK4(k1_zfmisc_1(X0)))) = sK4(sK4(k1_zfmisc_1(X0))) )
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f4006,f224])).

fof(f224,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f223])).

fof(f4006,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_funct_1(k6_partfun1(X0),sK4(sK4(k1_zfmisc_1(X0)))) = sK4(sK4(k1_zfmisc_1(X0)))
      | k1_xboole_0 = sK4(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f1211,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t6_boole)).

fof(f1211,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | k1_funct_1(k6_partfun1(X0),sK4(sK4(k1_zfmisc_1(X0)))) = sK4(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f1209,f601])).

fof(f601,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k1_funct_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(resolution,[],[f146,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t2_subset)).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(k6_partfun1(X1),X0) = X0 ) ),
    inference(forward_demodulation,[],[f125,f107])).

fof(f107,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',redefinition_k6_partfun1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t35_funct_1)).

fof(f1209,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f1017,f121])).

fof(f121,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',existence_m1_subset_1)).

fof(f1017,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,sK4(k1_zfmisc_1(X12)))
      | v1_xboole_0(sK4(k1_zfmisc_1(X12)))
      | m1_subset_1(X11,X12) ) ),
    inference(resolution,[],[f640,f121])).

fof(f640,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X3,X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f133,f126])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t4_subset)).

fof(f15614,plain,
    ( spl7_1842
    | ~ spl7_78
    | spl7_357
    | spl7_1831 ),
    inference(avatar_split_clause,[],[f15590,f15409,f1983,f502,f15612])).

fof(f15612,plain,
    ( spl7_1842
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),sK4(k3_struct_0(sK6))) = sK4(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1842])])).

fof(f502,plain,
    ( spl7_78
  <=> k3_struct_0(sK6) = k6_partfun1(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f1983,plain,
    ( spl7_357
  <=> ~ v1_xboole_0(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_357])])).

fof(f15409,plain,
    ( spl7_1831
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1831])])).

fof(f15590,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),sK4(k3_struct_0(sK6))) = sK4(k3_struct_0(sK6))
    | ~ spl7_78
    | ~ spl7_357
    | ~ spl7_1831 ),
    inference(forward_demodulation,[],[f15589,f503])).

fof(f503,plain,
    ( k3_struct_0(sK6) = k6_partfun1(u1_struct_0(sK6))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f502])).

fof(f15589,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),sK4(k6_partfun1(u1_struct_0(sK6)))) = sK4(k6_partfun1(u1_struct_0(sK6)))
    | ~ spl7_78
    | ~ spl7_357
    | ~ spl7_1831 ),
    inference(subsumption_resolution,[],[f15588,f1984])).

fof(f1984,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK6))
    | ~ spl7_357 ),
    inference(avatar_component_clause,[],[f1983])).

fof(f15588,plain,
    ( v1_xboole_0(k3_struct_0(sK6))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),sK4(k6_partfun1(u1_struct_0(sK6)))) = sK4(k6_partfun1(u1_struct_0(sK6)))
    | ~ spl7_78
    | ~ spl7_1831 ),
    inference(forward_demodulation,[],[f15576,f503])).

fof(f15576,plain,
    ( v1_xboole_0(k6_partfun1(u1_struct_0(sK6)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),sK4(k6_partfun1(u1_struct_0(sK6)))) = sK4(k6_partfun1(u1_struct_0(sK6)))
    | ~ spl7_1831 ),
    inference(resolution,[],[f15410,f4439])).

fof(f4439,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X0))
      | v1_xboole_0(k6_partfun1(X0))
      | k1_funct_1(k6_partfun1(k2_zfmisc_1(X0,X0)),sK4(k6_partfun1(X0))) = sK4(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f1207,f121])).

fof(f1207,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k6_partfun1(X0))
      | v1_xboole_0(k6_partfun1(X0))
      | v1_xboole_0(k2_zfmisc_1(X0,X0))
      | k1_funct_1(k6_partfun1(k2_zfmisc_1(X0,X0)),X1) = X1 ) ),
    inference(resolution,[],[f1015,f601])).

fof(f1015,plain,(
    ! [X8,X9] :
      ( m1_subset_1(X8,k2_zfmisc_1(X9,X9))
      | v1_xboole_0(k6_partfun1(X9))
      | ~ m1_subset_1(X8,k6_partfun1(X9)) ) ),
    inference(resolution,[],[f640,f108])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k6_partfun1)).

fof(f15410,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
    | ~ spl7_1831 ),
    inference(avatar_component_clause,[],[f15409])).

fof(f15607,plain,
    ( spl7_1838
    | ~ spl7_1841
    | ~ spl7_1832 ),
    inference(avatar_split_clause,[],[f15592,f15415,f15605,f15599])).

fof(f15599,plain,
    ( spl7_1838
  <=> v1_xboole_0(sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1838])])).

fof(f15605,plain,
    ( spl7_1841
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1841])])).

fof(f15415,plain,
    ( spl7_1832
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK6))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1832])])).

fof(f15592,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | v1_xboole_0(sK4(k3_struct_0(sK6)))
    | ~ spl7_1832 ),
    inference(resolution,[],[f15416,f121])).

fof(f15416,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK6))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),X1)
        | v1_xboole_0(X1) )
    | ~ spl7_1832 ),
    inference(avatar_component_clause,[],[f15415])).

fof(f15575,plain,
    ( spl7_357
    | ~ spl7_1762
    | ~ spl7_1836 ),
    inference(avatar_contradiction_clause,[],[f15572])).

fof(f15572,plain,
    ( $false
    | ~ spl7_357
    | ~ spl7_1762
    | ~ spl7_1836 ),
    inference(resolution,[],[f15564,f121])).

fof(f15564,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_struct_0(sK6))
    | ~ spl7_357
    | ~ spl7_1762
    | ~ spl7_1836 ),
    inference(subsumption_resolution,[],[f15545,f1984])).

fof(f15545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK6))
        | v1_xboole_0(k3_struct_0(sK6)) )
    | ~ spl7_1762
    | ~ spl7_1836 ),
    inference(resolution,[],[f15543,f14813])).

fof(f14813,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ m1_subset_1(X4,X3)
        | v1_xboole_0(X3) )
    | ~ spl7_1762 ),
    inference(avatar_component_clause,[],[f14812])).

fof(f14812,plain,
    ( spl7_1762
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ m1_subset_1(X4,X3)
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1762])])).

fof(f15543,plain,
    ( m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_1836 ),
    inference(avatar_component_clause,[],[f15542])).

fof(f15542,plain,
    ( spl7_1836
  <=> m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1836])])).

fof(f15544,plain,
    ( spl7_1836
    | ~ spl7_118
    | ~ spl7_1834 ),
    inference(avatar_split_clause,[],[f15455,f15452,f693,f15542])).

fof(f693,plain,
    ( spl7_118
  <=> m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f15452,plain,
    ( spl7_1834
  <=> k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1834])])).

fof(f15455,plain,
    ( m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_118
    | ~ spl7_1834 ),
    inference(superposition,[],[f694,f15453])).

fof(f15453,plain,
    ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)) = o_0_0_xboole_0
    | ~ spl7_1834 ),
    inference(avatar_component_clause,[],[f15452])).

fof(f694,plain,
    ( m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f693])).

fof(f15454,plain,
    ( spl7_1834
    | ~ spl7_20
    | ~ spl7_1830 ),
    inference(avatar_split_clause,[],[f15434,f15412,f223,f15452])).

fof(f15412,plain,
    ( spl7_1830
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1830])])).

fof(f15434,plain,
    ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1830 ),
    inference(forward_demodulation,[],[f15418,f224])).

fof(f15418,plain,
    ( k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)) = k1_xboole_0
    | ~ spl7_1830 ),
    inference(resolution,[],[f15413,f117])).

fof(f15413,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
    | ~ spl7_1830 ),
    inference(avatar_component_clause,[],[f15412])).

fof(f15417,plain,
    ( spl7_1830
    | spl7_1832
    | ~ spl7_358 ),
    inference(avatar_split_clause,[],[f2012,f1989,f15415,f15412])).

fof(f1989,plain,
    ( spl7_358
  <=> ! [X7] :
        ( m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
        | ~ m1_subset_1(X7,k3_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_358])])).

fof(f2012,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK6))
        | v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),X1) )
    | ~ spl7_358 ),
    inference(resolution,[],[f1990,f531])).

fof(f531,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f404,f126])).

fof(f404,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X4,X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f126,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',antisymmetry_r2_hidden)).

fof(f1990,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
        | ~ m1_subset_1(X7,k3_struct_0(sK6)) )
    | ~ spl7_358 ),
    inference(avatar_component_clause,[],[f1989])).

fof(f15407,plain,
    ( spl7_244
    | spl7_756
    | ~ spl7_66
    | spl7_195
    | spl7_415 ),
    inference(avatar_split_clause,[],[f4490,f2377,f1102,f454,f4796,f1392])).

fof(f1392,plain,
    ( spl7_244
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f4796,plain,
    ( spl7_756
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_756])])).

fof(f454,plain,
    ( spl7_66
  <=> k3_struct_0(sK1) = k6_partfun1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1102,plain,
    ( spl7_195
  <=> ~ v1_xboole_0(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_195])])).

fof(f2377,plain,
    ( spl7_415
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_415])])).

fof(f4490,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK1))))
    | ~ spl7_66
    | ~ spl7_195
    | ~ spl7_415 ),
    inference(resolution,[],[f4471,f1209])).

fof(f4471,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK1))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),X1) = X1 )
    | ~ spl7_66
    | ~ spl7_195
    | ~ spl7_415 ),
    inference(subsumption_resolution,[],[f4470,f1103])).

fof(f1103,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK1))
    | ~ spl7_195 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f4470,plain,
    ( ! [X1] :
        ( v1_xboole_0(k3_struct_0(sK1))
        | ~ m1_subset_1(X1,k3_struct_0(sK1))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),X1) = X1 )
    | ~ spl7_66
    | ~ spl7_415 ),
    inference(forward_demodulation,[],[f4469,f455])).

fof(f455,plain,
    ( k3_struct_0(sK1) = k6_partfun1(u1_struct_0(sK1))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f454])).

fof(f4469,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK1))
        | v1_xboole_0(k6_partfun1(u1_struct_0(sK1)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),X1) = X1 )
    | ~ spl7_66
    | ~ spl7_415 ),
    inference(subsumption_resolution,[],[f4443,f2378])).

fof(f2378,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_415 ),
    inference(avatar_component_clause,[],[f2377])).

fof(f4443,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK1))
        | v1_xboole_0(k6_partfun1(u1_struct_0(sK1)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),X1) = X1 )
    | ~ spl7_66 ),
    inference(superposition,[],[f1207,f455])).

fof(f15406,plain,
    ( spl7_1828
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1817 ),
    inference(avatar_split_clause,[],[f15334,f15226,f5040,f447,f15404])).

fof(f15404,plain,
    ( spl7_1828
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1828])])).

fof(f447,plain,
    ( spl7_64
  <=> v1_relat_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f15226,plain,
    ( spl7_1817
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1817])])).

fof(f15334,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1817 ),
    inference(resolution,[],[f15227,f10677])).

fof(f10677,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
        | k1_funct_1(k3_struct_0(sK0),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),sK4(X0)) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f10487,f121])).

fof(f10487,plain,
    ( ! [X52,X51] :
        ( ~ m1_subset_1(X52,sK4(k1_zfmisc_1(X51)))
        | v1_xboole_0(sK4(k1_zfmisc_1(X51)))
        | k1_funct_1(k3_struct_0(sK0),sK4(X51)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X51),sK4(X51)) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f6450,f121])).

fof(f6450,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | k1_funct_1(k3_struct_0(sK0),sK4(X2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X2),sK4(X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X3,X1) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5305,f126])).

fof(f5305,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | k1_funct_1(k3_struct_0(sK0),sK4(X5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X5),sK4(X5)) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t5_subset)).

fof(f5246,plain,
    ( ! [X23] :
        ( v1_xboole_0(X23)
        | k1_funct_1(k3_struct_0(sK0),sK4(X23)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X23),sK4(X23)) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f121])).

fof(f5055,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK0),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X7),X6) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5052,f448])).

fof(f448,plain,
    ( v1_relat_1(k3_struct_0(sK0))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f447])).

fof(f5052,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK0),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK0))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_788 ),
    inference(resolution,[],[f5041,f1069])).

fof(f1069,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X1)
      | k1_funct_1(X1,X2) = k1_funct_1(k7_relat_1(X1,X3),X2)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f132,f126])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t72_funct_1)).

fof(f15227,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))
    | ~ spl7_1817 ),
    inference(avatar_component_clause,[],[f15226])).

fof(f15399,plain,
    ( spl7_1826
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1817 ),
    inference(avatar_split_clause,[],[f15333,f15226,f5067,f463,f15397])).

fof(f15397,plain,
    ( spl7_1826
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1826])])).

fof(f463,plain,
    ( spl7_68
  <=> v1_relat_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f5067,plain,
    ( spl7_792
  <=> v1_funct_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_792])])).

fof(f15333,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1817 ),
    inference(resolution,[],[f15227,f10827])).

fof(f10827,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
        | k1_funct_1(k3_struct_0(sK1),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X0),sK4(X0)) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f10535,f121])).

fof(f10535,plain,
    ( ! [X52,X51] :
        ( ~ m1_subset_1(X52,sK4(k1_zfmisc_1(X51)))
        | v1_xboole_0(sK4(k1_zfmisc_1(X51)))
        | k1_funct_1(k3_struct_0(sK1),sK4(X51)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X51),sK4(X51)) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f6513,f121])).

fof(f6513,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | k1_funct_1(k3_struct_0(sK1),sK4(X2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X2),sK4(X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X3,X1) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5422,f126])).

fof(f5422,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
        | k1_funct_1(k3_struct_0(sK1),sK4(X5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X5),sK4(X5)) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f134])).

fof(f5386,plain,
    ( ! [X23] :
        ( v1_xboole_0(X23)
        | k1_funct_1(k3_struct_0(sK1),sK4(X23)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X23),sK4(X23)) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f121])).

fof(f5082,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK1),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X7),X6) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(subsumption_resolution,[],[f5079,f464])).

fof(f464,plain,
    ( v1_relat_1(k3_struct_0(sK1))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f463])).

fof(f5079,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK1),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK1))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_792 ),
    inference(resolution,[],[f5068,f1069])).

fof(f5068,plain,
    ( v1_funct_1(k3_struct_0(sK1))
    | ~ spl7_792 ),
    inference(avatar_component_clause,[],[f5067])).

fof(f15375,plain,
    ( spl7_1824
    | spl7_1817 ),
    inference(avatar_split_clause,[],[f15337,f15226,f15373])).

fof(f15373,plain,
    ( spl7_1824
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))) = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1824])])).

fof(f15337,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))) = sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))
    | ~ spl7_1817 ),
    inference(resolution,[],[f15227,f858])).

fof(f858,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | k1_funct_1(k6_partfun1(X2),sK4(X2)) = sK4(X2) ) ),
    inference(resolution,[],[f601,f121])).

fof(f15368,plain,
    ( spl7_1822
    | spl7_1817 ),
    inference(avatar_split_clause,[],[f15336,f15226,f15366])).

fof(f15366,plain,
    ( spl7_1822
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1822])])).

fof(f15336,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_1817 ),
    inference(resolution,[],[f15227,f3732])).

fof(f3732,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
      | k1_funct_1(k6_partfun1(X0),sK4(X0)) = sK4(X0) ) ),
    inference(resolution,[],[f3724,f121])).

fof(f3724,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,sK4(k1_zfmisc_1(X28)))
      | v1_xboole_0(sK4(k1_zfmisc_1(X28)))
      | k1_funct_1(k6_partfun1(X28),sK4(X28)) = sK4(X28) ) ),
    inference(resolution,[],[f1929,f121])).

fof(f1929,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k1_funct_1(k6_partfun1(X2),sK4(X2)) = sK4(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f888,f126])).

fof(f888,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_funct_1(k6_partfun1(X0),sK4(X0)) = sK4(X0) ) ),
    inference(resolution,[],[f858,f134])).

fof(f15330,plain,
    ( ~ spl7_64
    | spl7_1821 ),
    inference(avatar_contradiction_clause,[],[f15329])).

fof(f15329,plain,
    ( $false
    | ~ spl7_64
    | ~ spl7_1821 ),
    inference(subsumption_resolution,[],[f15328,f448])).

fof(f15328,plain,
    ( ~ v1_relat_1(k3_struct_0(sK0))
    | ~ spl7_1821 ),
    inference(resolution,[],[f15326,f400])).

fof(f400,plain,(
    ! [X0] :
      ( v1_relat_1(sK4(k1_zfmisc_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f113,f121])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',cc2_relat_1)).

fof(f15326,plain,
    ( ~ v1_relat_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_1821 ),
    inference(avatar_component_clause,[],[f15325])).

fof(f15325,plain,
    ( spl7_1821
  <=> ~ v1_relat_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1821])])).

fof(f15327,plain,
    ( ~ spl7_1821
    | spl7_189
    | ~ spl7_1818 ),
    inference(avatar_split_clause,[],[f15317,f15266,f1061,f15325])).

fof(f1061,plain,
    ( spl7_189
  <=> ~ v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f15266,plain,
    ( spl7_1818
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1818])])).

fof(f15317,plain,
    ( ~ v1_relat_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_189
    | ~ spl7_1818 ),
    inference(subsumption_resolution,[],[f15271,f1062])).

fof(f1062,plain,
    ( ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl7_189 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f15271,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_1818 ),
    inference(superposition,[],[f400,f15267])).

fof(f15267,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_1818 ),
    inference(avatar_component_clause,[],[f15266])).

fof(f15268,plain,
    ( spl7_1818
    | ~ spl7_20
    | ~ spl7_1816 ),
    inference(avatar_split_clause,[],[f15248,f15229,f223,f15266])).

fof(f15229,plain,
    ( spl7_1816
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1816])])).

fof(f15248,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_20
    | ~ spl7_1816 ),
    inference(forward_demodulation,[],[f15232,f224])).

fof(f15232,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_1816 ),
    inference(resolution,[],[f15230,f117])).

fof(f15230,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))
    | ~ spl7_1816 ),
    inference(avatar_component_clause,[],[f15229])).

fof(f15231,plain,
    ( spl7_1814
    | spl7_1816
    | spl7_240
    | ~ spl7_182 ),
    inference(avatar_split_clause,[],[f4221,f1025,f1377,f15229,f15223])).

fof(f15223,plain,
    ( spl7_1814
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1814])])).

fof(f1377,plain,
    ( spl7_240
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_240])])).

fof(f1025,plain,
    ( spl7_182
  <=> ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k3_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f4221,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0))))))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_182 ),
    inference(resolution,[],[f1218,f1026])).

fof(f1026,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k3_struct_0(sK0))
        | m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl7_182 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1218,plain,(
    ! [X6] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X6))))),X6)
      | v1_xboole_0(sK4(k1_zfmisc_1(X6)))
      | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X6))))) ) ),
    inference(resolution,[],[f1209,f1017])).

fof(f15218,plain,(
    ~ spl7_1812 ),
    inference(avatar_contradiction_clause,[],[f15215])).

fof(f15215,plain,
    ( $false
    | ~ spl7_1812 ),
    inference(resolution,[],[f15213,f121])).

fof(f15213,plain,
    ( ! [X4] : ~ m1_subset_1(X4,k3_struct_0(sK0))
    | ~ spl7_1812 ),
    inference(avatar_component_clause,[],[f15212])).

fof(f15212,plain,
    ( spl7_1812
  <=> ! [X4] : ~ m1_subset_1(X4,k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1812])])).

fof(f15214,plain,
    ( spl7_1812
    | spl7_1304
    | ~ spl7_82
    | spl7_181 ),
    inference(avatar_split_clause,[],[f3727,f1019,f518,f10033,f15212])).

fof(f10033,plain,
    ( spl7_1304
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1304])])).

fof(f3727,plain,
    ( ! [X4] :
        ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k3_struct_0(sK0)) )
    | ~ spl7_82
    | ~ spl7_181 ),
    inference(subsumption_resolution,[],[f3705,f1020])).

fof(f3705,plain,
    ( ! [X4] :
        ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(k3_struct_0(sK0))
        | ~ m1_subset_1(X4,k3_struct_0(sK0)) )
    | ~ spl7_82 ),
    inference(resolution,[],[f1929,f519])).

fof(f15209,plain,
    ( ~ spl7_1811
    | spl7_506
    | spl7_1310
    | ~ spl7_530 ),
    inference(avatar_split_clause,[],[f3367,f3363,f10050,f3171,f15207])).

fof(f15207,plain,
    ( spl7_1811
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1811])])).

fof(f3171,plain,
    ( spl7_506
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_506])])).

fof(f10050,plain,
    ( spl7_1310
  <=> v1_xboole_0(sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1310])])).

fof(f3363,plain,
    ( spl7_530
  <=> m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_530])])).

fof(f3367,plain,
    ( v1_xboole_0(sK4(k4_tmap_1(sK0,sK3(sK0))))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_530 ),
    inference(resolution,[],[f3364,f531])).

fof(f3364,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_530 ),
    inference(avatar_component_clause,[],[f3363])).

fof(f15202,plain,
    ( spl7_1804
    | spl7_1806
    | ~ spl7_1809
    | ~ spl7_436 ),
    inference(avatar_split_clause,[],[f2747,f2564,f15200,f15194,f15188])).

fof(f15188,plain,
    ( spl7_1804
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1804])])).

fof(f15194,plain,
    ( spl7_1806
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1806])])).

fof(f15200,plain,
    ( spl7_1809
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1809])])).

fof(f2564,plain,
    ( spl7_436
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_436])])).

fof(f2747,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1)))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK1))))
    | ~ spl7_436 ),
    inference(resolution,[],[f2565,f1209])).

fof(f2565,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1)
        | v1_xboole_0(X1) )
    | ~ spl7_436 ),
    inference(avatar_component_clause,[],[f2564])).

fof(f15181,plain,
    ( ~ spl7_1801
    | spl7_1802
    | spl7_310
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f748,f744,f1737,f15179,f15173])).

fof(f15173,plain,
    ( spl7_1801
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))),k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1801])])).

fof(f15179,plain,
    ( spl7_1802
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1802])])).

fof(f1737,plain,
    ( spl7_310
  <=> v1_xboole_0(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_310])])).

fof(f744,plain,
    ( spl7_128
  <=> m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f748,plain,
    ( v1_xboole_0(k3_struct_0(sK3(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))),k3_struct_0(sK3(sK0)))
    | ~ spl7_128 ),
    inference(resolution,[],[f745,f531])).

fof(f745,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
    | ~ spl7_128 ),
    inference(avatar_component_clause,[],[f744])).

fof(f15168,plain,
    ( ~ spl7_1797
    | spl7_1798
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f15138,f5633,f5617,f4377,f2428,f186,f15166,f15160])).

fof(f15160,plain,
    ( spl7_1797
  <=> ~ l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1797])])).

fof(f15166,plain,
    ( spl7_1798
  <=> v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1798])])).

fof(f186,plain,
    ( spl7_10
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f2428,plain,
    ( spl7_422
  <=> u1_struct_0(sK5) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_422])])).

fof(f4377,plain,
    ( spl7_700
  <=> v1_funct_1(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_700])])).

fof(f5617,plain,
    ( spl7_848
  <=> v1_funct_2(k3_struct_0(sK5),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_848])])).

fof(f5633,plain,
    ( spl7_852
  <=> m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_852])])).

fof(f15138,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ l1_pre_topc(sK5)
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(superposition,[],[f15135,f2429])).

fof(f2429,plain,
    ( u1_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_422 ),
    inference(avatar_component_clause,[],[f2428])).

fof(f15135,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),X0),u1_struct_0(X0),o_0_0_xboole_0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f15134,f4378])).

fof(f4378,plain,
    ( v1_funct_1(k3_struct_0(sK5))
    | ~ spl7_700 ),
    inference(avatar_component_clause,[],[f4377])).

fof(f15134,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),X0),u1_struct_0(X0),o_0_0_xboole_0)
        | ~ v1_funct_1(k3_struct_0(sK5))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f15133,f5634])).

fof(f5634,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_852 ),
    inference(avatar_component_clause,[],[f5633])).

fof(f15133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),X0),u1_struct_0(X0),o_0_0_xboole_0)
        | ~ v1_funct_1(k3_struct_0(sK5))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_848 ),
    inference(resolution,[],[f8382,f5618])).

fof(f5618,plain,
    ( v1_funct_2(k3_struct_0(sK5),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl7_848 ),
    inference(avatar_component_clause,[],[f5617])).

fof(f8382,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | v1_funct_2(k2_tmap_1(sK5,sK5,X0,X1),u1_struct_0(X1),o_0_0_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8304,f2429])).

fof(f8304,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X0)
        | v1_funct_2(k2_tmap_1(sK5,sK5,X0,X1),u1_struct_0(X1),u1_struct_0(sK5))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8303,f2429])).

fof(f8303,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | v1_funct_2(k2_tmap_1(sK5,sK5,X0,X1),u1_struct_0(X1),u1_struct_0(sK5))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8301,f2429])).

fof(f8301,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | v1_funct_2(k2_tmap_1(sK5,sK5,X0,X1),u1_struct_0(X1),u1_struct_0(sK5))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f4251,f187])).

fof(f187,plain,
    ( l1_struct_0(sK5)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f4251,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
        | v1_funct_2(k2_tmap_1(sK5,X1,X0,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ l1_pre_topc(X2) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2218,f187])).

fof(f2218,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ l1_struct_0(X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X5)
      | ~ l1_struct_0(X4)
      | v1_funct_2(k2_tmap_1(X3,X4,X5,X6),u1_struct_0(X6),u1_struct_0(X4))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f138,f114])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
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
    inference(flattening,[],[f79])).

fof(f79,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k2_tmap_1)).

fof(f15149,plain,
    ( spl7_1794
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f15142,f5633,f5617,f4377,f2428,f2326,f266,f186,f15147])).

fof(f15147,plain,
    ( spl7_1794
  <=> v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK3(sK0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1794])])).

fof(f266,plain,
    ( spl7_30
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f2326,plain,
    ( spl7_398
  <=> u1_struct_0(sK3(sK0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_398])])).

fof(f15142,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK3(sK0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f15139,f267])).

fof(f267,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f15139,plain,
    ( v1_funct_2(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK3(sK0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ l1_pre_topc(sK3(sK0))
    | ~ spl7_10
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(superposition,[],[f15135,f2327])).

fof(f2327,plain,
    ( u1_struct_0(sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_398 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f15131,plain,
    ( spl7_1790
    | spl7_1792
    | ~ spl7_350 ),
    inference(avatar_split_clause,[],[f1974,f1953,f15129,f15126])).

fof(f15126,plain,
    ( spl7_1790
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1790])])).

fof(f15129,plain,
    ( spl7_1792
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK5))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1792])])).

fof(f1953,plain,
    ( spl7_350
  <=> ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))
        | ~ m1_subset_1(X6,k3_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_350])])).

fof(f1974,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK5))
        | v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)),X1) )
    | ~ spl7_350 ),
    inference(resolution,[],[f1954,f531])).

fof(f1954,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))
        | ~ m1_subset_1(X6,k3_struct_0(sK5)) )
    | ~ spl7_350 ),
    inference(avatar_component_clause,[],[f1953])).

fof(f15121,plain,
    ( spl7_1788
    | ~ spl7_724
    | ~ spl7_1782 ),
    inference(avatar_split_clause,[],[f15025,f15021,f4628,f15119])).

fof(f15119,plain,
    ( spl7_1788
  <=> m1_subset_1(sK4(k3_struct_0(sK3(sK6))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1788])])).

fof(f4628,plain,
    ( spl7_724
  <=> m1_subset_1(sK4(k3_struct_0(sK3(sK6))),k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_724])])).

fof(f15021,plain,
    ( spl7_1782
  <=> u1_struct_0(sK3(sK6)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1782])])).

fof(f15025,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK3(sK6))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_724
    | ~ spl7_1782 ),
    inference(superposition,[],[f4629,f15022])).

fof(f15022,plain,
    ( u1_struct_0(sK3(sK6)) = o_0_0_xboole_0
    | ~ spl7_1782 ),
    inference(avatar_component_clause,[],[f15021])).

fof(f4629,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK3(sK6))),k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6))))
    | ~ spl7_724 ),
    inference(avatar_component_clause,[],[f4628])).

fof(f15113,plain,
    ( spl7_1786
    | ~ spl7_224
    | ~ spl7_1782 ),
    inference(avatar_split_clause,[],[f15026,f15021,f1300,f15111])).

fof(f15111,plain,
    ( spl7_1786
  <=> m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1786])])).

fof(f1300,plain,
    ( spl7_224
  <=> m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f15026,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_224
    | ~ spl7_1782 ),
    inference(superposition,[],[f1301,f15022])).

fof(f1301,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)))))
    | ~ spl7_224 ),
    inference(avatar_component_clause,[],[f1300])).

fof(f15073,plain,
    ( spl7_1784
    | ~ spl7_102
    | ~ spl7_424
    | ~ spl7_1782 ),
    inference(avatar_split_clause,[],[f15042,f15021,f2446,f614,f15071])).

fof(f15071,plain,
    ( spl7_1784
  <=> k3_struct_0(sK5) = k3_struct_0(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1784])])).

fof(f614,plain,
    ( spl7_102
  <=> k3_struct_0(sK3(sK6)) = k6_partfun1(u1_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f2446,plain,
    ( spl7_424
  <=> k3_struct_0(sK5) = k6_partfun1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_424])])).

fof(f15042,plain,
    ( k3_struct_0(sK5) = k3_struct_0(sK3(sK6))
    | ~ spl7_102
    | ~ spl7_424
    | ~ spl7_1782 ),
    inference(forward_demodulation,[],[f15027,f2447])).

fof(f2447,plain,
    ( k3_struct_0(sK5) = k6_partfun1(o_0_0_xboole_0)
    | ~ spl7_424 ),
    inference(avatar_component_clause,[],[f2446])).

fof(f15027,plain,
    ( k3_struct_0(sK3(sK6)) = k6_partfun1(o_0_0_xboole_0)
    | ~ spl7_102
    | ~ spl7_1782 ),
    inference(superposition,[],[f615,f15022])).

fof(f615,plain,
    ( k3_struct_0(sK3(sK6)) = k6_partfun1(u1_struct_0(sK3(sK6)))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f614])).

fof(f15023,plain,
    ( spl7_1782
    | spl7_672
    | ~ spl7_8
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f1231,f614,f179,f4248,f15021])).

fof(f4248,plain,
    ( spl7_672
  <=> k1_funct_1(k3_struct_0(sK3(sK6)),sK4(u1_struct_0(sK3(sK6)))) = sK4(u1_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_672])])).

fof(f179,plain,
    ( spl7_8
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1231,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK6)),sK4(u1_struct_0(sK3(sK6)))) = sK4(u1_struct_0(sK3(sK6)))
    | u1_struct_0(sK3(sK6)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_102 ),
    inference(superposition,[],[f889,f615])).

fof(f889,plain,
    ( ! [X3] :
        ( k1_funct_1(k6_partfun1(X3),sK4(X3)) = sK4(X3)
        | o_0_0_xboole_0 = X3 )
    | ~ spl7_8 ),
    inference(resolution,[],[f858,f350])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f130,f180])).

fof(f180,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f179])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t8_boole)).

fof(f15016,plain,
    ( ~ spl7_1779
    | spl7_1780
    | spl7_356
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f739,f693,f1986,f15014,f15008])).

fof(f15008,plain,
    ( spl7_1779
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1779])])).

fof(f15014,plain,
    ( spl7_1780
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1780])])).

fof(f1986,plain,
    ( spl7_356
  <=> v1_xboole_0(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_356])])).

fof(f739,plain,
    ( v1_xboole_0(k3_struct_0(sK6))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))),k3_struct_0(sK6))
    | ~ spl7_118 ),
    inference(resolution,[],[f694,f531])).

fof(f15003,plain,
    ( spl7_1776
    | ~ spl7_80
    | ~ spl7_832
    | spl7_1701 ),
    inference(avatar_split_clause,[],[f14193,f14182,f5476,f511,f15001])).

fof(f15001,plain,
    ( spl7_1776
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1776])])).

fof(f511,plain,
    ( spl7_80
  <=> v1_relat_1(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f5476,plain,
    ( spl7_832
  <=> v1_funct_1(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_832])])).

fof(f14182,plain,
    ( spl7_1701
  <=> ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1701])])).

fof(f14193,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1701 ),
    inference(resolution,[],[f14183,f8527])).

fof(f8527,plain,
    ( ! [X26] :
        ( v1_xboole_0(X26)
        | k1_funct_1(k3_struct_0(sK6),sK4(X26)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),X26),sK4(X26)) )
    | ~ spl7_80
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f121])).

fof(f5500,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK6),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),X7),X6) )
    | ~ spl7_80
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f5497,f512])).

fof(f512,plain,
    ( v1_relat_1(k3_struct_0(sK6))
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f511])).

fof(f5497,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK6),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK6))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_832 ),
    inference(resolution,[],[f5477,f1069])).

fof(f5477,plain,
    ( v1_funct_1(k3_struct_0(sK6))
    | ~ spl7_832 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f14183,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_1701 ),
    inference(avatar_component_clause,[],[f14182])).

fof(f14996,plain,
    ( spl7_1774
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1701 ),
    inference(avatar_split_clause,[],[f14187,f14182,f5067,f463,f14994])).

fof(f14994,plain,
    ( spl7_1774
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1774])])).

fof(f14187,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1701 ),
    inference(resolution,[],[f14183,f5386])).

fof(f14989,plain,
    ( spl7_1772
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1701 ),
    inference(avatar_split_clause,[],[f14186,f14182,f5040,f447,f14987])).

fof(f14987,plain,
    ( spl7_1772
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1772])])).

fof(f14186,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1701 ),
    inference(resolution,[],[f14183,f5246])).

fof(f14877,plain,
    ( spl7_1770
    | ~ spl7_80
    | ~ spl7_832
    | spl7_1703
    | ~ spl7_1722 ),
    inference(avatar_split_clause,[],[f14389,f14362,f14201,f5476,f511,f14875])).

fof(f14875,plain,
    ( spl7_1770
  <=> k1_funct_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1770])])).

fof(f14201,plain,
    ( spl7_1703
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1703])])).

fof(f14362,plain,
    ( spl7_1722
  <=> m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1722])])).

fof(f14389,plain,
    ( k1_funct_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1703
    | ~ spl7_1722 ),
    inference(subsumption_resolution,[],[f14378,f14202])).

fof(f14202,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_1703 ),
    inference(avatar_component_clause,[],[f14201])).

fof(f14378,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | k1_funct_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1722 ),
    inference(resolution,[],[f14363,f5500])).

fof(f14363,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_1722 ),
    inference(avatar_component_clause,[],[f14362])).

fof(f14852,plain,
    ( spl7_1768
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1703
    | ~ spl7_1722 ),
    inference(avatar_split_clause,[],[f14385,f14362,f14201,f5067,f463,f14850])).

fof(f14850,plain,
    ( spl7_1768
  <=> k1_funct_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1768])])).

fof(f14385,plain,
    ( k1_funct_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1703
    | ~ spl7_1722 ),
    inference(subsumption_resolution,[],[f14374,f14202])).

fof(f14374,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | k1_funct_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1722 ),
    inference(resolution,[],[f14363,f5082])).

fof(f14845,plain,
    ( spl7_1766
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1703
    | ~ spl7_1722 ),
    inference(avatar_split_clause,[],[f14384,f14362,f14201,f5040,f447,f14843])).

fof(f14843,plain,
    ( spl7_1766
  <=> k1_funct_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1766])])).

fof(f14384,plain,
    ( k1_funct_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1703
    | ~ spl7_1722 ),
    inference(subsumption_resolution,[],[f14373,f14202])).

fof(f14373,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | k1_funct_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1722 ),
    inference(resolution,[],[f14363,f5055])).

fof(f14838,plain,
    ( ~ spl7_1765
    | ~ spl7_398
    | spl7_1687 ),
    inference(avatar_split_clause,[],[f14831,f13949,f2326,f14836])).

fof(f14836,plain,
    ( spl7_1765
  <=> k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)) != k3_funct_2(o_0_0_xboole_0,u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1765])])).

fof(f13949,plain,
    ( spl7_1687
  <=> k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) != k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1687])])).

fof(f14831,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)) != k3_funct_2(o_0_0_xboole_0,u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl7_398
    | ~ spl7_1687 ),
    inference(superposition,[],[f13950,f2327])).

fof(f13950,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) != k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))
    | ~ spl7_1687 ),
    inference(avatar_component_clause,[],[f13949])).

fof(f14814,plain,
    ( spl7_1762
    | spl7_366
    | ~ spl7_70
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13549,f13504,f470,f2112,f14812])).

fof(f2112,plain,
    ( spl7_366
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_366])])).

fof(f470,plain,
    ( spl7_70
  <=> k3_struct_0(sK3(sK0)) = k6_partfun1(u1_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f13504,plain,
    ( spl7_1644
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1644])])).

fof(f13549,plain,
    ( ! [X4,X3] :
        ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,X3) )
    | ~ spl7_70
    | ~ spl7_1644 ),
    inference(forward_demodulation,[],[f13518,f471])).

fof(f471,plain,
    ( k3_struct_0(sK3(sK0)) = k6_partfun1(u1_struct_0(sK3(sK0)))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f470])).

fof(f13518,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
        | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK0))),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,X3) )
    | ~ spl7_1644 ),
    inference(superposition,[],[f3779,f13505])).

fof(f13505,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1644 ),
    inference(avatar_component_clause,[],[f13504])).

fof(f3779,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK4(k1_zfmisc_1(X2))))
      | k1_funct_1(k6_partfun1(X2),sK4(X2)) = sK4(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f3739,f126])).

fof(f3739,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK4(k1_zfmisc_1(X2))))
      | k1_funct_1(k6_partfun1(X2),sK4(X2)) = sK4(X2) ) ),
    inference(resolution,[],[f3732,f134])).

fof(f14800,plain,
    ( spl7_1760
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f14793,f5633,f5617,f4377,f2428,f2326,f266,f186,f14798])).

fof(f14798,plain,
    ( spl7_1760
  <=> v1_funct_1(k2_tmap_1(sK3(sK0),sK5,k3_struct_0(sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1760])])).

fof(f14793,plain,
    ( v1_funct_1(k2_tmap_1(sK3(sK0),sK5,k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14792,f4378])).

fof(f14792,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14791,f5634])).

fof(f14791,plain,
    ( ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_848 ),
    inference(resolution,[],[f14693,f5618])).

fof(f14693,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14692,f2327])).

fof(f14692,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),o_0_0_xboole_0)))
        | ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14691,f2429])).

fof(f14691,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK5))))
        | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14690,f2429])).

fof(f14690,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,u1_struct_0(sK5))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK5))))
        | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398 ),
    inference(subsumption_resolution,[],[f14683,f267])).

fof(f14683,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,u1_struct_0(sK5))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK5))))
        | v1_funct_1(k2_tmap_1(sK3(sK0),sK5,X1,sK5))
        | ~ l1_pre_topc(sK3(sK0)) )
    | ~ spl7_10
    | ~ spl7_398 ),
    inference(superposition,[],[f7157,f2327])).

fof(f7157,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5))))
        | v1_funct_1(k2_tmap_1(X1,sK5,X0,sK5))
        | ~ l1_pre_topc(X1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f3451,f187])).

fof(f3451,plain,
    ( ! [X4,X2,X3] :
        ( ~ l1_struct_0(X4)
        | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X4))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
        | v1_funct_1(k2_tmap_1(X3,X4,X2,sK5))
        | ~ l1_pre_topc(X3) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2001,f114])).

fof(f2001,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(X0,X1,X2,sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f137,f187])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f14784,plain,
    ( spl7_1758
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f14777,f5633,f5617,f4377,f2428,f2326,f266,f186,f14782])).

fof(f14782,plain,
    ( spl7_1758
  <=> v1_funct_1(k2_tmap_1(sK5,sK3(sK0),k3_struct_0(sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1758])])).

fof(f14777,plain,
    ( v1_funct_1(k2_tmap_1(sK5,sK3(sK0),k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14776,f4378])).

fof(f14776,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14775,f5634])).

fof(f14775,plain,
    ( ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422
    | ~ spl7_848 ),
    inference(resolution,[],[f14497,f5618])).

fof(f14497,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14496,f2429])).

fof(f14496,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),o_0_0_xboole_0)))
        | ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14495,f2327])).

fof(f14495,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK0)))))
        | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f14494,f2429])).

fof(f14494,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK5),o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK0)))))
        | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),X1,sK5)) )
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_398 ),
    inference(subsumption_resolution,[],[f14486,f267])).

fof(f14486,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK5),o_0_0_xboole_0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3(sK0)))))
        | v1_funct_1(k2_tmap_1(sK5,sK3(sK0),X1,sK5))
        | ~ l1_pre_topc(sK3(sK0)) )
    | ~ spl7_10
    | ~ spl7_398 ),
    inference(superposition,[],[f6590,f2327])).

fof(f6590,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK5),u1_struct_0(X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X2))))
        | v1_funct_1(k2_tmap_1(sK5,X2,X1,sK5))
        | ~ l1_pre_topc(X2) )
    | ~ spl7_10 ),
    inference(resolution,[],[f3450,f114])).

fof(f3450,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
        | v1_funct_1(k2_tmap_1(sK5,X1,X0,sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2001,f187])).

fof(f14774,plain,
    ( spl7_1756
    | spl7_1703 ),
    inference(avatar_split_clause,[],[f14204,f14201,f14772])).

fof(f14772,plain,
    ( spl7_1756
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))) = sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1756])])).

fof(f14204,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))) = sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_1703 ),
    inference(resolution,[],[f14202,f858])).

fof(f14743,plain,
    ( spl7_366
    | spl7_398
    | ~ spl7_70
    | ~ spl7_1640
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f14072,f13504,f13461,f470,f2326,f2112])).

fof(f13461,plain,
    ( spl7_1640
  <=> v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1640])])).

fof(f14072,plain,
    ( u1_struct_0(sK3(sK0)) = o_0_0_xboole_0
    | k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
    | ~ spl7_70
    | ~ spl7_1640
    | ~ spl7_1644 ),
    inference(forward_demodulation,[],[f13621,f13505])).

fof(f13621,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
    | u1_struct_0(sK3(sK0)) = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_70
    | ~ spl7_1640 ),
    inference(superposition,[],[f13475,f471])).

fof(f13475,plain,
    ( ! [X4] :
        ( sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))) = X4
        | k1_funct_1(k6_partfun1(X4),sK4(X4)) = sK4(X4) )
    | ~ spl7_1640 ),
    inference(resolution,[],[f13462,f890])).

fof(f890,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X5)
      | X4 = X5
      | k1_funct_1(k6_partfun1(X4),sK4(X4)) = sK4(X4) ) ),
    inference(resolution,[],[f858,f130])).

fof(f13462,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_1640 ),
    inference(avatar_component_clause,[],[f13461])).

fof(f14678,plain,
    ( spl7_1754
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f14327,f5633,f5617,f4377,f2428,f186,f14676])).

fof(f14676,plain,
    ( spl7_1754
  <=> m1_subset_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1754])])).

fof(f14327,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_700
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14326,f4378])).

fof(f14326,plain,
    ( m1_subset_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ v1_funct_1(k3_struct_0(sK5))
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_848
    | ~ spl7_852 ),
    inference(subsumption_resolution,[],[f14325,f5634])).

fof(f14325,plain,
    ( ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | m1_subset_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ v1_funct_1(k3_struct_0(sK5))
    | ~ spl7_10
    | ~ spl7_422
    | ~ spl7_848 ),
    inference(resolution,[],[f8428,f5618])).

fof(f8428,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | m1_subset_1(k2_tmap_1(sK5,sK5,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8427,f2429])).

fof(f8427,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X0)
        | m1_subset_1(k2_tmap_1(sK5,sK5,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8426,f2429])).

fof(f8426,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | m1_subset_1(k2_tmap_1(sK5,sK5,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) )
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f8424,f2429])).

fof(f8424,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | m1_subset_1(k2_tmap_1(sK5,sK5,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) )
    | ~ spl7_10 ),
    inference(resolution,[],[f4573,f187])).

fof(f4573,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(X1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
        | m1_subset_1(k2_tmap_1(sK5,X1,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2368,f187])).

fof(f2368,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_struct_0(X1)
        | m1_subset_1(k2_tmap_1(X0,X1,X2,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) )
    | ~ spl7_10 ),
    inference(resolution,[],[f139,f187])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f14671,plain,
    ( spl7_1752
    | ~ spl7_398
    | ~ spl7_694 ),
    inference(avatar_split_clause,[],[f14093,f4340,f2326,f14669])).

fof(f14669,plain,
    ( spl7_1752
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1752])])).

fof(f4340,plain,
    ( spl7_694
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_694])])).

fof(f14093,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_694 ),
    inference(superposition,[],[f4341,f2327])).

fof(f4341,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_694 ),
    inference(avatar_component_clause,[],[f4340])).

fof(f14664,plain,
    ( spl7_1748
    | ~ spl7_1751
    | ~ spl7_398
    | ~ spl7_748
    | spl7_1071
    | ~ spl7_1708 ),
    inference(avatar_split_clause,[],[f14554,f14234,f7527,f4769,f2326,f14662,f14656])).

fof(f14656,plain,
    ( spl7_1748
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1748])])).

fof(f14662,plain,
    ( spl7_1751
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1751])])).

fof(f4769,plain,
    ( spl7_748
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK0)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_748])])).

fof(f7527,plain,
    ( spl7_1071
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1071])])).

fof(f14234,plain,
    ( spl7_1708
  <=> k3_struct_0(sK5) = k3_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1708])])).

fof(f14554,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | ~ spl7_398
    | ~ spl7_748
    | ~ spl7_1071
    | ~ spl7_1708 ),
    inference(subsumption_resolution,[],[f14552,f7528])).

fof(f7528,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1071 ),
    inference(avatar_component_clause,[],[f7527])).

fof(f14552,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_398
    | ~ spl7_748
    | ~ spl7_1708 ),
    inference(resolution,[],[f14290,f1209])).

fof(f14290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),X0)
        | v1_xboole_0(X0) )
    | ~ spl7_398
    | ~ spl7_748
    | ~ spl7_1708 ),
    inference(forward_demodulation,[],[f14243,f2327])).

fof(f14243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),X0)
        | v1_xboole_0(X0) )
    | ~ spl7_748
    | ~ spl7_1708 ),
    inference(superposition,[],[f4770,f14235])).

fof(f14235,plain,
    ( k3_struct_0(sK5) = k3_struct_0(sK3(sK0))
    | ~ spl7_1708 ),
    inference(avatar_component_clause,[],[f14234])).

fof(f4770,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK0)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),X1)
        | v1_xboole_0(X1) )
    | ~ spl7_748 ),
    inference(avatar_component_clause,[],[f4769])).

fof(f14651,plain,
    ( spl7_1746
    | spl7_1701
    | ~ spl7_1724 ),
    inference(avatar_split_clause,[],[f14414,f14398,f14182,f14649])).

fof(f14649,plain,
    ( spl7_1746
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) = sK4(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1746])])).

fof(f14398,plain,
    ( spl7_1724
  <=> m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1724])])).

fof(f14414,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) = sK4(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_1701
    | ~ spl7_1724 ),
    inference(subsumption_resolution,[],[f14402,f14183])).

fof(f14402,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) = sK4(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_1724 ),
    inference(resolution,[],[f14399,f601])).

fof(f14399,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_1724 ),
    inference(avatar_component_clause,[],[f14398])).

fof(f14642,plain,
    ( spl7_1744
    | ~ spl7_389
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14635,f2326,f165,f158,f151,f2214,f14640])).

fof(f14640,plain,
    ( spl7_1744
  <=> v1_funct_2(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1744])])).

fof(f2214,plain,
    ( spl7_389
  <=> ~ m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_389])])).

fof(f14635,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_398 ),
    inference(subsumption_resolution,[],[f14634,f152])).

fof(f14634,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_398 ),
    inference(subsumption_resolution,[],[f14633,f166])).

fof(f14633,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_398 ),
    inference(resolution,[],[f14131,f159])).

fof(f14131,plain,
    ( ! [X13] :
        ( ~ v2_pre_topc(X13)
        | ~ m1_pre_topc(sK3(sK0),X13)
        | ~ l1_pre_topc(X13)
        | v1_funct_2(k4_tmap_1(X13,sK3(sK0)),o_0_0_xboole_0,u1_struct_0(X13))
        | v2_struct_0(X13) )
    | ~ spl7_398 ),
    inference(superposition,[],[f128,f2327])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k4_tmap_1)).

fof(f14632,plain,
    ( spl7_1742
    | ~ spl7_1252
    | ~ spl7_1450
    | ~ spl7_1708 ),
    inference(avatar_split_clause,[],[f14299,f14234,f11769,f9041,f14630])).

fof(f14630,plain,
    ( spl7_1742
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1742])])).

fof(f9041,plain,
    ( spl7_1252
  <=> k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK0)) = k3_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1252])])).

fof(f11769,plain,
    ( spl7_1450
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1450])])).

fof(f14299,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_1252
    | ~ spl7_1450
    | ~ spl7_1708 ),
    inference(forward_demodulation,[],[f14278,f9042])).

fof(f9042,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_1252 ),
    inference(avatar_component_clause,[],[f9041])).

fof(f14278,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_1450
    | ~ spl7_1708 ),
    inference(superposition,[],[f11770,f14235])).

fof(f11770,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_1450 ),
    inference(avatar_component_clause,[],[f11769])).

fof(f14625,plain,
    ( spl7_1740
    | ~ spl7_1418
    | ~ spl7_1708 ),
    inference(avatar_split_clause,[],[f14276,f14234,f11273,f14623])).

fof(f14623,plain,
    ( spl7_1740
  <=> k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1740])])).

fof(f11273,plain,
    ( spl7_1418
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1418])])).

fof(f14276,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_1418
    | ~ spl7_1708 ),
    inference(superposition,[],[f11274,f14235])).

fof(f11274,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_1418 ),
    inference(avatar_component_clause,[],[f11273])).

fof(f14618,plain,
    ( ~ spl7_1739
    | spl7_1310
    | spl7_1701
    | ~ spl7_1724 ),
    inference(avatar_split_clause,[],[f14413,f14398,f14182,f10050,f14616])).

fof(f14616,plain,
    ( spl7_1739
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1739])])).

fof(f14413,plain,
    ( v1_xboole_0(sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_1701
    | ~ spl7_1724 ),
    inference(subsumption_resolution,[],[f14401,f14183])).

fof(f14401,plain,
    ( v1_xboole_0(sK4(k4_tmap_1(sK0,sK3(sK0))))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_1724 ),
    inference(resolution,[],[f14399,f531])).

fof(f14611,plain,
    ( spl7_1736
    | ~ spl7_398
    | ~ spl7_1460 ),
    inference(avatar_split_clause,[],[f14101,f11844,f2326,f14609])).

fof(f14609,plain,
    ( spl7_1736
  <=> k4_tmap_1(sK0,sK3(sK0)) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1736])])).

fof(f11844,plain,
    ( spl7_1460
  <=> k4_tmap_1(sK0,sK3(sK0)) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1460])])).

fof(f14101,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_398
    | ~ spl7_1460 ),
    inference(superposition,[],[f11845,f2327])).

fof(f11845,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_1460 ),
    inference(avatar_component_clause,[],[f11844])).

fof(f14562,plain,
    ( spl7_1734
    | ~ spl7_398
    | ~ spl7_914 ),
    inference(avatar_split_clause,[],[f14098,f6124,f2326,f14560])).

fof(f14560,plain,
    ( spl7_1734
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1734])])).

fof(f6124,plain,
    ( spl7_914
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_914])])).

fof(f14098,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_398
    | ~ spl7_914 ),
    inference(superposition,[],[f6125,f2327])).

fof(f6125,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_914 ),
    inference(avatar_component_clause,[],[f6124])).

fof(f14453,plain,
    ( ~ spl7_1733
    | ~ spl7_398
    | spl7_1689 ),
    inference(avatar_split_clause,[],[f14446,f13957,f2326,f14451])).

fof(f14451,plain,
    ( spl7_1733
  <=> ~ m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1733])])).

fof(f13957,plain,
    ( spl7_1689
  <=> ~ m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1689])])).

fof(f14446,plain,
    ( ~ m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)),u1_struct_0(sK0))
    | ~ spl7_398
    | ~ spl7_1689 ),
    inference(superposition,[],[f13958,f2327])).

fof(f13958,plain,
    ( ~ m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_1689 ),
    inference(avatar_component_clause,[],[f13957])).

fof(f14445,plain,
    ( ~ spl7_1731
    | ~ spl7_398
    | spl7_1691 ),
    inference(avatar_split_clause,[],[f14126,f13996,f2326,f14443])).

fof(f14443,plain,
    ( spl7_1731
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1731])])).

fof(f13996,plain,
    ( spl7_1691
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1691])])).

fof(f14126,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(o_0_0_xboole_0)))
    | ~ spl7_398
    | ~ spl7_1691 ),
    inference(superposition,[],[f13997,f2327])).

fof(f13997,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_1691 ),
    inference(avatar_component_clause,[],[f13996])).

fof(f14438,plain,
    ( spl7_1728
    | ~ spl7_398
    | ~ spl7_470 ),
    inference(avatar_split_clause,[],[f14080,f2802,f2326,f14436])).

fof(f14436,plain,
    ( spl7_1728
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1728])])).

fof(f2802,plain,
    ( spl7_470
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_470])])).

fof(f14080,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_398
    | ~ spl7_470 ),
    inference(superposition,[],[f2803,f2327])).

fof(f2803,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_470 ),
    inference(avatar_component_clause,[],[f2802])).

fof(f14431,plain,
    ( ~ spl7_1727
    | ~ spl7_398
    | spl7_1405 ),
    inference(avatar_split_clause,[],[f14100,f11075,f2326,f14429])).

fof(f14429,plain,
    ( spl7_1727
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1727])])).

fof(f11075,plain,
    ( spl7_1405
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1405])])).

fof(f14100,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_398
    | ~ spl7_1405 ),
    inference(superposition,[],[f11076,f2327])).

fof(f11076,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_1405 ),
    inference(avatar_component_clause,[],[f11075])).

fof(f14400,plain,
    ( spl7_1724
    | ~ spl7_398
    | ~ spl7_530 ),
    inference(avatar_split_clause,[],[f14087,f3363,f2326,f14398])).

fof(f14087,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_530 ),
    inference(superposition,[],[f3364,f2327])).

fof(f14364,plain,
    ( spl7_1722
    | ~ spl7_298
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14075,f2326,f1684,f14362])).

fof(f1684,plain,
    ( spl7_298
  <=> m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_298])])).

fof(f14075,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_298
    | ~ spl7_398 ),
    inference(superposition,[],[f1685,f2327])).

fof(f1685,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_298 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f14357,plain,
    ( ~ spl7_1721
    | ~ spl7_398
    | spl7_505 ),
    inference(avatar_split_clause,[],[f14356,f3162,f2326,f14350])).

fof(f14350,plain,
    ( spl7_1721
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1721])])).

fof(f3162,plain,
    ( spl7_505
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_505])])).

fof(f14356,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_398
    | ~ spl7_505 ),
    inference(forward_demodulation,[],[f3163,f2327])).

fof(f3163,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_505 ),
    inference(avatar_component_clause,[],[f3162])).

fof(f14355,plain,
    ( spl7_1720
    | ~ spl7_398
    | ~ spl7_504 ),
    inference(avatar_split_clause,[],[f14085,f3165,f2326,f14353])).

fof(f14353,plain,
    ( spl7_1720
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1720])])).

fof(f3165,plain,
    ( spl7_504
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_504])])).

fof(f14085,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_398
    | ~ spl7_504 ),
    inference(superposition,[],[f3166,f2327])).

fof(f3166,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_504 ),
    inference(avatar_component_clause,[],[f3165])).

fof(f14348,plain,
    ( ~ spl7_1719
    | ~ spl7_398
    | spl7_545
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f14142,f7836,f3431,f2326,f14346])).

fof(f14346,plain,
    ( spl7_1719
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1719])])).

fof(f3431,plain,
    ( spl7_545
  <=> ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_545])])).

fof(f7836,plain,
    ( spl7_1096
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1096])])).

fof(f14142,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_545
    | ~ spl7_1096 ),
    inference(forward_demodulation,[],[f14088,f7837])).

fof(f7837,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_1096 ),
    inference(avatar_component_clause,[],[f7836])).

fof(f14088,plain,
    ( ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_545 ),
    inference(superposition,[],[f3432,f2327])).

fof(f3432,plain,
    ( ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_545 ),
    inference(avatar_component_clause,[],[f3431])).

fof(f14341,plain,
    ( ~ spl7_1717
    | ~ spl7_398
    | spl7_483 ),
    inference(avatar_split_clause,[],[f14083,f2875,f2326,f14339])).

fof(f14339,plain,
    ( spl7_1717
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1717])])).

fof(f2875,plain,
    ( spl7_483
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_483])])).

fof(f14083,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_483 ),
    inference(superposition,[],[f2876,f2327])).

fof(f2876,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_483 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f14334,plain,
    ( ~ spl7_1715
    | ~ spl7_398
    | spl7_651 ),
    inference(avatar_split_clause,[],[f14090,f4088,f2326,f14332])).

fof(f14332,plain,
    ( spl7_1715
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1715])])).

fof(f4088,plain,
    ( spl7_651
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_651])])).

fof(f14090,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl7_398
    | ~ spl7_651 ),
    inference(superposition,[],[f4089,f2327])).

fof(f4089,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl7_651 ),
    inference(avatar_component_clause,[],[f4088])).

fof(f14324,plain,
    ( ~ spl7_1713
    | ~ spl7_398
    | spl7_475 ),
    inference(avatar_split_clause,[],[f14082,f2821,f2326,f14322])).

fof(f14322,plain,
    ( spl7_1713
  <=> k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1713])])).

fof(f2821,plain,
    ( spl7_475
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_475])])).

fof(f14082,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) != o_0_0_xboole_0
    | ~ spl7_398
    | ~ spl7_475 ),
    inference(superposition,[],[f2822,f2327])).

fof(f2822,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) != o_0_0_xboole_0
    | ~ spl7_475 ),
    inference(avatar_component_clause,[],[f2821])).

fof(f14317,plain,
    ( ~ spl7_1711
    | spl7_391
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14078,f2326,f2229,f14315])).

fof(f14315,plain,
    ( spl7_1711
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1711])])).

fof(f2229,plain,
    ( spl7_391
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_391])])).

fof(f14078,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_391
    | ~ spl7_398 ),
    inference(superposition,[],[f2230,f2327])).

fof(f2230,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_391 ),
    inference(avatar_component_clause,[],[f2229])).

fof(f14304,plain,
    ( spl7_700
    | ~ spl7_808
    | ~ spl7_1708 ),
    inference(avatar_split_clause,[],[f14246,f14234,f5132,f4377])).

fof(f5132,plain,
    ( spl7_808
  <=> v1_funct_1(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_808])])).

fof(f14246,plain,
    ( v1_funct_1(k3_struct_0(sK5))
    | ~ spl7_808
    | ~ spl7_1708 ),
    inference(superposition,[],[f5133,f14235])).

fof(f5133,plain,
    ( v1_funct_1(k3_struct_0(sK3(sK0)))
    | ~ spl7_808 ),
    inference(avatar_component_clause,[],[f5132])).

fof(f14236,plain,
    ( spl7_1708
    | ~ spl7_70
    | ~ spl7_398
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f14139,f2446,f2326,f470,f14234])).

fof(f14139,plain,
    ( k3_struct_0(sK5) = k3_struct_0(sK3(sK0))
    | ~ spl7_70
    | ~ spl7_398
    | ~ spl7_424 ),
    inference(forward_demodulation,[],[f14073,f2447])).

fof(f14073,plain,
    ( k3_struct_0(sK3(sK0)) = k6_partfun1(o_0_0_xboole_0)
    | ~ spl7_70
    | ~ spl7_398 ),
    inference(superposition,[],[f471,f2327])).

fof(f14229,plain,
    ( ~ spl7_1707
    | ~ spl7_398
    | spl7_657 ),
    inference(avatar_split_clause,[],[f14091,f4124,f2326,f14227])).

fof(f14227,plain,
    ( spl7_1707
  <=> k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1707])])).

fof(f4124,plain,
    ( spl7_657
  <=> k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_657])])).

fof(f14091,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)) != o_0_0_xboole_0
    | ~ spl7_398
    | ~ spl7_657 ),
    inference(superposition,[],[f4125,f2327])).

fof(f4125,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) != o_0_0_xboole_0
    | ~ spl7_657 ),
    inference(avatar_component_clause,[],[f4124])).

fof(f14222,plain,
    ( ~ spl7_1705
    | ~ spl7_398
    | spl7_491 ),
    inference(avatar_split_clause,[],[f14084,f2932,f2326,f14220])).

fof(f14220,plain,
    ( spl7_1705
  <=> ~ m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1705])])).

fof(f2932,plain,
    ( spl7_491
  <=> ~ m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_491])])).

fof(f14084,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_491 ),
    inference(superposition,[],[f2933,f2327])).

fof(f2933,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_491 ),
    inference(avatar_component_clause,[],[f2932])).

fof(f14203,plain,
    ( ~ spl7_1703
    | ~ spl7_398
    | spl7_473 ),
    inference(avatar_split_clause,[],[f14081,f2805,f2326,f14201])).

fof(f2805,plain,
    ( spl7_473
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_473])])).

fof(f14081,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))))
    | ~ spl7_398
    | ~ spl7_473 ),
    inference(superposition,[],[f2806,f2327])).

fof(f2806,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_473 ),
    inference(avatar_component_clause,[],[f2805])).

fof(f14184,plain,
    ( ~ spl7_1701
    | ~ spl7_398
    | spl7_507 ),
    inference(avatar_split_clause,[],[f14086,f3168,f2326,f14182])).

fof(f3168,plain,
    ( spl7_507
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_507])])).

fof(f14086,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_398
    | ~ spl7_507 ),
    inference(superposition,[],[f3169,f2327])).

fof(f3169,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_507 ),
    inference(avatar_component_clause,[],[f3168])).

fof(f14177,plain,
    ( ~ spl7_1699
    | spl7_393
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14176,f2326,f2280,f14170])).

fof(f14170,plain,
    ( spl7_1699
  <=> ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1699])])).

fof(f2280,plain,
    ( spl7_393
  <=> ~ v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_393])])).

fof(f14176,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl7_393
    | ~ spl7_398 ),
    inference(forward_demodulation,[],[f2281,f2327])).

fof(f2281,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl7_393 ),
    inference(avatar_component_clause,[],[f2280])).

fof(f14175,plain,
    ( spl7_1698
    | ~ spl7_392
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14079,f2326,f2283,f14173])).

fof(f14173,plain,
    ( spl7_1698
  <=> v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1698])])).

fof(f2283,plain,
    ( spl7_392
  <=> v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_392])])).

fof(f14079,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl7_392
    | ~ spl7_398 ),
    inference(superposition,[],[f2284,f2327])).

fof(f2284,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ spl7_392 ),
    inference(avatar_component_clause,[],[f2283])).

fof(f14168,plain,
    ( ~ spl7_1697
    | spl7_301
    | ~ spl7_398 ),
    inference(avatar_split_clause,[],[f14076,f2326,f1695,f14166])).

fof(f14166,plain,
    ( spl7_1697
  <=> ~ v1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1697])])).

fof(f1695,plain,
    ( spl7_301
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_301])])).

fof(f14076,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,u1_struct_0(sK0)))
    | ~ spl7_301
    | ~ spl7_398 ),
    inference(superposition,[],[f1696,f2327])).

fof(f1696,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_301 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f14071,plain,
    ( spl7_398
    | ~ spl7_20
    | ~ spl7_684 ),
    inference(avatar_split_clause,[],[f14056,f4310,f223,f2326])).

fof(f4310,plain,
    ( spl7_684
  <=> v1_xboole_0(u1_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_684])])).

fof(f14056,plain,
    ( u1_struct_0(sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_684 ),
    inference(forward_demodulation,[],[f14040,f224])).

fof(f14040,plain,
    ( u1_struct_0(sK3(sK0)) = k1_xboole_0
    | ~ spl7_684 ),
    inference(resolution,[],[f4311,f117])).

fof(f4311,plain,
    ( v1_xboole_0(u1_struct_0(sK3(sK0)))
    | ~ spl7_684 ),
    inference(avatar_component_clause,[],[f4310])).

fof(f14038,plain,
    ( spl7_1694
    | ~ spl7_62
    | spl7_117
    | ~ spl7_1688 ),
    inference(avatar_split_clause,[],[f13980,f13960,f681,f438,f14036])).

fof(f14036,plain,
    ( spl7_1694
  <=> k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1694])])).

fof(f438,plain,
    ( spl7_62
  <=> k3_struct_0(sK0) = k6_partfun1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f681,plain,
    ( spl7_117
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f13960,plain,
    ( spl7_1688
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1688])])).

fof(f13980,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_62
    | ~ spl7_117
    | ~ spl7_1688 ),
    inference(forward_demodulation,[],[f13979,f439])).

fof(f439,plain,
    ( k3_struct_0(sK0) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f438])).

fof(f13979,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_117
    | ~ spl7_1688 ),
    inference(subsumption_resolution,[],[f13965,f682])).

fof(f682,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_117 ),
    inference(avatar_component_clause,[],[f681])).

fof(f13965,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_1688 ),
    inference(resolution,[],[f13961,f601])).

fof(f13961,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_1688 ),
    inference(avatar_component_clause,[],[f13960])).

fof(f14005,plain,
    ( spl7_1678
    | spl7_1656
    | ~ spl7_1640
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13719,f13504,f13461,f13754,f13881])).

fof(f13881,plain,
    ( spl7_1678
  <=> ! [X10] :
        ( k1_funct_1(k6_partfun1(X10),sK4(X10)) = sK4(X10)
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),X10) = X10 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1678])])).

fof(f13754,plain,
    ( spl7_1656
  <=> k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1656])])).

fof(f13719,plain,
    ( ! [X0] :
        ( k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),X0) = X0
        | k1_funct_1(k6_partfun1(X0),sK4(X0)) = sK4(X0) )
    | ~ spl7_1640
    | ~ spl7_1644 ),
    inference(forward_demodulation,[],[f13648,f13505])).

fof(f13648,plain,
    ( ! [X0] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),X0) = X0
        | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
        | k1_funct_1(k6_partfun1(X0),sK4(X0)) = sK4(X0) )
    | ~ spl7_1640 ),
    inference(superposition,[],[f13475,f13475])).

fof(f14004,plain,
    ( ~ spl7_1691
    | spl7_1692
    | spl7_117
    | ~ spl7_1688 ),
    inference(avatar_split_clause,[],[f13978,f13960,f681,f14002,f13996])).

fof(f14002,plain,
    ( spl7_1692
  <=> v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1692])])).

fof(f13978,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_117
    | ~ spl7_1688 ),
    inference(subsumption_resolution,[],[f13964,f682])).

fof(f13964,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))))
    | ~ spl7_1688 ),
    inference(resolution,[],[f13961,f531])).

fof(f13962,plain,
    ( spl7_1688
    | ~ spl7_1430
    | ~ spl7_1686 ),
    inference(avatar_split_clause,[],[f13955,f13952,f11611,f13960])).

fof(f11611,plain,
    ( spl7_1430
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1430])])).

fof(f13952,plain,
    ( spl7_1686
  <=> k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1686])])).

fof(f13955,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_1430
    | ~ spl7_1686 ),
    inference(superposition,[],[f11612,f13953])).

fof(f13953,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))
    | ~ spl7_1686 ),
    inference(avatar_component_clause,[],[f13952])).

fof(f11612,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_1430 ),
    inference(avatar_component_clause,[],[f11611])).

fof(f13954,plain,
    ( spl7_1686
    | ~ spl7_1674 ),
    inference(avatar_split_clause,[],[f13920,f13870,f13952])).

fof(f13870,plain,
    ( spl7_1674
  <=> ! [X1] :
        ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),X1) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1674])])).

fof(f13920,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0))))
    | ~ spl7_1674 ),
    inference(resolution,[],[f13871,f121])).

fof(f13871,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),X1) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1) )
    | ~ spl7_1674 ),
    inference(avatar_component_clause,[],[f13870])).

fof(f13947,plain,
    ( spl7_1684
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13831,f13588,f13504,f789,f326,f13945])).

fof(f13945,plain,
    ( spl7_1684
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1684])])).

fof(f326,plain,
    ( spl7_42
  <=> l1_pre_topc(sK3(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f789,plain,
    ( spl7_138
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f13588,plain,
    ( spl7_1653
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1653])])).

fof(f13831,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13820,f13505])).

fof(f13820,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f13104])).

fof(f13104,plain,
    ( ! [X34] :
        ( v1_xboole_0(X34)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(X34)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),X34),sK4(X34)) )
    | ~ spl7_42
    | ~ spl7_138 ),
    inference(resolution,[],[f12742,f121])).

fof(f12742,plain,
    ( ! [X14,X15] :
        ( ~ m1_subset_1(X15,X14)
        | v1_xboole_0(X14)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),X15) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),X14),X15) )
    | ~ spl7_42
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f12720,f327])).

fof(f327,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f326])).

fof(f12720,plain,
    ( ! [X14,X15] :
        ( v1_xboole_0(X14)
        | ~ m1_subset_1(X15,X14)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),X15) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),X14),X15)
        | ~ l1_pre_topc(sK3(sK3(sK3(sK1)))) )
    | ~ spl7_138 ),
    inference(resolution,[],[f5456,f790])).

fof(f790,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))))
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f789])).

fof(f5456,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(k3_struct_0(X2))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,X3)
      | k1_funct_1(k3_struct_0(X2),X4) = k1_funct_1(k7_relat_1(k3_struct_0(X2),X3),X4)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f2704,f114])).

fof(f2704,plain,(
    ! [X6,X4,X5] :
      ( ~ l1_struct_0(X4)
      | ~ v1_relat_1(k3_struct_0(X4))
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X5,X6)
      | k1_funct_1(k3_struct_0(X4),X5) = k1_funct_1(k7_relat_1(k3_struct_0(X4),X6),X5) ) ),
    inference(resolution,[],[f1069,f110])).

fof(f13589,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1653 ),
    inference(avatar_component_clause,[],[f13588])).

fof(f13940,plain,
    ( spl7_1682
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13830,f13588,f13504,f773,f316,f13938])).

fof(f13938,plain,
    ( spl7_1682
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1682])])).

fof(f316,plain,
    ( spl7_40
  <=> l1_pre_topc(sK3(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f773,plain,
    ( spl7_134
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f13830,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13819,f13505])).

fof(f13819,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f12897])).

fof(f12897,plain,
    ( ! [X34] :
        ( v1_xboole_0(X34)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(X34)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),X34),sK4(X34)) )
    | ~ spl7_40
    | ~ spl7_134 ),
    inference(resolution,[],[f12741,f121])).

fof(f12741,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X13,X12)
        | v1_xboole_0(X12)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),X13) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),X12),X13) )
    | ~ spl7_40
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f12719,f317])).

fof(f317,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f316])).

fof(f12719,plain,
    ( ! [X12,X13] :
        ( v1_xboole_0(X12)
        | ~ m1_subset_1(X13,X12)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),X13) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),X12),X13)
        | ~ l1_pre_topc(sK3(sK3(sK3(sK0)))) )
    | ~ spl7_134 ),
    inference(resolution,[],[f5456,f774])).

fof(f774,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))))
    | ~ spl7_134 ),
    inference(avatar_component_clause,[],[f773])).

fof(f13933,plain,
    ( spl7_1656
    | spl7_1666
    | ~ spl7_20
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13543,f13504,f5476,f511,f223,f13843,f13754])).

fof(f13843,plain,
    ( spl7_1666
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1666])])).

fof(f13543,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1644 ),
    inference(superposition,[],[f8632,f13505])).

fof(f8632,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK6),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_80
    | ~ spl7_832 ),
    inference(forward_demodulation,[],[f8595,f224])).

fof(f8595,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK6),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_80
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f117])).

fof(f13932,plain,
    ( spl7_1656
    | spl7_1662
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13537,f13504,f5067,f463,f223,f13775,f13754])).

fof(f13775,plain,
    ( spl7_1662
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1662])])).

fof(f13537,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1644 ),
    inference(superposition,[],[f5445,f13505])).

fof(f5445,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK1),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(forward_demodulation,[],[f5419,f224])).

fof(f5419,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK1),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f117])).

fof(f13931,plain,
    ( spl7_1656
    | spl7_1660
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13536,f13504,f5040,f447,f223,f13768,f13754])).

fof(f13768,plain,
    ( spl7_1660
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1660])])).

fof(f13536,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1644 ),
    inference(superposition,[],[f5328,f13505])).

fof(f5328,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK0),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f5302,f224])).

fof(f5302,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK0),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f117])).

fof(f13930,plain,
    ( spl7_1670
    | spl7_1652
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13574,f13561,f5169,f495,f13591,f13857])).

fof(f13857,plain,
    ( spl7_1670
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1670])])).

fof(f13591,plain,
    ( spl7_1652
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1652])])).

fof(f495,plain,
    ( spl7_76
  <=> v1_relat_1(k3_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f5169,plain,
    ( spl7_814
  <=> v1_funct_1(k3_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_814])])).

fof(f13561,plain,
    ( spl7_1648
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1648])])).

fof(f13574,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5193])).

fof(f5193,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK3(sK1)),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X7),X6) )
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(subsumption_resolution,[],[f5190,f496])).

fof(f496,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK1)))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f495])).

fof(f5190,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK3(sK1)),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK3(sK1)))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_814 ),
    inference(resolution,[],[f5170,f1069])).

fof(f5170,plain,
    ( v1_funct_1(k3_struct_0(sK3(sK1)))
    | ~ spl7_814 ),
    inference(avatar_component_clause,[],[f5169])).

fof(f13562,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1648 ),
    inference(avatar_component_clause,[],[f13561])).

fof(f13929,plain,
    ( spl7_1668
    | spl7_1652
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13573,f13561,f5132,f479,f13591,f13850])).

fof(f13850,plain,
    ( spl7_1668
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1668])])).

fof(f479,plain,
    ( spl7_72
  <=> v1_relat_1(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f13573,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5159])).

fof(f5159,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK3(sK0)),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X7),X6) )
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(subsumption_resolution,[],[f5156,f480])).

fof(f480,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK0)))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f479])).

fof(f5156,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK3(sK0)),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK3(sK0)))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_808 ),
    inference(resolution,[],[f5133,f1069])).

fof(f13928,plain,
    ( spl7_1656
    | spl7_1664
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_52
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13542,f13504,f377,f223,f186,f13836,f13754])).

fof(f13836,plain,
    ( spl7_1664
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1664])])).

fof(f377,plain,
    ( spl7_52
  <=> v1_relat_1(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f13542,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_52
    | ~ spl7_1644 ),
    inference(superposition,[],[f7309,f13505])).

fof(f7309,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK5),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f7276,f224])).

fof(f7276,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK5),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_10
    | ~ spl7_52 ),
    inference(resolution,[],[f7231,f117])).

fof(f7231,plain,
    ( ! [X26] :
        ( v1_xboole_0(X26)
        | k1_funct_1(k3_struct_0(sK5),sK4(X26)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),X26),sK4(X26)) )
    | ~ spl7_10
    | ~ spl7_52 ),
    inference(resolution,[],[f5457,f121])).

fof(f5457,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | k1_funct_1(k3_struct_0(sK5),X1) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),X0),X1) )
    | ~ spl7_10
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f5455,f378])).

fof(f378,plain,
    ( v1_relat_1(k3_struct_0(sK5))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f377])).

fof(f5455,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k3_struct_0(sK5))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | k1_funct_1(k3_struct_0(sK5),X1) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),X0),X1) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2704,f187])).

fof(f13927,plain,
    ( spl7_1680
    | spl7_1650
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13533,f13504,f13585,f13925])).

fof(f13925,plain,
    ( spl7_1680
  <=> ! [X10] :
        ( k1_zfmisc_1(u1_struct_0(sK3(sK0))) = X10
        | k1_funct_1(k6_partfun1(X10),sK4(X10)) = sK4(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1680])])).

fof(f13585,plain,
    ( spl7_1650
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1650])])).

fof(f13533,plain,
    ( ! [X10] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
        | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = X10
        | k1_funct_1(k6_partfun1(X10),sK4(X10)) = sK4(X10) )
    | ~ spl7_1644 ),
    inference(superposition,[],[f1295,f13505])).

fof(f1295,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | k1_funct_1(k6_partfun1(X1),sK4(X1)) = sK4(X1)
      | k1_funct_1(k6_partfun1(X2),sK4(X2)) = sK4(X2) ) ),
    inference(resolution,[],[f890,f858])).

fof(f13883,plain,
    ( spl7_1652
    | spl7_1678
    | ~ spl7_1640 ),
    inference(avatar_split_clause,[],[f13726,f13461,f13881,f13591])).

fof(f13726,plain,
    ( ! [X10] :
        ( k1_funct_1(k6_partfun1(X10),sK4(X10)) = sK4(X10)
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),X10) = X10 )
    | ~ spl7_1640 ),
    inference(resolution,[],[f13678,f601])).

fof(f13678,plain,
    ( ! [X34] :
        ( m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(sK3(sK0))))
        | k1_funct_1(k6_partfun1(X34),sK4(X34)) = sK4(X34) )
    | ~ spl7_1640 ),
    inference(superposition,[],[f121,f13475])).

fof(f13879,plain,
    ( spl7_1676
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13827,f13588,f13504,f6299,f575,f13877])).

fof(f13877,plain,
    ( spl7_1676
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1676])])).

fof(f575,plain,
    ( spl7_94
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f6299,plain,
    ( spl7_956
  <=> v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_956])])).

fof(f13827,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13816,f13505])).

fof(f13816,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f6667])).

fof(f6667,plain,
    ( ! [X26] :
        ( v1_xboole_0(X26)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(X26)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X26),sK4(X26)) )
    | ~ spl7_94
    | ~ spl7_956 ),
    inference(resolution,[],[f6323,f121])).

fof(f6323,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X7),X6) )
    | ~ spl7_94
    | ~ spl7_956 ),
    inference(subsumption_resolution,[],[f6320,f576])).

fof(f576,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f575])).

fof(f6320,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK3(sK3(sK1))))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_956 ),
    inference(resolution,[],[f6300,f1069])).

fof(f6300,plain,
    ( v1_funct_1(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_956 ),
    inference(avatar_component_clause,[],[f6299])).

fof(f13872,plain,
    ( spl7_1674
    | spl7_684
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f6179,f165,f158,f151,f4310,f13870])).

fof(f6179,plain,
    ( ! [X1] :
        ( v1_xboole_0(u1_struct_0(sK3(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),X1) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f6177,f166])).

fof(f6177,plain,
    ( ! [X1] :
        ( v1_xboole_0(u1_struct_0(sK3(sK0)))
        | k1_funct_1(k4_tmap_1(sK0,sK3(sK0)),X1) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f3945,f116])).

fof(f116,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',existence_m1_pre_topc)).

fof(f3945,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | k1_funct_1(k4_tmap_1(sK0,X0),X1) = k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3944,f152])).

fof(f3944,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k4_tmap_1(sK0,X0),X1) = k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3943,f166])).

fof(f3943,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k4_tmap_1(sK0,X0),X1) = k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1)
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f1855,f159])).

fof(f1855,plain,(
    ! [X4,X2,X3] :
      ( ~ v2_pre_topc(X4)
      | k1_funct_1(k4_tmap_1(X4,X3),X2) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2)
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1854,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1854,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | k1_funct_1(k4_tmap_1(X4,X3),X2) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2)
      | ~ v1_funct_1(k4_tmap_1(X4,X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1851,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1851,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(k4_tmap_1(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | k1_funct_1(k4_tmap_1(X4,X3),X2) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2)
      | ~ v1_funct_1(k4_tmap_1(X4,X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f136,f128])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',redefinition_k3_funct_2)).

fof(f13868,plain,
    ( spl7_1672
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13826,f13588,f13504,f6261,f556,f13866])).

fof(f13866,plain,
    ( spl7_1672
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1672])])).

fof(f556,plain,
    ( spl7_90
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f6261,plain,
    ( spl7_950
  <=> v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_950])])).

fof(f13826,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13815,f13505])).

fof(f13815,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f6386])).

fof(f6386,plain,
    ( ! [X26] :
        ( v1_xboole_0(X26)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(X26)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X26),sK4(X26)) )
    | ~ spl7_90
    | ~ spl7_950 ),
    inference(resolution,[],[f6287,f121])).

fof(f6287,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X6,X7)
        | v1_xboole_0(X7)
        | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X7),X6) )
    | ~ spl7_90
    | ~ spl7_950 ),
    inference(subsumption_resolution,[],[f6284,f557])).

fof(f557,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK0))))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f556])).

fof(f6284,plain,
    ( ! [X6,X7] :
        ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),X6) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X7),X6)
        | ~ v1_relat_1(k3_struct_0(sK3(sK3(sK0))))
        | v1_xboole_0(X7)
        | ~ m1_subset_1(X6,X7) )
    | ~ spl7_950 ),
    inference(resolution,[],[f6262,f1069])).

fof(f6262,plain,
    ( v1_funct_1(k3_struct_0(sK3(sK3(sK0))))
    | ~ spl7_950 ),
    inference(avatar_component_clause,[],[f6261])).

fof(f13861,plain,
    ( spl7_1666
    | spl7_1652
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13576,f13561,f5476,f511,f13591,f13843])).

fof(f13576,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5500])).

fof(f13860,plain,
    ( spl7_1664
    | spl7_1652
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13575,f13561,f377,f186,f13591,f13836])).

fof(f13575,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5457])).

fof(f13859,plain,
    ( spl7_1670
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13825,f13588,f13504,f5169,f495,f13857])).

fof(f13825,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13814,f13505])).

fof(f13814,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f5949])).

fof(f5949,plain,
    ( ! [X25] :
        ( v1_xboole_0(X25)
        | k1_funct_1(k3_struct_0(sK3(sK1)),sK4(X25)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X25),sK4(X25)) )
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f121])).

fof(f13852,plain,
    ( spl7_1668
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13824,f13588,f13504,f5132,f479,f13850])).

fof(f13824,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13813,f13505])).

fof(f13813,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f5807])).

fof(f5807,plain,
    ( ! [X24] :
        ( v1_xboole_0(X24)
        | k1_funct_1(k3_struct_0(sK3(sK0)),sK4(X24)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X24),sK4(X24)) )
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f121])).

fof(f13845,plain,
    ( spl7_1666
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13829,f13588,f13504,f5476,f511,f13843])).

fof(f13829,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13818,f13505])).

fof(f13818,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f8527])).

fof(f13838,plain,
    ( spl7_1664
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1644
    | spl7_1653 ),
    inference(avatar_split_clause,[],[f13828,f13588,f13504,f377,f186,f13836])).

fof(f13828,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1644
    | ~ spl7_1653 ),
    inference(forward_demodulation,[],[f13817,f13505])).

fof(f13817,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1653 ),
    inference(resolution,[],[f13589,f7231])).

fof(f13809,plain,
    ( spl7_1656
    | ~ spl7_20
    | ~ spl7_1652 ),
    inference(avatar_split_clause,[],[f13794,f13591,f223,f13754])).

fof(f13794,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1652 ),
    inference(forward_demodulation,[],[f13778,f224])).

fof(f13778,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3(sK0))) = k1_xboole_0
    | ~ spl7_1652 ),
    inference(resolution,[],[f13592,f117])).

fof(f13592,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1652 ),
    inference(avatar_component_clause,[],[f13591])).

fof(f13777,plain,
    ( spl7_1662
    | spl7_1652
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13572,f13561,f5067,f463,f13591,f13775])).

fof(f13572,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5082])).

fof(f13770,plain,
    ( spl7_1660
    | spl7_1652
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13571,f13561,f5040,f447,f13591,f13768])).

fof(f13571,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f5055])).

fof(f13763,plain,
    ( spl7_1658
    | spl7_1650
    | ~ spl7_8
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13535,f13504,f179,f13585,f13761])).

fof(f13761,plain,
    ( spl7_1658
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1658])])).

fof(f13535,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_8
    | ~ spl7_1644 ),
    inference(superposition,[],[f3740,f13505])).

fof(f3740,plain,
    ( ! [X5] :
        ( k1_funct_1(k6_partfun1(X5),sK4(X5)) = sK4(X5)
        | o_0_0_xboole_0 = sK4(k1_zfmisc_1(X5)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f3732,f350])).

fof(f13756,plain,
    ( spl7_1656
    | spl7_1650
    | ~ spl7_8
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13532,f13504,f179,f13585,f13754])).

fof(f13532,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_1644 ),
    inference(superposition,[],[f889,f13505])).

fof(f13611,plain,
    ( spl7_1654
    | ~ spl7_701
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f13599,f665,f186,f4380,f13609])).

fof(f13609,plain,
    ( spl7_1654
  <=> v1_funct_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1654])])).

fof(f4380,plain,
    ( spl7_701
  <=> ~ v1_funct_1(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_701])])).

fof(f665,plain,
    ( spl7_112
  <=> m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f13599,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5))
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f13598,f187])).

fof(f13598,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | v1_funct_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f13594,f666])).

fof(f666,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f665])).

fof(f13594,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | v1_funct_1(k2_tmap_1(sK5,sK5,k3_struct_0(sK5),sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl7_10 ),
    inference(resolution,[],[f6589,f111])).

fof(f6589,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK5),u1_struct_0(sK5))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | v1_funct_1(k2_tmap_1(sK5,sK5,X0,sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f3450,f187])).

fof(f13593,plain,
    ( spl7_1650
    | spl7_1652
    | ~ spl7_1648 ),
    inference(avatar_split_clause,[],[f13570,f13561,f13591,f13585])).

fof(f13570,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1648 ),
    inference(resolution,[],[f13562,f601])).

fof(f13563,plain,
    ( spl7_1648
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13530,f13504,f13561])).

fof(f13530,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1644 ),
    inference(superposition,[],[f121,f13505])).

fof(f13556,plain,
    ( ~ spl7_1647
    | spl7_189
    | ~ spl7_1644 ),
    inference(avatar_split_clause,[],[f13548,f13504,f1061,f13554])).

fof(f13554,plain,
    ( spl7_1647
  <=> ~ v1_relat_1(u1_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1647])])).

fof(f13548,plain,
    ( ~ v1_relat_1(u1_struct_0(sK3(sK0)))
    | ~ spl7_189
    | ~ spl7_1644 ),
    inference(subsumption_resolution,[],[f13508,f1062])).

fof(f13508,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(u1_struct_0(sK3(sK0)))
    | ~ spl7_1644 ),
    inference(superposition,[],[f400,f13505])).

fof(f13506,plain,
    ( spl7_1644
    | ~ spl7_20
    | ~ spl7_1640 ),
    inference(avatar_split_clause,[],[f13486,f13461,f223,f13504])).

fof(f13486,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_20
    | ~ spl7_1640 ),
    inference(forward_demodulation,[],[f13470,f224])).

fof(f13470,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0))))
    | ~ spl7_1640 ),
    inference(resolution,[],[f13462,f117])).

fof(f13469,plain,
    ( spl7_1640
    | spl7_1642
    | ~ spl7_1420 ),
    inference(avatar_split_clause,[],[f11604,f11298,f13467,f13461])).

fof(f13467,plain,
    ( spl7_1642
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1642])])).

fof(f11298,plain,
    ( spl7_1420
  <=> ! [X1] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1420])])).

fof(f11604,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))),u1_struct_0(sK0))
    | v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK3(sK0)))))
    | ~ spl7_1420 ),
    inference(resolution,[],[f11299,f1209])).

fof(f11299,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1),u1_struct_0(sK0)) )
    | ~ spl7_1420 ),
    inference(avatar_component_clause,[],[f11298])).

fof(f13452,plain,
    ( spl7_1638
    | ~ spl7_42
    | ~ spl7_138
    | spl7_485 ),
    inference(avatar_split_clause,[],[f13227,f2881,f789,f326,f13450])).

fof(f13450,plain,
    ( spl7_1638
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1638])])).

fof(f2881,plain,
    ( spl7_485
  <=> ~ v1_xboole_0(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_485])])).

fof(f13227,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_485 ),
    inference(resolution,[],[f13104,f2882])).

fof(f2882,plain,
    ( ~ v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl7_485 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f13445,plain,
    ( spl7_1636
    | ~ spl7_42
    | ~ spl7_138
    | spl7_357 ),
    inference(avatar_split_clause,[],[f13211,f1983,f789,f326,f13443])).

fof(f13443,plain,
    ( spl7_1636
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1636])])).

fof(f13211,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_357 ),
    inference(resolution,[],[f13104,f1984])).

fof(f13438,plain,
    ( spl7_1634
    | ~ spl7_42
    | ~ spl7_138
    | spl7_349 ),
    inference(avatar_split_clause,[],[f13210,f1947,f789,f326,f13436])).

fof(f13436,plain,
    ( spl7_1634
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1634])])).

fof(f1947,plain,
    ( spl7_349
  <=> ~ v1_xboole_0(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_349])])).

fof(f13210,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_349 ),
    inference(resolution,[],[f13104,f1948])).

fof(f1948,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK5))
    | ~ spl7_349 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f13431,plain,
    ( spl7_1632
    | ~ spl7_42
    | ~ spl7_138
    | spl7_195 ),
    inference(avatar_split_clause,[],[f13206,f1102,f789,f326,f13429])).

fof(f13429,plain,
    ( spl7_1632
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1632])])).

fof(f13206,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_195 ),
    inference(resolution,[],[f13104,f1103])).

fof(f13423,plain,
    ( spl7_1630
    | ~ spl7_28
    | ~ spl7_156
    | spl7_451 ),
    inference(avatar_split_clause,[],[f13407,f2709,f911,f258,f13421])).

fof(f13421,plain,
    ( spl7_1630
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1630])])).

fof(f258,plain,
    ( spl7_28
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f911,plain,
    ( spl7_156
  <=> k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f2709,plain,
    ( spl7_451
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_451])])).

fof(f13407,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1))
    | ~ spl7_28
    | ~ spl7_156
    | ~ spl7_451 ),
    inference(forward_demodulation,[],[f13406,f912])).

fof(f912,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1))
    | ~ spl7_156 ),
    inference(avatar_component_clause,[],[f911])).

fof(f13406,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(u1_struct_0(sK1)))
    | ~ spl7_28
    | ~ spl7_451 ),
    inference(subsumption_resolution,[],[f13385,f259])).

fof(f259,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f258])).

fof(f13385,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_451 ),
    inference(resolution,[],[f6466,f2710])).

fof(f2710,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_451 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f6466,plain,(
    ! [X3] :
      ( v1_xboole_0(u1_struct_0(X3))
      | k1_funct_1(k3_struct_0(X3),sK4(u1_struct_0(X3))) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X3),k3_struct_0(X3),sK4(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f3337,f121])).

fof(f3337,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | k1_funct_1(k3_struct_0(X1),X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f1853,f114])).

fof(f1853,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k1_funct_1(k3_struct_0(X1),X0) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1852,f110])).

fof(f1852,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k1_funct_1(k3_struct_0(X1),X0) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0)
      | ~ v1_funct_1(k3_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1850,f112])).

fof(f1850,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | k1_funct_1(k3_struct_0(X1),X0) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0)
      | ~ v1_funct_1(k3_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f136,f111])).

fof(f13415,plain,
    ( spl7_1628
    | ~ spl7_4
    | spl7_117
    | ~ spl7_154 ),
    inference(avatar_split_clause,[],[f13405,f901,f681,f165,f13413])).

fof(f13413,plain,
    ( spl7_1628
  <=> k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1628])])).

fof(f901,plain,
    ( spl7_154
  <=> k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f13405,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_117
    | ~ spl7_154 ),
    inference(forward_demodulation,[],[f13404,f902])).

fof(f902,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0))
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f901])).

fof(f13404,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK4(u1_struct_0(sK0)))
    | ~ spl7_4
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f13384,f166])).

fof(f13384,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK4(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_117 ),
    inference(resolution,[],[f6466,f682])).

fof(f13382,plain,
    ( spl7_1626
    | ~ spl7_42
    | ~ spl7_138
    | spl7_181 ),
    inference(avatar_split_clause,[],[f13205,f1019,f789,f326,f13380])).

fof(f13380,plain,
    ( spl7_1626
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1626])])).

fof(f13205,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_181 ),
    inference(resolution,[],[f13104,f1020])).

fof(f13375,plain,
    ( spl7_1624
    | ~ spl7_42
    | ~ spl7_138
    | spl7_451 ),
    inference(avatar_split_clause,[],[f13202,f2709,f789,f326,f13373])).

fof(f13373,plain,
    ( spl7_1624
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1624])])).

fof(f13202,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_451 ),
    inference(resolution,[],[f13104,f2710])).

fof(f13368,plain,
    ( spl7_1622
    | ~ spl7_42
    | spl7_117
    | ~ spl7_138 ),
    inference(avatar_split_clause,[],[f13201,f789,f681,f326,f13366])).

fof(f13366,plain,
    ( spl7_1622
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1622])])).

fof(f13201,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_42
    | ~ spl7_117
    | ~ spl7_138 ),
    inference(resolution,[],[f13104,f682])).

fof(f13361,plain,
    ( spl7_1620
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_642
    | spl7_649 ),
    inference(avatar_split_clause,[],[f13152,f4078,f4053,f789,f326,f13359])).

fof(f13359,plain,
    ( spl7_1620
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1620])])).

fof(f4053,plain,
    ( spl7_642
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_642])])).

fof(f4078,plain,
    ( spl7_649
  <=> ~ v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_649])])).

fof(f13152,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_642
    | ~ spl7_649 ),
    inference(subsumption_resolution,[],[f13096,f4079])).

fof(f4079,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_649 ),
    inference(avatar_component_clause,[],[f4078])).

fof(f13096,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_642 ),
    inference(resolution,[],[f12742,f4054])).

fof(f4054,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_642 ),
    inference(avatar_component_clause,[],[f4053])).

fof(f13350,plain,
    ( spl7_1618
    | ~ spl7_40
    | ~ spl7_134
    | spl7_485 ),
    inference(avatar_split_clause,[],[f13020,f2881,f773,f316,f13348])).

fof(f13348,plain,
    ( spl7_1618
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1618])])).

fof(f13020,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_485 ),
    inference(resolution,[],[f12897,f2882])).

fof(f13343,plain,
    ( spl7_1616
    | ~ spl7_40
    | ~ spl7_134
    | spl7_357 ),
    inference(avatar_split_clause,[],[f13004,f1983,f773,f316,f13341])).

fof(f13341,plain,
    ( spl7_1616
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1616])])).

fof(f13004,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_357 ),
    inference(resolution,[],[f12897,f1984])).

fof(f13336,plain,
    ( spl7_1614
    | ~ spl7_40
    | ~ spl7_134
    | spl7_349 ),
    inference(avatar_split_clause,[],[f13003,f1947,f773,f316,f13334])).

fof(f13334,plain,
    ( spl7_1614
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1614])])).

fof(f13003,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_349 ),
    inference(resolution,[],[f12897,f1948])).

fof(f13329,plain,
    ( spl7_1612
    | ~ spl7_40
    | ~ spl7_134
    | spl7_195 ),
    inference(avatar_split_clause,[],[f12999,f1102,f773,f316,f13327])).

fof(f13327,plain,
    ( spl7_1612
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1612])])).

fof(f12999,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_195 ),
    inference(resolution,[],[f12897,f1103])).

fof(f13322,plain,
    ( spl7_1610
    | ~ spl7_40
    | ~ spl7_134
    | spl7_181 ),
    inference(avatar_split_clause,[],[f12998,f1019,f773,f316,f13320])).

fof(f13320,plain,
    ( spl7_1610
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1610])])).

fof(f12998,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_181 ),
    inference(resolution,[],[f12897,f1020])).

fof(f13315,plain,
    ( spl7_1608
    | ~ spl7_40
    | ~ spl7_134
    | spl7_451 ),
    inference(avatar_split_clause,[],[f12995,f2709,f773,f316,f13313])).

fof(f13313,plain,
    ( spl7_1608
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1608])])).

fof(f12995,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_451 ),
    inference(resolution,[],[f12897,f2710])).

fof(f13308,plain,
    ( spl7_1606
    | ~ spl7_40
    | spl7_117
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f12994,f773,f681,f316,f13306])).

fof(f13306,plain,
    ( spl7_1606
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1606])])).

fof(f12994,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_40
    | ~ spl7_117
    | ~ spl7_134 ),
    inference(resolution,[],[f12897,f682])).

fof(f13301,plain,
    ( spl7_1604
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_642
    | spl7_649 ),
    inference(avatar_split_clause,[],[f12945,f4078,f4053,f773,f316,f13299])).

fof(f13299,plain,
    ( spl7_1604
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1604])])).

fof(f12945,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_642
    | ~ spl7_649 ),
    inference(subsumption_resolution,[],[f12889,f4079])).

fof(f12889,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_642 ),
    inference(resolution,[],[f12741,f4054])).

fof(f13273,plain,
    ( spl7_1602
    | ~ spl7_80
    | ~ spl7_832
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12359,f12114,f5476,f511,f13271])).

fof(f13271,plain,
    ( spl7_1602
  <=> k1_funct_1(k3_struct_0(sK6),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1602])])).

fof(f12114,plain,
    ( spl7_1499
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1499])])).

fof(f12359,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f8527])).

fof(f12115,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1499 ),
    inference(avatar_component_clause,[],[f12114])).

fof(f13266,plain,
    ( spl7_1600
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12352,f12114,f5040,f447,f13264])).

fof(f13264,plain,
    ( spl7_1600
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1600])])).

fof(f12352,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f5246])).

fof(f13259,plain,
    ( spl7_1598
    | ~ spl7_10
    | ~ spl7_52
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12358,f12114,f377,f186,f13257])).

fof(f13257,plain,
    ( spl7_1598
  <=> k1_funct_1(k3_struct_0(sK5),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1598])])).

fof(f12358,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f7231])).

fof(f13248,plain,
    ( spl7_1596
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1100
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f13155,f7903,f7880,f789,f326,f13246])).

fof(f13246,plain,
    ( spl7_1596
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1596])])).

fof(f7880,plain,
    ( spl7_1100
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1100])])).

fof(f7903,plain,
    ( spl7_1105
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1105])])).

fof(f13155,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1100
    | ~ spl7_1105 ),
    inference(subsumption_resolution,[],[f13099,f7904])).

fof(f7904,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_1105 ),
    inference(avatar_component_clause,[],[f7903])).

fof(f13099,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_1100 ),
    inference(resolution,[],[f12742,f7881])).

fof(f7881,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_1100 ),
    inference(avatar_component_clause,[],[f7880])).

fof(f13241,plain,
    ( spl7_1594
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_524
    | spl7_535 ),
    inference(avatar_split_clause,[],[f13153,f3395,f3319,f789,f326,f13239])).

fof(f13239,plain,
    ( spl7_1594
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1594])])).

fof(f3319,plain,
    ( spl7_524
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_524])])).

fof(f3395,plain,
    ( spl7_535
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_535])])).

fof(f13153,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_524
    | ~ spl7_535 ),
    inference(subsumption_resolution,[],[f13097,f3396])).

fof(f3396,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_535 ),
    inference(avatar_component_clause,[],[f3395])).

fof(f13097,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_138
    | ~ spl7_524 ),
    inference(resolution,[],[f12742,f3320])).

fof(f3320,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_524 ),
    inference(avatar_component_clause,[],[f3319])).

fof(f13183,plain,
    ( spl7_1592
    | ~ spl7_16
    | ~ spl7_42
    | spl7_117
    | ~ spl7_138 ),
    inference(avatar_split_clause,[],[f13157,f789,f681,f326,f207,f13181])).

fof(f13181,plain,
    ( spl7_1592
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1592])])).

fof(f207,plain,
    ( spl7_16
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f13157,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_42
    | ~ spl7_117
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f13102,f682])).

fof(f13102,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_42
    | ~ spl7_138 ),
    inference(resolution,[],[f12742,f208])).

fof(f208,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f13176,plain,
    ( spl7_1590
    | ~ spl7_42
    | ~ spl7_126
    | ~ spl7_138
    | spl7_165 ),
    inference(avatar_split_clause,[],[f13154,f937,f789,f732,f326,f13174])).

fof(f13174,plain,
    ( spl7_1590
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1590])])).

fof(f732,plain,
    ( spl7_126
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f937,plain,
    ( spl7_165
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).

fof(f13154,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_126
    | ~ spl7_138
    | ~ spl7_165 ),
    inference(subsumption_resolution,[],[f13098,f938])).

fof(f938,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_165 ),
    inference(avatar_component_clause,[],[f937])).

fof(f13098,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_42
    | ~ spl7_126
    | ~ spl7_138 ),
    inference(resolution,[],[f12742,f733])).

fof(f733,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_126 ),
    inference(avatar_component_clause,[],[f732])).

fof(f13041,plain,
    ( spl7_1588
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1100
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f12948,f7903,f7880,f773,f316,f13039])).

fof(f13039,plain,
    ( spl7_1588
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1588])])).

fof(f12948,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1100
    | ~ spl7_1105 ),
    inference(subsumption_resolution,[],[f12892,f7904])).

fof(f12892,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_1100 ),
    inference(resolution,[],[f12741,f7881])).

fof(f13034,plain,
    ( spl7_1586
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_524
    | spl7_535 ),
    inference(avatar_split_clause,[],[f12946,f3395,f3319,f773,f316,f13032])).

fof(f13032,plain,
    ( spl7_1586
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1586])])).

fof(f12946,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_524
    | ~ spl7_535 ),
    inference(subsumption_resolution,[],[f12890,f3396])).

fof(f12890,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_134
    | ~ spl7_524 ),
    inference(resolution,[],[f12741,f3320])).

fof(f12976,plain,
    ( spl7_1584
    | ~ spl7_16
    | ~ spl7_40
    | spl7_117
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f12950,f773,f681,f316,f207,f12974])).

fof(f12974,plain,
    ( spl7_1584
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1584])])).

fof(f12950,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_40
    | ~ spl7_117
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f12895,f682])).

fof(f12895,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_40
    | ~ spl7_134 ),
    inference(resolution,[],[f12741,f208])).

fof(f12969,plain,
    ( spl7_1582
    | ~ spl7_40
    | ~ spl7_126
    | ~ spl7_134
    | spl7_165 ),
    inference(avatar_split_clause,[],[f12947,f937,f773,f732,f316,f12967])).

fof(f12967,plain,
    ( spl7_1582
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1582])])).

fof(f12947,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_126
    | ~ spl7_134
    | ~ spl7_165 ),
    inference(subsumption_resolution,[],[f12891,f938])).

fof(f12891,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_40
    | ~ spl7_126
    | ~ spl7_134 ),
    inference(resolution,[],[f12741,f733])).

fof(f12834,plain,
    ( spl7_1580
    | ~ spl7_76
    | ~ spl7_814
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12663,f12247,f5169,f495,f12832])).

fof(f12832,plain,
    ( spl7_1580
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1580])])).

fof(f12247,plain,
    ( spl7_1511
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1511])])).

fof(f12663,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f5949])).

fof(f12248,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1511 ),
    inference(avatar_component_clause,[],[f12247])).

fof(f12827,plain,
    ( spl7_1578
    | ~ spl7_72
    | ~ spl7_808
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12662,f12247,f5132,f479,f12825])).

fof(f12825,plain,
    ( spl7_1578
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1578])])).

fof(f12662,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f5807])).

fof(f12816,plain,
    ( spl7_1576
    | ~ spl7_66
    | ~ spl7_68
    | spl7_451
    | ~ spl7_792
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12366,f12114,f5067,f2709,f463,f454,f12814])).

fof(f12814,plain,
    ( spl7_1576
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1576])])).

fof(f12366,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_66
    | ~ spl7_68
    | ~ spl7_451
    | ~ spl7_792
    | ~ spl7_1499 ),
    inference(forward_demodulation,[],[f12353,f12364])).

fof(f12364,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_66
    | ~ spl7_451
    | ~ spl7_1499 ),
    inference(forward_demodulation,[],[f12363,f455])).

fof(f12363,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_451
    | ~ spl7_1499 ),
    inference(subsumption_resolution,[],[f12349,f2710])).

fof(f12349,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f1211])).

fof(f12353,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f5386])).

fof(f12809,plain,
    ( spl7_1574
    | ~ spl7_64
    | spl7_451
    | ~ spl7_788
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12361,f12114,f5040,f2709,f447,f12807])).

fof(f12807,plain,
    ( spl7_1574
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1574])])).

fof(f12361,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_64
    | ~ spl7_451
    | ~ spl7_788
    | ~ spl7_1499 ),
    inference(subsumption_resolution,[],[f12346,f2710])).

fof(f12346,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f5247])).

fof(f5247,plain,
    ( ! [X24] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(X24)))
        | k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(X24)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),X24),sK4(sK4(k1_zfmisc_1(X24))))
        | v1_xboole_0(X24) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f1209])).

fof(f12802,plain,
    ( spl7_1572
    | ~ spl7_1528
    | ~ spl7_1570 ),
    inference(avatar_split_clause,[],[f12795,f12792,f12411,f12800])).

fof(f12800,plain,
    ( spl7_1572
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1572])])).

fof(f12411,plain,
    ( spl7_1528
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1528])])).

fof(f12792,plain,
    ( spl7_1570
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1570])])).

fof(f12795,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1528
    | ~ spl7_1570 ),
    inference(forward_demodulation,[],[f12793,f12412])).

fof(f12412,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1528 ),
    inference(avatar_component_clause,[],[f12411])).

fof(f12793,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_1570 ),
    inference(avatar_component_clause,[],[f12792])).

fof(f12794,plain,
    ( spl7_1570
    | ~ spl7_68
    | spl7_451
    | ~ spl7_792
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12360,f12114,f5067,f2709,f463,f12792])).

fof(f12360,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_68
    | ~ spl7_451
    | ~ spl7_792
    | ~ spl7_1499 ),
    inference(subsumption_resolution,[],[f12345,f2710])).

fof(f12345,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f5387])).

fof(f5387,plain,
    ( ! [X24] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(X24)))
        | k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(X24)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),X24),sK4(sK4(k1_zfmisc_1(X24))))
        | v1_xboole_0(X24) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f1209])).

fof(f12787,plain,
    ( spl7_1568
    | ~ spl7_80
    | ~ spl7_832
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12667,f12247,f5476,f511,f12785])).

fof(f12785,plain,
    ( spl7_1568
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1568])])).

fof(f12667,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f8527])).

fof(f12780,plain,
    ( spl7_1566
    | ~ spl7_10
    | ~ spl7_52
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12666,f12247,f377,f186,f12778])).

fof(f12778,plain,
    ( spl7_1566
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1566])])).

fof(f12666,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f7231])).

fof(f12773,plain,
    ( spl7_1564
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12661,f12247,f5067,f463,f12771])).

fof(f12771,plain,
    ( spl7_1564
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1564])])).

fof(f12661,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f5386])).

fof(f12766,plain,
    ( spl7_1562
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12660,f12247,f5040,f447,f12764])).

fof(f12764,plain,
    ( spl7_1562
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1562])])).

fof(f12660,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f5246])).

fof(f12712,plain,
    ( spl7_1560
    | ~ spl7_62
    | spl7_117
    | ~ spl7_1548 ),
    inference(avatar_split_clause,[],[f12627,f12609,f681,f438,f12710])).

fof(f12710,plain,
    ( spl7_1560
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1560])])).

fof(f12609,plain,
    ( spl7_1548
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1548])])).

fof(f12627,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ spl7_62
    | ~ spl7_117
    | ~ spl7_1548 ),
    inference(forward_demodulation,[],[f12626,f439])).

fof(f12626,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ spl7_117
    | ~ spl7_1548 ),
    inference(subsumption_resolution,[],[f12614,f682])).

fof(f12614,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ spl7_1548 ),
    inference(resolution,[],[f12610,f601])).

fof(f12610,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0))
    | ~ spl7_1548 ),
    inference(avatar_component_clause,[],[f12609])).

fof(f12705,plain,
    ( ~ spl7_1557
    | spl7_1558
    | spl7_117
    | ~ spl7_1548 ),
    inference(avatar_split_clause,[],[f12625,f12609,f681,f12703,f12697])).

fof(f12697,plain,
    ( spl7_1557
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1557])])).

fof(f12703,plain,
    ( spl7_1558
  <=> v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1558])])).

fof(f12625,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ spl7_117
    | ~ spl7_1548 ),
    inference(subsumption_resolution,[],[f12613,f682])).

fof(f12613,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))))
    | ~ spl7_1548 ),
    inference(resolution,[],[f12610,f531])).

fof(f12658,plain,
    ( spl7_1554
    | ~ spl7_64
    | spl7_451
    | ~ spl7_788
    | ~ spl7_1532 ),
    inference(avatar_split_clause,[],[f12520,f12499,f5040,f2709,f447,f12656])).

fof(f12656,plain,
    ( spl7_1554
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1554])])).

fof(f12499,plain,
    ( spl7_1532
  <=> m1_subset_1(sK4(sK4(o_0_0_xboole_0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1532])])).

fof(f12520,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_451
    | ~ spl7_788
    | ~ spl7_1532 ),
    inference(subsumption_resolution,[],[f12507,f2710])).

fof(f12507,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1532 ),
    inference(resolution,[],[f12500,f5055])).

fof(f12500,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl7_1532 ),
    inference(avatar_component_clause,[],[f12499])).

fof(f12651,plain,
    ( spl7_1552
    | ~ spl7_68
    | spl7_451
    | ~ spl7_792
    | ~ spl7_1512
    | ~ spl7_1528
    | ~ spl7_1532 ),
    inference(avatar_split_clause,[],[f12522,f12499,f12411,f12257,f5067,f2709,f463,f12649])).

fof(f12649,plain,
    ( spl7_1552
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1552])])).

fof(f12257,plain,
    ( spl7_1512
  <=> k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1512])])).

fof(f12522,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_68
    | ~ spl7_451
    | ~ spl7_792
    | ~ spl7_1512
    | ~ spl7_1528
    | ~ spl7_1532 ),
    inference(forward_demodulation,[],[f12521,f12432])).

fof(f12432,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_1512
    | ~ spl7_1528 ),
    inference(superposition,[],[f12412,f12258])).

fof(f12258,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl7_1512 ),
    inference(avatar_component_clause,[],[f12257])).

fof(f12521,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_451
    | ~ spl7_792
    | ~ spl7_1532 ),
    inference(subsumption_resolution,[],[f12508,f2710])).

fof(f12508,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1532 ),
    inference(resolution,[],[f12500,f5082])).

fof(f12643,plain,
    ( spl7_1550
    | ~ spl7_28
    | spl7_451
    | ~ spl7_1512
    | ~ spl7_1528
    | ~ spl7_1532 ),
    inference(avatar_split_clause,[],[f12517,f12499,f12411,f12257,f2709,f258,f12641])).

fof(f12641,plain,
    ( spl7_1550
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1550])])).

fof(f12517,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_28
    | ~ spl7_451
    | ~ spl7_1512
    | ~ spl7_1528
    | ~ spl7_1532 ),
    inference(forward_demodulation,[],[f12516,f12432])).

fof(f12516,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_28
    | ~ spl7_451
    | ~ spl7_1532 ),
    inference(subsumption_resolution,[],[f12515,f259])).

fof(f12515,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_451
    | ~ spl7_1532 ),
    inference(subsumption_resolution,[],[f12504,f2710])).

fof(f12504,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_1532 ),
    inference(resolution,[],[f12500,f3337])).

fof(f12611,plain,
    ( spl7_1548
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_451
    | ~ spl7_1532
    | ~ spl7_1546 ),
    inference(avatar_split_clause,[],[f12604,f12601,f12499,f2709,f200,f165,f158,f151,f12609])).

fof(f12601,plain,
    ( spl7_1546
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1546])])).

fof(f12604,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451
    | ~ spl7_1532
    | ~ spl7_1546 ),
    inference(forward_demodulation,[],[f12602,f12502])).

fof(f12502,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451
    | ~ spl7_1532 ),
    inference(resolution,[],[f12500,f6178])).

fof(f6178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451 ),
    inference(subsumption_resolution,[],[f6176,f2710])).

fof(f6176,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | k1_funct_1(k4_tmap_1(sK0,sK1),X0) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f3945,f201])).

fof(f12602,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0))
    | ~ spl7_1546 ),
    inference(avatar_component_clause,[],[f12601])).

fof(f12603,plain,
    ( spl7_1546
    | ~ spl7_1500
    | ~ spl7_1512 ),
    inference(avatar_split_clause,[],[f12426,f12257,f12123,f12601])).

fof(f12123,plain,
    ( spl7_1500
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1500])])).

fof(f12426,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(o_0_0_xboole_0))),u1_struct_0(sK0))
    | ~ spl7_1500
    | ~ spl7_1512 ),
    inference(superposition,[],[f12124,f12258])).

fof(f12124,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | ~ spl7_1500 ),
    inference(avatar_component_clause,[],[f12123])).

fof(f12596,plain,
    ( spl7_1544
    | ~ spl7_1512
    | ~ spl7_1520 ),
    inference(avatar_split_clause,[],[f12431,f12335,f12257,f12594])).

fof(f12594,plain,
    ( spl7_1544
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1544])])).

fof(f12335,plain,
    ( spl7_1520
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1520])])).

fof(f12431,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1512
    | ~ spl7_1520 ),
    inference(superposition,[],[f12336,f12258])).

fof(f12336,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_1520 ),
    inference(avatar_component_clause,[],[f12335])).

fof(f12589,plain,
    ( spl7_1542
    | ~ spl7_1512
    | ~ spl7_1518 ),
    inference(avatar_split_clause,[],[f12430,f12328,f12257,f12587])).

fof(f12587,plain,
    ( spl7_1542
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1542])])).

fof(f12328,plain,
    ( spl7_1518
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1518])])).

fof(f12430,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1512
    | ~ spl7_1518 ),
    inference(superposition,[],[f12329,f12258])).

fof(f12329,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_1518 ),
    inference(avatar_component_clause,[],[f12328])).

fof(f12580,plain,
    ( ~ spl7_1541
    | ~ spl7_1512
    | spl7_1517 ),
    inference(avatar_split_clause,[],[f12579,f12268,f12257,f12573])).

fof(f12573,plain,
    ( spl7_1541
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1541])])).

fof(f12268,plain,
    ( spl7_1517
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1517])])).

fof(f12579,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1512
    | ~ spl7_1517 ),
    inference(forward_demodulation,[],[f12269,f12258])).

fof(f12269,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_1517 ),
    inference(avatar_component_clause,[],[f12268])).

fof(f12578,plain,
    ( spl7_1540
    | ~ spl7_1512
    | ~ spl7_1516 ),
    inference(avatar_split_clause,[],[f12429,f12271,f12257,f12576])).

fof(f12576,plain,
    ( spl7_1540
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1540])])).

fof(f12271,plain,
    ( spl7_1516
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1516])])).

fof(f12429,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1512
    | ~ spl7_1516 ),
    inference(superposition,[],[f12272,f12258])).

fof(f12272,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_1516 ),
    inference(avatar_component_clause,[],[f12271])).

fof(f12571,plain,
    ( ~ spl7_1539
    | spl7_1124
    | spl7_451
    | spl7_1499
    | ~ spl7_1512 ),
    inference(avatar_split_clause,[],[f12476,f12257,f12114,f2709,f7978,f12569])).

fof(f12569,plain,
    ( spl7_1539
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1539])])).

fof(f7978,plain,
    ( spl7_1124
  <=> v1_xboole_0(sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1124])])).

fof(f12476,plain,
    ( v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(u1_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_451
    | ~ spl7_1499
    | ~ spl7_1512 ),
    inference(forward_demodulation,[],[f12475,f12258])).

fof(f12475,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | ~ spl7_451
    | ~ spl7_1499
    | ~ spl7_1512 ),
    inference(subsumption_resolution,[],[f12474,f12115])).

fof(f12474,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_451
    | ~ spl7_1512 ),
    inference(subsumption_resolution,[],[f12441,f2710])).

fof(f12441,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1512 ),
    inference(superposition,[],[f1212,f12258])).

fof(f1212,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK4(sK4(k1_zfmisc_1(X1))))
      | v1_xboole_0(sK4(sK4(k1_zfmisc_1(X1))))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK4(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f1209,f531])).

fof(f12564,plain,
    ( spl7_1536
    | spl7_349
    | ~ spl7_494
    | ~ spl7_1512 ),
    inference(avatar_split_clause,[],[f12553,f12257,f3127,f1947,f12562])).

fof(f12562,plain,
    ( spl7_1536
  <=> m1_subset_1(sK4(k3_struct_0(sK5)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1536])])).

fof(f3127,plain,
    ( spl7_494
  <=> m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_494])])).

fof(f12553,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),u1_struct_0(sK1))
    | ~ spl7_349
    | ~ spl7_494
    | ~ spl7_1512 ),
    inference(resolution,[],[f12544,f121])).

fof(f12544,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_349
    | ~ spl7_494
    | ~ spl7_1512 ),
    inference(subsumption_resolution,[],[f12539,f1948])).

fof(f12539,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK1))
        | v1_xboole_0(k3_struct_0(sK5))
        | ~ m1_subset_1(X0,k3_struct_0(sK5)) )
    | ~ spl7_494
    | ~ spl7_1512 ),
    inference(resolution,[],[f12437,f3128])).

fof(f3128,plain,
    ( m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0)
    | ~ spl7_494 ),
    inference(avatar_component_clause,[],[f3127])).

fof(f12437,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,o_0_0_xboole_0)
        | m1_subset_1(X2,u1_struct_0(sK1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,X1) )
    | ~ spl7_1512 ),
    inference(superposition,[],[f640,f12258])).

fof(f12538,plain,
    ( spl7_1534
    | ~ spl7_1512
    | ~ spl7_1528 ),
    inference(avatar_split_clause,[],[f12432,f12411,f12257,f12536])).

fof(f12536,plain,
    ( spl7_1534
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1534])])).

fof(f12501,plain,
    ( spl7_1532
    | spl7_1499
    | ~ spl7_1512 ),
    inference(avatar_split_clause,[],[f12469,f12257,f12114,f12499])).

fof(f12469,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),u1_struct_0(sK1))
    | ~ spl7_1499
    | ~ spl7_1512 ),
    inference(subsumption_resolution,[],[f12439,f12115])).

fof(f12439,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),u1_struct_0(sK1))
    | v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1512 ),
    inference(superposition,[],[f1209,f12258])).

fof(f12494,plain,
    ( ~ spl7_489
    | spl7_1503
    | ~ spl7_1512 ),
    inference(avatar_split_clause,[],[f12427,f12257,f12164,f2913])).

fof(f2913,plain,
    ( spl7_489
  <=> o_0_0_xboole_0 != sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_489])])).

fof(f12164,plain,
    ( spl7_1503
  <=> o_0_0_xboole_0 != sK4(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1503])])).

fof(f12427,plain,
    ( o_0_0_xboole_0 != sK4(o_0_0_xboole_0)
    | ~ spl7_1503
    | ~ spl7_1512 ),
    inference(superposition,[],[f12165,f12258])).

fof(f12165,plain,
    ( o_0_0_xboole_0 != sK4(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1503 ),
    inference(avatar_component_clause,[],[f12164])).

fof(f12423,plain,
    ( spl7_1522
    | spl7_1510
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1506 ),
    inference(avatar_split_clause,[],[f12237,f12222,f5476,f511,f12250,f12342])).

fof(f12342,plain,
    ( spl7_1522
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1522])])).

fof(f12250,plain,
    ( spl7_1510
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1510])])).

fof(f12222,plain,
    ( spl7_1506
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1506])])).

fof(f12237,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1506 ),
    inference(resolution,[],[f12223,f5500])).

fof(f12223,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1506 ),
    inference(avatar_component_clause,[],[f12222])).

fof(f12422,plain,
    ( spl7_1520
    | spl7_1510
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1506 ),
    inference(avatar_split_clause,[],[f12236,f12222,f377,f186,f12250,f12335])).

fof(f12236,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1506 ),
    inference(resolution,[],[f12223,f5457])).

fof(f12421,plain,
    ( spl7_1518
    | spl7_1510
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1506 ),
    inference(avatar_split_clause,[],[f12233,f12222,f5067,f463,f12250,f12328])).

fof(f12233,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1506 ),
    inference(resolution,[],[f12223,f5082])).

fof(f12420,plain,
    ( spl7_1530
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12351,f12114,f12418])).

fof(f12418,plain,
    ( spl7_1530
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1530])])).

fof(f12351,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(u1_struct_0(sK1)))),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1499 ),
    inference(resolution,[],[f12115,f858])).

fof(f12413,plain,
    ( spl7_1528
    | ~ spl7_66
    | spl7_451
    | spl7_1499 ),
    inference(avatar_split_clause,[],[f12364,f12114,f2709,f454,f12411])).

fof(f12380,plain,
    ( spl7_1526
    | spl7_1446
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f852,f665,f11737,f12378])).

fof(f12378,plain,
    ( spl7_1526
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))),k3_struct_0(sK5)) = k3_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1526])])).

fof(f11737,plain,
    ( spl7_1446
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1446])])).

fof(f852,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | ~ spl7_112 ),
    inference(resolution,[],[f601,f666])).

fof(f12373,plain,
    ( spl7_1524
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12306,f12247,f12371])).

fof(f12371,plain,
    ( spl7_1524
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = sK4(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1524])])).

fof(f12306,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = sK4(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f858])).

fof(f12344,plain,
    ( spl7_1522
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1502
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12323,f12247,f12167,f5476,f511,f12342])).

fof(f12167,plain,
    ( spl7_1502
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1502])])).

fof(f12323,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1502
    | ~ spl7_1511 ),
    inference(forward_demodulation,[],[f12314,f12168])).

fof(f12168,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1502 ),
    inference(avatar_component_clause,[],[f12167])).

fof(f12314,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f8527])).

fof(f12337,plain,
    ( spl7_1520
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1502
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12322,f12247,f12167,f377,f186,f12335])).

fof(f12322,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1502
    | ~ spl7_1511 ),
    inference(forward_demodulation,[],[f12313,f12168])).

fof(f12313,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f7231])).

fof(f12330,plain,
    ( spl7_1518
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1502
    | spl7_1511 ),
    inference(avatar_split_clause,[],[f12317,f12247,f12167,f5067,f463,f12328])).

fof(f12317,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1502
    | ~ spl7_1511 ),
    inference(forward_demodulation,[],[f12308,f12168])).

fof(f12308,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(u1_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))),sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1511 ),
    inference(resolution,[],[f12248,f5386])).

fof(f12305,plain,
    ( spl7_1512
    | ~ spl7_20
    | ~ spl7_1510 ),
    inference(avatar_split_clause,[],[f12290,f12250,f223,f12257])).

fof(f12290,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1510 ),
    inference(forward_demodulation,[],[f12274,f224])).

fof(f12274,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_xboole_0
    | ~ spl7_1510 ),
    inference(resolution,[],[f12251,f117])).

fof(f12251,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1510 ),
    inference(avatar_component_clause,[],[f12250])).

fof(f12273,plain,
    ( spl7_1516
    | spl7_1510
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1506 ),
    inference(avatar_split_clause,[],[f12232,f12222,f5040,f447,f12250,f12271])).

fof(f12232,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1506 ),
    inference(resolution,[],[f12223,f5055])).

fof(f12266,plain,
    ( spl7_1514
    | spl7_1508
    | ~ spl7_8
    | ~ spl7_1502 ),
    inference(avatar_split_clause,[],[f12198,f12167,f179,f12244,f12264])).

fof(f12264,plain,
    ( spl7_1514
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1514])])).

fof(f12244,plain,
    ( spl7_1508
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1508])])).

fof(f12198,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_8
    | ~ spl7_1502 ),
    inference(superposition,[],[f3740,f12168])).

fof(f12259,plain,
    ( spl7_1512
    | spl7_1508
    | ~ spl7_8
    | ~ spl7_1502 ),
    inference(avatar_split_clause,[],[f12195,f12167,f179,f12244,f12257])).

fof(f12195,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_1502 ),
    inference(superposition,[],[f889,f12168])).

fof(f12252,plain,
    ( spl7_1508
    | spl7_1510
    | ~ spl7_1506 ),
    inference(avatar_split_clause,[],[f12231,f12222,f12250,f12244])).

fof(f12231,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(u1_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1506 ),
    inference(resolution,[],[f12223,f601])).

fof(f12224,plain,
    ( spl7_1506
    | ~ spl7_1502 ),
    inference(avatar_split_clause,[],[f12193,f12167,f12222])).

fof(f12193,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1502 ),
    inference(superposition,[],[f121,f12168])).

fof(f12217,plain,
    ( ~ spl7_1505
    | spl7_189
    | ~ spl7_1502 ),
    inference(avatar_split_clause,[],[f12209,f12167,f1061,f12215])).

fof(f12215,plain,
    ( spl7_1505
  <=> ~ v1_relat_1(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1505])])).

fof(f12209,plain,
    ( ~ v1_relat_1(u1_struct_0(sK1))
    | ~ spl7_189
    | ~ spl7_1502 ),
    inference(subsumption_resolution,[],[f12171,f1062])).

fof(f12171,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(u1_struct_0(sK1))
    | ~ spl7_1502 ),
    inference(superposition,[],[f400,f12168])).

fof(f12169,plain,
    ( spl7_1502
    | ~ spl7_20
    | ~ spl7_1498 ),
    inference(avatar_split_clause,[],[f12142,f12117,f223,f12167])).

fof(f12117,plain,
    ( spl7_1498
  <=> v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1498])])).

fof(f12142,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_20
    | ~ spl7_1498 ),
    inference(forward_demodulation,[],[f12126,f224])).

fof(f12126,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_1498 ),
    inference(resolution,[],[f12118,f117])).

fof(f12118,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1498 ),
    inference(avatar_component_clause,[],[f12117])).

fof(f12125,plain,
    ( spl7_1498
    | spl7_1500
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_451 ),
    inference(avatar_split_clause,[],[f4715,f2709,f200,f165,f158,f151,f12123,f12117])).

fof(f4715,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(sK4(k1_zfmisc_1(u1_struct_0(sK1))))),u1_struct_0(sK0))
    | v1_xboole_0(sK4(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451 ),
    inference(resolution,[],[f4709,f1209])).

fof(f4709,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451 ),
    inference(subsumption_resolution,[],[f4707,f2710])).

fof(f4707,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f3562,f201])).

fof(f3562,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v1_xboole_0(u1_struct_0(X0))
        | m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3561,f152])).

fof(f3561,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3560,f166])).

fof(f3560,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(X0),u1_struct_0(sK0),k4_tmap_1(sK0,X0),X1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f1732,f159])).

fof(f1732,plain,(
    ! [X4,X2,X3] :
      ( ~ v2_pre_topc(X4)
      | m1_subset_1(k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2),u1_struct_0(X4))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X2,u1_struct_0(X3))
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1731,f127])).

fof(f1731,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | m1_subset_1(k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2),u1_struct_0(X4))
      | ~ v1_funct_1(k4_tmap_1(X4,X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1728,f129])).

fof(f1728,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(X3))
      | ~ m1_subset_1(k4_tmap_1(X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | m1_subset_1(k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),k4_tmap_1(X4,X3),X2),u1_struct_0(X4))
      | ~ v1_funct_1(k4_tmap_1(X4,X3))
      | v1_xboole_0(u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f135,f128])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k3_funct_2)).

fof(f12112,plain,
    ( spl7_1496
    | ~ spl7_80
    | spl7_615
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8615,f5476,f3839,f511,f12110])).

fof(f12110,plain,
    ( spl7_1496
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1496])])).

fof(f3839,plain,
    ( spl7_615
  <=> ~ v1_xboole_0(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_615])])).

fof(f8615,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1)))))
    | ~ spl7_80
    | ~ spl7_615
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f3840])).

fof(f3840,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_615 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f12105,plain,
    ( spl7_1494
    | ~ spl7_10
    | ~ spl7_52
    | spl7_615 ),
    inference(avatar_split_clause,[],[f7297,f3839,f377,f186,f12103])).

fof(f12103,plain,
    ( spl7_1494
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1494])])).

fof(f7297,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1)))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_615 ),
    inference(resolution,[],[f7231,f3840])).

fof(f12098,plain,
    ( spl7_1492
    | ~ spl7_68
    | spl7_615
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5435,f5067,f3839,f463,f12096])).

fof(f12096,plain,
    ( spl7_1492
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1492])])).

fof(f5435,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1)))))
    | ~ spl7_68
    | ~ spl7_615
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f3840])).

fof(f12091,plain,
    ( spl7_1490
    | ~ spl7_64
    | spl7_615
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5318,f5040,f3839,f447,f12089])).

fof(f12089,plain,
    ( spl7_1490
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1490])])).

fof(f5318,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK3(sK1))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1)))))
    | ~ spl7_64
    | ~ spl7_615
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f3840])).

fof(f12080,plain,
    ( spl7_1488
    | ~ spl7_90
    | ~ spl7_950
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11334,f7774,f7634,f6261,f556,f12078])).

fof(f12078,plain,
    ( spl7_1488
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1488])])).

fof(f7634,plain,
    ( spl7_1079
  <=> ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1079])])).

fof(f7774,plain,
    ( spl7_1092
  <=> m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1092])])).

fof(f11334,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11325,f7635])).

fof(f7635,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1079 ),
    inference(avatar_component_clause,[],[f7634])).

fof(f11325,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f6287])).

fof(f7775,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1092 ),
    inference(avatar_component_clause,[],[f7774])).

fof(f12025,plain,
    ( ~ spl7_1483
    | spl7_1486
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f11995,f1684,f165,f158,f151,f12023,f12001])).

fof(f12001,plain,
    ( spl7_1483
  <=> ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1483])])).

fof(f12023,plain,
    ( spl7_1486
  <=> ! [X13] : m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1486])])).

fof(f11995,plain,
    ( ! [X13] :
        ( m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(subsumption_resolution,[],[f11984,f1685])).

fof(f11984,plain,
    ( ! [X13] :
        ( m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(superposition,[],[f142,f11979])).

fof(f11979,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X0) = k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(resolution,[],[f5154,f1685])).

fof(f5154,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_partfun1(X3,X4,k4_tmap_1(sK0,sK3(sK0)),X5) = k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X5) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f5153,f166])).

fof(f5153,plain,
    ( ! [X4,X5,X3] :
        ( k2_partfun1(X3,X4,k4_tmap_1(sK0,sK3(sK0)),X5) = k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X5)
        | ~ m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f3825,f116])).

fof(f3825,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | k2_partfun1(X0,X1,k4_tmap_1(sK0,X2),X3) = k7_relat_1(k4_tmap_1(sK0,X2),X3)
        | ~ m1_subset_1(k4_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3824,f152])).

fof(f3824,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_partfun1(X0,X1,k4_tmap_1(sK0,X2),X3) = k7_relat_1(k4_tmap_1(sK0,X2),X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_subset_1(k4_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f3823,f166])).

fof(f3823,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_partfun1(X0,X1,k4_tmap_1(sK0,X2),X3) = k7_relat_1(k4_tmap_1(sK0,X2),X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k4_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f1264,f159])).

fof(f1264,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_partfun1(X2,X3,k4_tmap_1(X0,X1),X4) = k7_relat_1(k4_tmap_1(X0,X1),X4)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f140,f127])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k2_partfun1)).

fof(f12011,plain,
    ( ~ spl7_389
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_1483 ),
    inference(avatar_split_clause,[],[f12010,f12001,f165,f158,f151,f2214])).

fof(f12010,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_1483 ),
    inference(subsumption_resolution,[],[f12009,f152])).

fof(f12009,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_1483 ),
    inference(subsumption_resolution,[],[f12008,f159])).

fof(f12008,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_1483 ),
    inference(subsumption_resolution,[],[f12007,f166])).

fof(f12007,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1483 ),
    inference(resolution,[],[f12002,f127])).

fof(f12002,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_1483 ),
    inference(avatar_component_clause,[],[f12001])).

fof(f12006,plain,
    ( ~ spl7_1483
    | spl7_1484
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f11996,f1684,f165,f158,f151,f12004,f12001])).

fof(f12004,plain,
    ( spl7_1484
  <=> ! [X14] : v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1484])])).

fof(f11996,plain,
    ( ! [X14] :
        ( v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X14))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(subsumption_resolution,[],[f11985,f1685])).

fof(f11985,plain,
    ( ! [X14] :
        ( v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK3(sK0)),X14))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_298 ),
    inference(superposition,[],[f141,f11979])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f11976,plain,
    ( spl7_1480
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f11747,f7511,f5067,f463,f11974])).

fof(f11974,plain,
    ( spl7_1480
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1480])])).

fof(f7511,plain,
    ( spl7_1067
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1067])])).

fof(f11747,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1067 ),
    inference(resolution,[],[f7512,f5386])).

fof(f7512,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_1067 ),
    inference(avatar_component_clause,[],[f7511])).

fof(f11969,plain,
    ( spl7_1478
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f11746,f7511,f5040,f447,f11967])).

fof(f11967,plain,
    ( spl7_1478
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1478])])).

fof(f11746,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1067 ),
    inference(resolution,[],[f7512,f5246])).

fof(f11962,plain,
    ( spl7_1476
    | ~ spl7_80
    | ~ spl7_306
    | spl7_435
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f10257,f5476,f2558,f1711,f511,f11960])).

fof(f11960,plain,
    ( spl7_1476
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1476])])).

fof(f1711,plain,
    ( spl7_306
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_306])])).

fof(f2558,plain,
    ( spl7_435
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_435])])).

fof(f10257,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_80
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_832 ),
    inference(resolution,[],[f8547,f121])).

fof(f8547,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k3_struct_0(sK6),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) )
    | ~ spl7_80
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f8478,f2559])).

fof(f2559,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl7_435 ),
    inference(avatar_component_clause,[],[f2558])).

fof(f8478,plain,
    ( ! [X4] :
        ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | k1_funct_1(k3_struct_0(sK6),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_80
    | ~ spl7_306
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f1712])).

fof(f1712,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_306 ),
    inference(avatar_component_clause,[],[f1711])).

fof(f11955,plain,
    ( spl7_1474
    | ~ spl7_68
    | ~ spl7_306
    | spl7_435
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f10236,f5067,f2558,f1711,f463,f11953])).

fof(f11953,plain,
    ( spl7_1474
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1474])])).

fof(f10236,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_68
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_792 ),
    inference(resolution,[],[f5398,f121])).

fof(f5398,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k3_struct_0(sK1),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) )
    | ~ spl7_68
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_792 ),
    inference(subsumption_resolution,[],[f5340,f2559])).

fof(f5340,plain,
    ( ! [X4] :
        ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | k1_funct_1(k3_struct_0(sK1),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_68
    | ~ spl7_306
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f1712])).

fof(f11948,plain,
    ( spl7_1472
    | ~ spl7_64
    | ~ spl7_306
    | spl7_435
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f10232,f5040,f2558,f1711,f447,f11946])).

fof(f11946,plain,
    ( spl7_1472
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1472])])).

fof(f10232,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_64
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_788 ),
    inference(resolution,[],[f5258,f121])).

fof(f5258,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k3_struct_0(sK0),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) )
    | ~ spl7_64
    | ~ spl7_306
    | ~ spl7_435
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5200,f2559])).

fof(f5200,plain,
    ( ! [X4] :
        ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | k1_funct_1(k3_struct_0(sK0),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_64
    | ~ spl7_306
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f1712])).

fof(f11941,plain,
    ( spl7_1470
    | ~ spl7_80
    | spl7_383
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8611,f5476,f2175,f511,f11939])).

fof(f11939,plain,
    ( spl7_1470
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1470])])).

fof(f2175,plain,
    ( spl7_383
  <=> ~ v1_xboole_0(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_383])])).

fof(f8611,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_80
    | ~ spl7_383
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f2176])).

fof(f2176,plain,
    ( ~ v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_383 ),
    inference(avatar_component_clause,[],[f2175])).

fof(f11934,plain,
    ( spl7_1468
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f7602,f7527,f5067,f463,f11932])).

fof(f11932,plain,
    ( spl7_1468
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1468])])).

fof(f7602,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1071 ),
    inference(resolution,[],[f7528,f5386])).

fof(f11927,plain,
    ( spl7_1466
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f7601,f7527,f5040,f447,f11925])).

fof(f11925,plain,
    ( spl7_1466
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1466])])).

fof(f7601,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1071 ),
    inference(resolution,[],[f7528,f5246])).

fof(f11860,plain,
    ( spl7_1464
    | ~ spl7_76
    | ~ spl7_200
    | spl7_415
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5973,f5169,f2377,f1132,f495,f11858])).

fof(f11858,plain,
    ( spl7_1464
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1464])])).

fof(f1132,plain,
    ( spl7_200
  <=> m1_subset_1(sK4(k3_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f5973,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_76
    | ~ spl7_200
    | ~ spl7_415
    | ~ spl7_814 ),
    inference(subsumption_resolution,[],[f5954,f2378])).

fof(f5954,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_76
    | ~ spl7_200
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f1133])).

fof(f1133,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_200 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f11853,plain,
    ( spl7_1462
    | ~ spl7_62
    | ~ spl7_76
    | spl7_397
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f11830,f5169,f2316,f495,f438,f11851])).

fof(f11851,plain,
    ( spl7_1462
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1462])])).

fof(f2316,plain,
    ( spl7_397
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_397])])).

fof(f11830,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_62
    | ~ spl7_76
    | ~ spl7_397
    | ~ spl7_814 ),
    inference(forward_demodulation,[],[f11812,f439])).

fof(f11812,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),k6_partfun1(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl7_76
    | ~ spl7_397
    | ~ spl7_814 ),
    inference(resolution,[],[f5928,f2317])).

fof(f2317,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_397 ),
    inference(avatar_component_clause,[],[f2316])).

fof(f5928,plain,
    ( ! [X12] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X12,X12)))
        | k1_funct_1(k3_struct_0(sK3(sK1)),k6_partfun1(X12)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(X12,X12))),k6_partfun1(X12)) )
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f108])).

fof(f11846,plain,
    ( spl7_1460
    | spl7_472
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f1689,f1684,f2808,f11844])).

fof(f2808,plain,
    ( spl7_472
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_472])])).

fof(f1689,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK3(sK0)) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_298 ),
    inference(resolution,[],[f1685,f601])).

fof(f11839,plain,
    ( spl7_1458
    | ~ spl7_76
    | ~ spl7_424
    | ~ spl7_814
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f11831,f7511,f5169,f2446,f495,f11837])).

fof(f11837,plain,
    ( spl7_1458
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1458])])).

fof(f11831,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_76
    | ~ spl7_424
    | ~ spl7_814
    | ~ spl7_1067 ),
    inference(forward_demodulation,[],[f11813,f2447])).

fof(f11813,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),k6_partfun1(o_0_0_xboole_0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1067 ),
    inference(resolution,[],[f5928,f7512])).

fof(f11794,plain,
    ( spl7_1456
    | ~ spl7_68
    | spl7_383
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5431,f5067,f2175,f463,f11792])).

fof(f11792,plain,
    ( spl7_1456
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1456])])).

fof(f5431,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_68
    | ~ spl7_383
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f2176])).

fof(f11787,plain,
    ( spl7_1454
    | ~ spl7_64
    | spl7_383
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5314,f5040,f2175,f447,f11785])).

fof(f11785,plain,
    ( spl7_1454
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1454])])).

fof(f5314,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_64
    | ~ spl7_383
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f2176])).

fof(f11778,plain,
    ( spl7_1452
    | ~ spl7_72
    | ~ spl7_200
    | spl7_415
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5831,f5132,f2377,f1132,f479,f11776])).

fof(f11776,plain,
    ( spl7_1452
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1452])])).

fof(f5831,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_72
    | ~ spl7_200
    | ~ spl7_415
    | ~ spl7_808 ),
    inference(subsumption_resolution,[],[f5812,f2378])).

fof(f5812,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_72
    | ~ spl7_200
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f1133])).

fof(f11771,plain,
    ( spl7_1450
    | ~ spl7_62
    | ~ spl7_72
    | spl7_397
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f11486,f5132,f2316,f479,f438,f11769])).

fof(f11486,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_62
    | ~ spl7_72
    | ~ spl7_397
    | ~ spl7_808 ),
    inference(forward_demodulation,[],[f11472,f439])).

fof(f11472,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k6_partfun1(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl7_72
    | ~ spl7_397
    | ~ spl7_808 ),
    inference(resolution,[],[f2317,f5787])).

fof(f5787,plain,
    ( ! [X12] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X12,X12)))
        | k1_funct_1(k3_struct_0(sK3(sK0)),k6_partfun1(X12)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(X12,X12))),k6_partfun1(X12)) )
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f108])).

fof(f11764,plain,
    ( spl7_1448
    | ~ spl7_76
    | ~ spl7_814
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11331,f7774,f7634,f5169,f495,f11762])).

fof(f11762,plain,
    ( spl7_1448
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1448])])).

fof(f11331,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11322,f7635])).

fof(f11322,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5193])).

fof(f11739,plain,
    ( ~ spl7_1445
    | spl7_1446
    | spl7_348
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f688,f665,f1950,f11737,f11731])).

fof(f11731,plain,
    ( spl7_1445
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1445])])).

fof(f1950,plain,
    ( spl7_348
  <=> v1_xboole_0(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_348])])).

fof(f688,plain,
    ( v1_xboole_0(k3_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))),k3_struct_0(sK5))
    | ~ spl7_112 ),
    inference(resolution,[],[f666,f531])).

fof(f11726,plain,
    ( spl7_1442
    | ~ spl7_72
    | ~ spl7_808
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11330,f7774,f7634,f5132,f479,f11724])).

fof(f11724,plain,
    ( spl7_1442
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1442])])).

fof(f11330,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11321,f7635])).

fof(f11321,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5159])).

fof(f11719,plain,
    ( spl7_1440
    | ~ spl7_80
    | ~ spl7_832
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11333,f7774,f7634,f5476,f511,f11717])).

fof(f11717,plain,
    ( spl7_1440
  <=> k1_funct_1(k3_struct_0(sK6),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1440])])).

fof(f11333,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11324,f7635])).

fof(f11324,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK6),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5500])).

fof(f11712,plain,
    ( spl7_1438
    | ~ spl7_10
    | ~ spl7_52
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11332,f7774,f7634,f377,f186,f11710])).

fof(f11710,plain,
    ( spl7_1438
  <=> k1_funct_1(k3_struct_0(sK5),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1438])])).

fof(f11332,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11323,f7635])).

fof(f11323,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK5),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5457])).

fof(f11705,plain,
    ( spl7_1436
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11329,f7774,f7634,f5067,f463,f11703])).

fof(f11703,plain,
    ( spl7_1436
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1436])])).

fof(f11329,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11320,f7635])).

fof(f11320,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5082])).

fof(f11698,plain,
    ( spl7_1434
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1079
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f11328,f7774,f7634,f5040,f447,f11696])).

fof(f11696,plain,
    ( spl7_1434
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1434])])).

fof(f11328,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1079
    | ~ spl7_1092 ),
    inference(subsumption_resolution,[],[f11319,f7635])).

fof(f11319,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f5055])).

fof(f11679,plain,
    ( spl7_1114
    | ~ spl7_1117
    | ~ spl7_788
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f11357,f7696,f5040,f7955,f7949])).

fof(f7949,plain,
    ( spl7_1114
  <=> ! [X7] : k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK0),X7) = k7_relat_1(k3_struct_0(sK0),X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1114])])).

fof(f7955,plain,
    ( spl7_1117
  <=> ~ m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1117])])).

fof(f7696,plain,
    ( spl7_1088
  <=> k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1088])])).

fof(f11357,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0)
        | k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK0),X17) = k7_relat_1(k3_struct_0(sK0),X17) )
    | ~ spl7_788
    | ~ spl7_1088 ),
    inference(superposition,[],[f5053,f7697])).

fof(f7697,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_1088 ),
    inference(avatar_component_clause,[],[f7696])).

fof(f5053,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_partfun1(X8,X9,k3_struct_0(sK0),X10) = k7_relat_1(k3_struct_0(sK0),X10) )
    | ~ spl7_788 ),
    inference(resolution,[],[f5041,f140])).

fof(f11678,plain,
    ( spl7_1432
    | spl7_181
    | ~ spl7_1088
    | ~ spl7_1116 ),
    inference(avatar_split_clause,[],[f11669,f7952,f7696,f1019,f11676])).

fof(f11676,plain,
    ( spl7_1432
  <=> m1_subset_1(sK4(k3_struct_0(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1432])])).

fof(f7952,plain,
    ( spl7_1116
  <=> m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1116])])).

fof(f11669,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_181
    | ~ spl7_1088
    | ~ spl7_1116 ),
    inference(resolution,[],[f11660,f121])).

fof(f11660,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK0))
        | m1_subset_1(X0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) )
    | ~ spl7_181
    | ~ spl7_1088
    | ~ spl7_1116 ),
    inference(subsumption_resolution,[],[f11650,f1020])).

fof(f11650,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | v1_xboole_0(k3_struct_0(sK0))
        | ~ m1_subset_1(X0,k3_struct_0(sK0)) )
    | ~ spl7_1088
    | ~ spl7_1116 ),
    inference(resolution,[],[f11368,f7953])).

fof(f7953,plain,
    ( m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl7_1116 ),
    inference(avatar_component_clause,[],[f7952])).

fof(f11368,plain,
    ( ! [X28,X29] :
        ( ~ m1_subset_1(X28,o_0_0_xboole_0)
        | m1_subset_1(X29,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | v1_xboole_0(X28)
        | ~ m1_subset_1(X29,X28) )
    | ~ spl7_1088 ),
    inference(superposition,[],[f640,f7697])).

fof(f11613,plain,
    ( spl7_1430
    | ~ spl7_1420 ),
    inference(avatar_split_clause,[],[f11603,f11298,f11611])).

fof(f11603,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))),u1_struct_0(sK0))
    | ~ spl7_1420 ),
    inference(resolution,[],[f11299,f121])).

fof(f11569,plain,
    ( spl7_1428
    | ~ spl7_1088
    | ~ spl7_1144 ),
    inference(avatar_split_clause,[],[f11342,f8126,f7696,f11567])).

fof(f11567,plain,
    ( spl7_1428
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1428])])).

fof(f8126,plain,
    ( spl7_1144
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1144])])).

fof(f11342,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK5))
    | ~ spl7_1088
    | ~ spl7_1144 ),
    inference(superposition,[],[f8127,f7697])).

fof(f8127,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_1144 ),
    inference(avatar_component_clause,[],[f8126])).

fof(f11562,plain,
    ( ~ spl7_1427
    | ~ spl7_1088
    | spl7_1143 ),
    inference(avatar_split_clause,[],[f11561,f8116,f7696,f11555])).

fof(f11555,plain,
    ( spl7_1427
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) != k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1427])])).

fof(f8116,plain,
    ( spl7_1143
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) != k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1143])])).

fof(f11561,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) != k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK5))
    | ~ spl7_1088
    | ~ spl7_1143 ),
    inference(forward_demodulation,[],[f8117,f7697])).

fof(f8117,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) != k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_1143 ),
    inference(avatar_component_clause,[],[f8116])).

fof(f11560,plain,
    ( spl7_1426
    | ~ spl7_1088
    | ~ spl7_1142 ),
    inference(avatar_split_clause,[],[f11341,f8119,f7696,f11558])).

fof(f11558,plain,
    ( spl7_1426
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1426])])).

fof(f8119,plain,
    ( spl7_1142
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1142])])).

fof(f11341,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK5))
    | ~ spl7_1088
    | ~ spl7_1142 ),
    inference(superposition,[],[f8120,f7697])).

fof(f8120,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_1142 ),
    inference(avatar_component_clause,[],[f8119])).

fof(f11528,plain,
    ( ~ spl7_1425
    | ~ spl7_424
    | spl7_1087
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f11527,f7696,f7663,f2446,f11513])).

fof(f11513,plain,
    ( spl7_1425
  <=> k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) != k3_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1425])])).

fof(f7663,plain,
    ( spl7_1087
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) != k3_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1087])])).

fof(f11527,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) != k3_struct_0(sK5)
    | ~ spl7_424
    | ~ spl7_1087
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f11526,f2447])).

fof(f11526,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),k3_struct_0(sK5)) != k3_struct_0(sK5)
    | ~ spl7_1087
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7664,f7697])).

fof(f7664,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) != k3_struct_0(sK5)
    | ~ spl7_1087 ),
    inference(avatar_component_clause,[],[f7663])).

fof(f11518,plain,
    ( spl7_1424
    | ~ spl7_424
    | ~ spl7_1086
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f11399,f7696,f7666,f2446,f11516])).

fof(f11516,plain,
    ( spl7_1424
  <=> k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) = k3_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1424])])).

fof(f7666,plain,
    ( spl7_1086
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) = k3_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1086])])).

fof(f11399,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | ~ spl7_424
    | ~ spl7_1086
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f11340,f2447])).

fof(f11340,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | ~ spl7_1086
    | ~ spl7_1088 ),
    inference(superposition,[],[f7667,f7697])).

fof(f7667,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | ~ spl7_1086 ),
    inference(avatar_component_clause,[],[f7666])).

fof(f11468,plain,
    ( spl7_1422
    | spl7_349
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f11457,f8947,f3127,f1947,f11466])).

fof(f11466,plain,
    ( spl7_1422
  <=> m1_subset_1(sK4(k3_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1422])])).

fof(f8947,plain,
    ( spl7_1248
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1248])])).

fof(f11457,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_349
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(resolution,[],[f11315,f121])).

fof(f11315,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK5))
        | m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl7_349
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f11302,f1948])).

fof(f11302,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(k3_struct_0(sK5))
        | ~ m1_subset_1(X1,k3_struct_0(sK5)) )
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(resolution,[],[f3128,f9904])).

fof(f9904,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,o_0_0_xboole_0)
        | m1_subset_1(X13,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X13,X12) )
    | ~ spl7_1248 ),
    inference(superposition,[],[f640,f8948])).

fof(f8948,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl7_1248 ),
    inference(avatar_component_clause,[],[f8947])).

fof(f11300,plain,
    ( spl7_1420
    | spl7_684
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f4710,f165,f158,f151,f4310,f11298])).

fof(f4710,plain,
    ( ! [X1] :
        ( v1_xboole_0(u1_struct_0(sK3(sK0)))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f4708,f166])).

fof(f4708,plain,
    ( ! [X1] :
        ( v1_xboole_0(u1_struct_0(sK3(sK0)))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k4_tmap_1(sK0,sK3(sK0)),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f3562,f116])).

fof(f11296,plain,
    ( spl7_494
    | ~ spl7_424
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7737,f7696,f2446,f3127])).

fof(f7737,plain,
    ( m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0)
    | ~ spl7_424
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7703,f2447])).

fof(f7703,plain,
    ( m1_subset_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_1088 ),
    inference(superposition,[],[f108,f7697])).

fof(f11275,plain,
    ( spl7_1418
    | ~ spl7_72
    | ~ spl7_424
    | ~ spl7_808
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f11267,f7511,f5132,f2446,f479,f11273])).

fof(f11267,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_72
    | ~ spl7_424
    | ~ spl7_808
    | ~ spl7_1067 ),
    inference(forward_demodulation,[],[f11249,f2447])).

fof(f11249,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),k6_partfun1(o_0_0_xboole_0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1067 ),
    inference(resolution,[],[f5787,f7512])).

fof(f11248,plain,
    ( spl7_1416
    | ~ spl7_68
    | spl7_349
    | ~ spl7_792
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f11238,f7527,f5067,f1947,f463,f11246])).

fof(f11246,plain,
    ( spl7_1416
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1416])])).

fof(f11238,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | ~ spl7_68
    | ~ spl7_349
    | ~ spl7_792
    | ~ spl7_1071 ),
    inference(subsumption_resolution,[],[f11215,f1948])).

fof(f11215,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | v1_xboole_0(k3_struct_0(sK5))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1071 ),
    inference(resolution,[],[f5387,f7528])).

fof(f11214,plain,
    ( spl7_1414
    | ~ spl7_64
    | spl7_349
    | ~ spl7_788
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f11204,f7527,f5040,f1947,f447,f11212])).

fof(f11212,plain,
    ( spl7_1414
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1414])])).

fof(f11204,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | ~ spl7_64
    | ~ spl7_349
    | ~ spl7_788
    | ~ spl7_1071 ),
    inference(subsumption_resolution,[],[f11181,f1948])).

fof(f11181,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))))
    | v1_xboole_0(k3_struct_0(sK5))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1071 ),
    inference(resolution,[],[f5247,f7528])).

fof(f11180,plain,
    ( spl7_1410
    | ~ spl7_1413
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f10720,f8947,f200,f165,f158,f151,f11178,f11172])).

fof(f11172,plain,
    ( spl7_1410
  <=> ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0) = k7_relat_1(k4_tmap_1(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1410])])).

fof(f11178,plain,
    ( spl7_1413
  <=> ~ m1_subset_1(k4_tmap_1(sK0,sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1413])])).

fof(f10720,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),o_0_0_xboole_0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0) = k7_relat_1(k4_tmap_1(sK0,sK1),X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_1248 ),
    inference(superposition,[],[f5152,f8948])).

fof(f5152,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,k4_tmap_1(sK0,sK1),X2) = k7_relat_1(k4_tmap_1(sK0,sK1),X2) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f3825,f201])).

fof(f11170,plain,
    ( spl7_1408
    | spl7_402
    | ~ spl7_802 ),
    inference(avatar_split_clause,[],[f5115,f5109,f2339,f11168])).

fof(f11168,plain,
    ( spl7_1408
  <=> ! [X5] : k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),k7_relat_1(k3_struct_0(sK1),X5)) = k7_relat_1(k3_struct_0(sK1),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1408])])).

fof(f2339,plain,
    ( spl7_402
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_402])])).

fof(f5109,plain,
    ( spl7_802
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_802])])).

fof(f5115,plain,
    ( ! [X5] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),k7_relat_1(k3_struct_0(sK1),X5)) = k7_relat_1(k3_struct_0(sK1),X5) )
    | ~ spl7_802 ),
    inference(resolution,[],[f5110,f601])).

fof(f5110,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl7_802 ),
    inference(avatar_component_clause,[],[f5109])).

fof(f11166,plain,
    ( spl7_1406
    | spl7_396
    | ~ spl7_796 ),
    inference(avatar_split_clause,[],[f5096,f5090,f2319,f11164])).

fof(f11164,plain,
    ( spl7_1406
  <=> ! [X5] : k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k7_relat_1(k3_struct_0(sK0),X5)) = k7_relat_1(k3_struct_0(sK0),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1406])])).

fof(f2319,plain,
    ( spl7_396
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_396])])).

fof(f5090,plain,
    ( spl7_796
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_796])])).

fof(f5096,plain,
    ( ! [X5] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k7_relat_1(k3_struct_0(sK0),X5)) = k7_relat_1(k3_struct_0(sK0),X5) )
    | ~ spl7_796 ),
    inference(resolution,[],[f5091,f601])).

fof(f5091,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_796 ),
    inference(avatar_component_clause,[],[f5090])).

fof(f11077,plain,
    ( ~ spl7_1405
    | spl7_472
    | spl7_382
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f1690,f1684,f2178,f2808,f11075])).

fof(f2178,plain,
    ( spl7_382
  <=> v1_xboole_0(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_382])])).

fof(f1690,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_298 ),
    inference(resolution,[],[f1685,f531])).

fof(f11011,plain,
    ( spl7_1402
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_306
    | spl7_435 ),
    inference(avatar_split_clause,[],[f8847,f2558,f1711,f377,f186,f11009])).

fof(f11009,plain,
    ( spl7_1402
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1402])])).

fof(f8847,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_306
    | ~ spl7_435 ),
    inference(resolution,[],[f7247,f121])).

fof(f7247,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k3_struct_0(sK5),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4) )
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_306
    | ~ spl7_435 ),
    inference(subsumption_resolution,[],[f7185,f2559])).

fof(f7185,plain,
    ( ! [X4] :
        ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | k1_funct_1(k3_struct_0(sK5),X4) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X4)
        | ~ m1_subset_1(X4,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_306 ),
    inference(resolution,[],[f5457,f1712])).

fof(f11004,plain,
    ( spl7_1400
    | ~ spl7_10
    | ~ spl7_52
    | spl7_383 ),
    inference(avatar_split_clause,[],[f7293,f2175,f377,f186,f11002])).

fof(f11002,plain,
    ( spl7_1400
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1400])])).

fof(f7293,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_383 ),
    inference(resolution,[],[f7231,f2176])).

fof(f10993,plain,
    ( spl7_1398
    | ~ spl7_80
    | spl7_357
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8618,f5476,f1983,f511,f10991])).

fof(f10991,plain,
    ( spl7_1398
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1398])])).

fof(f8618,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_80
    | ~ spl7_357
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1984])).

fof(f10986,plain,
    ( spl7_1396
    | ~ spl7_80
    | spl7_349
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8617,f5476,f1947,f511,f10984])).

fof(f10984,plain,
    ( spl7_1396
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1396])])).

fof(f8617,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_80
    | ~ spl7_349
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1948])).

fof(f10979,plain,
    ( spl7_1088
    | spl7_1086
    | ~ spl7_8
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f7433,f2446,f179,f7666,f7696])).

fof(f7433,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_424 ),
    inference(superposition,[],[f2415,f2447])).

fof(f2415,plain,
    ( ! [X5] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(X5,X5))),k6_partfun1(X5)) = k6_partfun1(X5)
        | k1_zfmisc_1(k2_zfmisc_1(X5,X5)) = o_0_0_xboole_0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f854,f350])).

fof(f854,plain,(
    ! [X1] :
      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(X1,X1))),k6_partfun1(X1)) = k6_partfun1(X1) ) ),
    inference(resolution,[],[f601,f108])).

fof(f10964,plain,
    ( spl7_1392
    | ~ spl7_1395
    | ~ spl7_832
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f10954,f8947,f5476,f10962,f10956])).

fof(f10956,plain,
    ( spl7_1392
  <=> ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK6),X0) = k7_relat_1(k3_struct_0(sK6),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1392])])).

fof(f10962,plain,
    ( spl7_1395
  <=> ~ m1_subset_1(k3_struct_0(sK6),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1395])])).

fof(f10954,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_struct_0(sK6),o_0_0_xboole_0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK6),X0) = k7_relat_1(k3_struct_0(sK6),X0) )
    | ~ spl7_832
    | ~ spl7_1248 ),
    inference(superposition,[],[f5498,f8948])).

fof(f5498,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_partfun1(X8,X9,k3_struct_0(sK6),X10) = k7_relat_1(k3_struct_0(sK6),X10) )
    | ~ spl7_832 ),
    inference(resolution,[],[f5477,f140])).

fof(f10947,plain,
    ( spl7_1390
    | ~ spl7_10
    | ~ spl7_52
    | spl7_357 ),
    inference(avatar_split_clause,[],[f7300,f1983,f377,f186,f10945])).

fof(f10945,plain,
    ( spl7_1390
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1390])])).

fof(f7300,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_357 ),
    inference(resolution,[],[f7231,f1984])).

fof(f10940,plain,
    ( spl7_1388
    | ~ spl7_10
    | ~ spl7_52
    | spl7_349 ),
    inference(avatar_split_clause,[],[f7299,f1947,f377,f186,f10938])).

fof(f10938,plain,
    ( spl7_1388
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1388])])).

fof(f7299,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_349 ),
    inference(resolution,[],[f7231,f1948])).

fof(f10919,plain,
    ( spl7_1148
    | spl7_1104
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7894,f7880,f6299,f575,f7906,f8145])).

fof(f8145,plain,
    ( spl7_1148
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1148])])).

fof(f7906,plain,
    ( spl7_1104
  <=> v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1104])])).

fof(f7894,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f6323])).

fof(f10918,plain,
    ( spl7_1146
    | spl7_1104
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7893,f7880,f6261,f556,f7906,f8138])).

fof(f8138,plain,
    ( spl7_1146
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1146])])).

fof(f7893,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f6287])).

fof(f10917,plain,
    ( spl7_1106
    | spl7_1140
    | ~ spl7_20
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7863,f7836,f5169,f495,f223,f8112,f7913])).

fof(f7913,plain,
    ( spl7_1106
  <=> k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1106])])).

fof(f8112,plain,
    ( spl7_1140
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1140])])).

fof(f7863,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1096 ),
    inference(superposition,[],[f6010,f7837])).

fof(f6010,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(forward_demodulation,[],[f5983,f224])).

fof(f5983,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f117])).

fof(f10916,plain,
    ( spl7_1106
    | spl7_1138
    | ~ spl7_20
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7862,f7836,f5132,f479,f223,f8105,f7913])).

fof(f8105,plain,
    ( spl7_1138
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1138])])).

fof(f7862,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1096 ),
    inference(superposition,[],[f5868,f7837])).

fof(f5868,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),sK4(X0))
        | o_0_0_xboole_0 = X0 )
    | ~ spl7_20
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(forward_demodulation,[],[f5841,f224])).

fof(f5841,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(X0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),sK4(X0))
        | k1_xboole_0 = X0 )
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f117])).

fof(f10762,plain,
    ( ~ spl7_1383
    | spl7_1386
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f10736,f1660,f200,f165,f158,f151,f10760,f10742])).

fof(f10742,plain,
    ( spl7_1383
  <=> ~ v1_funct_1(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1383])])).

fof(f10760,plain,
    ( spl7_1386
  <=> ! [X13] : m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK1),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1386])])).

fof(f1660,plain,
    ( spl7_292
  <=> m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_292])])).

fof(f10736,plain,
    ( ! [X13] :
        ( m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK1),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(subsumption_resolution,[],[f10725,f1661])).

fof(f1661,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_292 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f10725,plain,
    ( ! [X13] :
        ( m1_subset_1(k7_relat_1(k4_tmap_1(sK0,sK1),X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(superposition,[],[f142,f10719])).

fof(f10719,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),X0) = k7_relat_1(k4_tmap_1(sK0,sK1),X0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(resolution,[],[f5152,f1661])).

fof(f10753,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_1383 ),
    inference(avatar_contradiction_clause,[],[f10752])).

fof(f10752,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_1383 ),
    inference(subsumption_resolution,[],[f10751,f152])).

fof(f10751,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_1383 ),
    inference(subsumption_resolution,[],[f10750,f159])).

fof(f10750,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_1383 ),
    inference(subsumption_resolution,[],[f10749,f166])).

fof(f10749,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_14
    | ~ spl7_1383 ),
    inference(subsumption_resolution,[],[f10748,f201])).

fof(f10748,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1383 ),
    inference(resolution,[],[f10743,f127])).

fof(f10743,plain,
    ( ~ v1_funct_1(k4_tmap_1(sK0,sK1))
    | ~ spl7_1383 ),
    inference(avatar_component_clause,[],[f10742])).

fof(f10747,plain,
    ( ~ spl7_1383
    | spl7_1384
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f10737,f1660,f200,f165,f158,f151,f10745,f10742])).

fof(f10745,plain,
    ( spl7_1384
  <=> ! [X14] : v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK1),X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1384])])).

fof(f10737,plain,
    ( ! [X14] :
        ( v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK1),X14))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(subsumption_resolution,[],[f10726,f1661])).

fof(f10726,plain,
    ( ! [X14] :
        ( v1_funct_1(k7_relat_1(k4_tmap_1(sK0,sK1),X14))
        | ~ m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k4_tmap_1(sK0,sK1)) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_292 ),
    inference(superposition,[],[f141,f10719])).

fof(f10618,plain,
    ( spl7_548
    | spl7_982
    | ~ spl7_20
    | ~ spl7_76
    | ~ spl7_230
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6254,f5169,f1326,f495,f223,f6552,f3447])).

fof(f3447,plain,
    ( spl7_548
  <=> k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_548])])).

fof(f6552,plain,
    ( spl7_982
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_982])])).

fof(f1326,plain,
    ( spl7_230
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_230])])).

fof(f6254,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_76
    | ~ spl7_230
    | ~ spl7_814 ),
    inference(superposition,[],[f6010,f1327])).

fof(f1327,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_230 ),
    inference(avatar_component_clause,[],[f1326])).

fof(f10560,plain,
    ( spl7_1380
    | ~ spl7_76
    | ~ spl7_814
    | spl7_1079 ),
    inference(avatar_split_clause,[],[f8388,f7634,f5169,f495,f10558])).

fof(f10558,plain,
    ( spl7_1380
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1380])])).

fof(f8388,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1079 ),
    inference(resolution,[],[f7635,f5949])).

fof(f10553,plain,
    ( spl7_1378
    | ~ spl7_76
    | spl7_417
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6903,f5169,f2383,f495,f10551])).

fof(f10551,plain,
    ( spl7_1378
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1378])])).

fof(f2383,plain,
    ( spl7_417
  <=> ~ v1_xboole_0(sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_417])])).

fof(f6903,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_76
    | ~ spl7_417
    | ~ spl7_814 ),
    inference(resolution,[],[f2384,f5949])).

fof(f2384,plain,
    ( ~ v1_xboole_0(sK4(k3_struct_0(sK1)))
    | ~ spl7_417 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f10429,plain,
    ( spl7_548
    | spl7_962
    | ~ spl7_20
    | ~ spl7_72
    | ~ spl7_230
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f6188,f5132,f1326,f479,f223,f6334,f3447])).

fof(f6334,plain,
    ( spl7_962
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_962])])).

fof(f6188,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_72
    | ~ spl7_230
    | ~ spl7_808 ),
    inference(superposition,[],[f5868,f1327])).

fof(f10428,plain,
    ( spl7_1376
    | ~ spl7_76
    | spl7_719
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6001,f5169,f4589,f495,f10426])).

fof(f10426,plain,
    ( spl7_1376
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1376])])).

fof(f4589,plain,
    ( spl7_719
  <=> ~ v1_xboole_0(k3_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_719])])).

fof(f6001,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6))))
    | ~ spl7_76
    | ~ spl7_719
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f4590])).

fof(f4590,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK3(sK6)))
    | ~ spl7_719 ),
    inference(avatar_component_clause,[],[f4589])).

fof(f10421,plain,
    ( spl7_1374
    | ~ spl7_76
    | spl7_311
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5999,f5169,f1734,f495,f10419])).

fof(f10419,plain,
    ( spl7_1374
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1374])])).

fof(f1734,plain,
    ( spl7_311
  <=> ~ v1_xboole_0(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_311])])).

fof(f5999,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_76
    | ~ spl7_311
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1735])).

fof(f1735,plain,
    ( ~ v1_xboole_0(k3_struct_0(sK3(sK0)))
    | ~ spl7_311 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f10414,plain,
    ( spl7_1372
    | ~ spl7_76
    | spl7_305
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5995,f5169,f1705,f495,f10412])).

fof(f10412,plain,
    ( spl7_1372
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1372])])).

fof(f1705,plain,
    ( spl7_305
  <=> ~ v1_xboole_0(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_305])])).

fof(f5995,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_76
    | ~ spl7_305
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1706])).

fof(f1706,plain,
    ( ~ v1_xboole_0(k4_tmap_1(sK0,sK1))
    | ~ spl7_305 ),
    inference(avatar_component_clause,[],[f1705])).

fof(f10351,plain,
    ( spl7_1370
    | ~ spl7_72
    | ~ spl7_808
    | spl7_1079 ),
    inference(avatar_split_clause,[],[f8387,f7634,f5132,f479,f10349])).

fof(f10349,plain,
    ( spl7_1370
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1370])])).

fof(f8387,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1079 ),
    inference(resolution,[],[f7635,f5807])).

fof(f10340,plain,
    ( spl7_1368
    | ~ spl7_72
    | spl7_417
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f6902,f5132,f2383,f479,f10338])).

fof(f10338,plain,
    ( spl7_1368
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1368])])).

fof(f6902,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_72
    | ~ spl7_417
    | ~ spl7_808 ),
    inference(resolution,[],[f2384,f5807])).

fof(f10333,plain,
    ( spl7_984
    | spl7_534
    | ~ spl7_90
    | ~ spl7_524
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6379,f6261,f3319,f556,f3398,f6595])).

fof(f6595,plain,
    ( spl7_984
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_984])])).

fof(f3398,plain,
    ( spl7_534
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_534])])).

fof(f6379,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_524
    | ~ spl7_950 ),
    inference(resolution,[],[f6287,f3320])).

fof(f10332,plain,
    ( ~ spl7_1365
    | spl7_1366
    | ~ spl7_1362 ),
    inference(avatar_split_clause,[],[f10311,f10306,f10330,f10327])).

fof(f10327,plain,
    ( spl7_1365
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1365])])).

fof(f10330,plain,
    ( spl7_1366
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1366])])).

fof(f10306,plain,
    ( spl7_1362
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1362])])).

fof(f10311,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))) )
    | ~ spl7_1362 ),
    inference(resolution,[],[f10307,f113])).

fof(f10307,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
    | ~ spl7_1362 ),
    inference(avatar_component_clause,[],[f10306])).

fof(f10308,plain,
    ( ~ spl7_957
    | spl7_1362
    | ~ spl7_36
    | ~ spl7_218 ),
    inference(avatar_split_clause,[],[f6296,f1261,f296,f10306,f6302])).

fof(f6302,plain,
    ( spl7_957
  <=> ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_957])])).

fof(f296,plain,
    ( spl7_36
  <=> l1_pre_topc(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1261,plain,
    ( spl7_218
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f6296,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) )
    | ~ spl7_36
    | ~ spl7_218 ),
    inference(subsumption_resolution,[],[f6294,f1262])).

fof(f1262,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
    | ~ spl7_218 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f6294,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
        | ~ m1_subset_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) )
    | ~ spl7_36 ),
    inference(superposition,[],[f142,f4976])).

fof(f4976,plain,
    ( ! [X5] : k2_partfun1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))),k3_struct_0(sK3(sK3(sK1))),X5) = k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X5)
    | ~ spl7_36 ),
    inference(resolution,[],[f4970,f297])).

fof(f297,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f296])).

fof(f10304,plain,
    ( spl7_1360
    | ~ spl7_72
    | spl7_719
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5859,f5132,f4589,f479,f10302])).

fof(f10302,plain,
    ( spl7_1360
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1360])])).

fof(f5859,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6))))
    | ~ spl7_72
    | ~ spl7_719
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f4590])).

fof(f10297,plain,
    ( spl7_1358
    | ~ spl7_72
    | spl7_311
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5857,f5132,f1734,f479,f10295])).

fof(f10295,plain,
    ( spl7_1358
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1358])])).

fof(f5857,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_72
    | ~ spl7_311
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1735])).

fof(f10290,plain,
    ( spl7_1356
    | ~ spl7_72
    | spl7_305
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5853,f5132,f1705,f479,f10288])).

fof(f10288,plain,
    ( spl7_1356
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1356])])).

fof(f5853,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_72
    | ~ spl7_305
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1706])).

fof(f10276,plain,
    ( spl7_1354
    | ~ spl7_80
    | spl7_117
    | ~ spl7_832
    | ~ spl7_1226 ),
    inference(avatar_split_clause,[],[f8815,f8790,f5476,f681,f511,f10274])).

fof(f10274,plain,
    ( spl7_1354
  <=> k1_funct_1(k3_struct_0(sK6),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1354])])).

fof(f8790,plain,
    ( spl7_1226
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1226])])).

fof(f8815,plain,
    ( k1_funct_1(k3_struct_0(sK6),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_80
    | ~ spl7_117
    | ~ spl7_832
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8801,f682])).

fof(f8801,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK6),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1226 ),
    inference(resolution,[],[f8791,f5500])).

fof(f8791,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl7_1226 ),
    inference(avatar_component_clause,[],[f8790])).

fof(f10266,plain,
    ( spl7_1352
    | ~ spl7_68
    | spl7_117
    | ~ spl7_792
    | ~ spl7_1226 ),
    inference(avatar_split_clause,[],[f8811,f8790,f5067,f681,f463,f10264])).

fof(f10264,plain,
    ( spl7_1352
  <=> k1_funct_1(k3_struct_0(sK1),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1352])])).

fof(f8811,plain,
    ( k1_funct_1(k3_struct_0(sK1),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_68
    | ~ spl7_117
    | ~ spl7_792
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8797,f682])).

fof(f8797,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK1),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1226 ),
    inference(resolution,[],[f8791,f5082])).

fof(f10256,plain,
    ( spl7_1336
    | spl7_648
    | ~ spl7_80
    | ~ spl7_642
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8519,f5476,f4053,f511,f4081,f10196])).

fof(f10196,plain,
    ( spl7_1336
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1336])])).

fof(f4081,plain,
    ( spl7_648
  <=> v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_648])])).

fof(f8519,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_642
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f4054])).

fof(f10255,plain,
    ( spl7_1350
    | spl7_1078
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1060 ),
    inference(avatar_split_clause,[],[f7467,f7461,f5067,f463,f7637,f10253])).

fof(f10253,plain,
    ( spl7_1350
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1350])])).

fof(f7637,plain,
    ( spl7_1078
  <=> v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1078])])).

fof(f7461,plain,
    ( spl7_1060
  <=> m1_subset_1(sK4(k3_struct_0(sK5)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1060])])).

fof(f7467,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1060 ),
    inference(resolution,[],[f7462,f5082])).

fof(f7462,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1060 ),
    inference(avatar_component_clause,[],[f7461])).

fof(f10248,plain,
    ( spl7_1348
    | spl7_1078
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1060 ),
    inference(avatar_split_clause,[],[f7466,f7461,f5040,f447,f7637,f10246])).

fof(f10246,plain,
    ( spl7_1348
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1348])])).

fof(f7466,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1060 ),
    inference(resolution,[],[f7462,f5055])).

fof(f10241,plain,
    ( spl7_1142
    | spl7_1066
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f7447,f5633,f5067,f463,f7514,f8119])).

fof(f7514,plain,
    ( spl7_1066
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1066])])).

fof(f7447,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_852 ),
    inference(resolution,[],[f5634,f5082])).

fof(f10240,plain,
    ( spl7_1144
    | spl7_1066
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f7446,f5633,f5040,f447,f7514,f8126])).

fof(f7446,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_852 ),
    inference(resolution,[],[f5634,f5055])).

fof(f10239,plain,
    ( spl7_1334
    | spl7_648
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_642 ),
    inference(avatar_split_clause,[],[f7224,f4053,f377,f186,f4081,f10189])).

fof(f10189,plain,
    ( spl7_1334
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1334])])).

fof(f7224,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_642 ),
    inference(resolution,[],[f5457,f4054])).

fof(f10235,plain,
    ( spl7_1332
    | spl7_648
    | ~ spl7_68
    | ~ spl7_642
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5377,f5067,f4053,f463,f4081,f10182])).

fof(f10182,plain,
    ( spl7_1332
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1332])])).

fof(f5377,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_642
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f4054])).

fof(f10231,plain,
    ( spl7_1346
    | ~ spl7_94
    | ~ spl7_582
    | spl7_649
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f10145,f6299,f4078,f3611,f575,f10229])).

fof(f10229,plain,
    ( spl7_1346
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1346])])).

fof(f3611,plain,
    ( spl7_582
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_582])])).

fof(f10145,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_956 ),
    inference(forward_demodulation,[],[f10135,f3612])).

fof(f3612,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_582 ),
    inference(avatar_component_clause,[],[f3611])).

fof(f10135,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_94
    | ~ spl7_649
    | ~ spl7_956 ),
    inference(resolution,[],[f4079,f6667])).

fof(f10224,plain,
    ( spl7_1344
    | ~ spl7_90
    | ~ spl7_582
    | spl7_649
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f10144,f6261,f4078,f3611,f556,f10222])).

fof(f10222,plain,
    ( spl7_1344
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1344])])).

fof(f10144,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_950 ),
    inference(forward_demodulation,[],[f10134,f3612])).

fof(f10134,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_90
    | ~ spl7_649
    | ~ spl7_950 ),
    inference(resolution,[],[f4079,f6386])).

fof(f10217,plain,
    ( spl7_1342
    | ~ spl7_76
    | ~ spl7_582
    | spl7_649
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f10143,f5169,f4078,f3611,f495,f10215])).

fof(f10215,plain,
    ( spl7_1342
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1342])])).

fof(f10143,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_814 ),
    inference(forward_demodulation,[],[f10133,f3612])).

fof(f10133,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_76
    | ~ spl7_649
    | ~ spl7_814 ),
    inference(resolution,[],[f4079,f5949])).

fof(f10210,plain,
    ( spl7_1340
    | ~ spl7_72
    | ~ spl7_582
    | spl7_649
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f10142,f5132,f4078,f3611,f479,f10208])).

fof(f10208,plain,
    ( spl7_1340
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1340])])).

fof(f10142,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_808 ),
    inference(forward_demodulation,[],[f10132,f3612])).

fof(f10132,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_72
    | ~ spl7_649
    | ~ spl7_808 ),
    inference(resolution,[],[f4079,f5807])).

fof(f10203,plain,
    ( spl7_1212
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_124
    | spl7_165 ),
    inference(avatar_split_clause,[],[f8292,f937,f717,f377,f186,f8716])).

fof(f8716,plain,
    ( spl7_1212
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1212])])).

fof(f717,plain,
    ( spl7_124
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f8292,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_124
    | ~ spl7_165 ),
    inference(forward_demodulation,[],[f8284,f718])).

fof(f718,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f717])).

fof(f8284,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_165 ),
    inference(resolution,[],[f938,f7231])).

fof(f10202,plain,
    ( spl7_710
    | spl7_1338
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f4120,f186,f10200,f4417])).

fof(f4417,plain,
    ( spl7_710
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_710])])).

fof(f10200,plain,
    ( spl7_1338
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | k1_funct_1(k2_tmap_1(X1,X2,X0,sK5),X3) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,sK5),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1338])])).

fof(f4120,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | k1_funct_1(k2_tmap_1(X1,X2,X0,sK5),X3) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,sK5),X3)
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f4119,f2368])).

fof(f4119,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ m1_subset_1(k2_tmap_1(X1,X2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X2))))
        | k1_funct_1(k2_tmap_1(X1,X2,X0,sK5),X3) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,sK5),X3)
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f4117,f2001])).

fof(f4117,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ m1_subset_1(k2_tmap_1(X1,X2,X0,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X2))))
        | k1_funct_1(k2_tmap_1(X1,X2,X0,sK5),X3) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(X2),k2_tmap_1(X1,X2,X0,sK5),X3)
        | ~ v1_funct_1(k2_tmap_1(X1,X2,X0,sK5))
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2217,f136])).

fof(f2217,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k2_tmap_1(X0,X1,X2,sK5),u1_struct_0(sK5),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl7_10 ),
    inference(resolution,[],[f138,f187])).

fof(f10198,plain,
    ( spl7_1336
    | ~ spl7_80
    | ~ spl7_582
    | spl7_649
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f10148,f5476,f4078,f3611,f511,f10196])).

fof(f10148,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_832 ),
    inference(forward_demodulation,[],[f10137,f3612])).

fof(f10137,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_80
    | ~ spl7_649
    | ~ spl7_832 ),
    inference(resolution,[],[f4079,f8527])).

fof(f10191,plain,
    ( spl7_1334
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_582
    | spl7_649 ),
    inference(avatar_split_clause,[],[f10146,f4078,f3611,f377,f186,f10189])).

fof(f10146,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_582
    | ~ spl7_649 ),
    inference(forward_demodulation,[],[f10136,f3612])).

fof(f10136,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_649 ),
    inference(resolution,[],[f4079,f7231])).

fof(f10184,plain,
    ( spl7_1332
    | ~ spl7_68
    | ~ spl7_582
    | spl7_649
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f10141,f5067,f4078,f3611,f463,f10182])).

fof(f10141,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_792 ),
    inference(forward_demodulation,[],[f10131,f3612])).

fof(f10131,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_68
    | ~ spl7_649
    | ~ spl7_792 ),
    inference(resolution,[],[f4079,f5386])).

fof(f10177,plain,
    ( spl7_1330
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1100
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f10158,f7903,f7880,f377,f186,f10175])).

fof(f10175,plain,
    ( spl7_1330
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1330])])).

fof(f10158,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1100
    | ~ spl7_1105 ),
    inference(subsumption_resolution,[],[f7892,f7904])).

fof(f7892,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f5457])).

fof(f10170,plain,
    ( ~ spl7_851
    | ~ spl7_230
    | spl7_289
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f10167,f2446,f1632,f1326,f5623])).

fof(f5623,plain,
    ( spl7_851
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_851])])).

fof(f1632,plain,
    ( spl7_289
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_289])])).

fof(f10167,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_230
    | ~ spl7_289
    | ~ spl7_424 ),
    inference(forward_demodulation,[],[f10166,f2447])).

fof(f10166,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_230
    | ~ spl7_289 ),
    inference(forward_demodulation,[],[f1633,f1327])).

fof(f1633,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_289 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f10169,plain,
    ( ~ spl7_10
    | ~ spl7_52
    | ~ spl7_230
    | spl7_289
    | ~ spl7_424
    | ~ spl7_1096
    | spl7_1105
    | ~ spl7_1132 ),
    inference(avatar_contradiction_clause,[],[f10168])).

fof(f10168,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_230
    | ~ spl7_289
    | ~ spl7_424
    | ~ spl7_1096
    | ~ spl7_1105
    | ~ spl7_1132 ),
    inference(subsumption_resolution,[],[f10167,f8086])).

fof(f8086,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1096
    | ~ spl7_1105
    | ~ spl7_1132 ),
    inference(forward_demodulation,[],[f8085,f8044])).

fof(f8044,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1132 ),
    inference(avatar_component_clause,[],[f8043])).

fof(f8043,plain,
    ( spl7_1132
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1132])])).

fof(f8085,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8077,f7837])).

fof(f8077,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f7231])).

fof(f10165,plain,
    ( ~ spl7_10
    | ~ spl7_52
    | ~ spl7_424
    | spl7_527
    | ~ spl7_1096
    | spl7_1105
    | ~ spl7_1132 ),
    inference(avatar_contradiction_clause,[],[f10164])).

fof(f10164,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_424
    | ~ spl7_527
    | ~ spl7_1096
    | ~ spl7_1105
    | ~ spl7_1132 ),
    inference(subsumption_resolution,[],[f10163,f8086])).

fof(f10163,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_424
    | ~ spl7_527 ),
    inference(forward_demodulation,[],[f3331,f2447])).

fof(f3331,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_527 ),
    inference(avatar_component_clause,[],[f3330])).

fof(f3330,plain,
    ( spl7_527
  <=> k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_527])])).

fof(f10162,plain,
    ( ~ spl7_10
    | ~ spl7_52
    | spl7_851
    | ~ spl7_1096
    | spl7_1105
    | ~ spl7_1132 ),
    inference(avatar_contradiction_clause,[],[f10161])).

fof(f10161,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_851
    | ~ spl7_1096
    | ~ spl7_1105
    | ~ spl7_1132 ),
    inference(subsumption_resolution,[],[f5624,f8086])).

fof(f5624,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_851 ),
    inference(avatar_component_clause,[],[f5623])).

fof(f10156,plain,
    ( spl7_1328
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_582
    | spl7_649
    | ~ spl7_850 ),
    inference(avatar_split_clause,[],[f10147,f5626,f4078,f3611,f377,f186,f10154])).

fof(f10154,plain,
    ( spl7_1328
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1328])])).

fof(f5626,plain,
    ( spl7_850
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_850])])).

fof(f10147,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_582
    | ~ spl7_649
    | ~ spl7_850 ),
    inference(forward_demodulation,[],[f10146,f5627])).

fof(f5627,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_850 ),
    inference(avatar_component_clause,[],[f5626])).

fof(f10128,plain,
    ( spl7_652
    | ~ spl7_20
    | ~ spl7_648 ),
    inference(avatar_split_clause,[],[f10118,f4081,f223,f4095])).

fof(f4095,plain,
    ( spl7_652
  <=> k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_652])])).

fof(f10118,plain,
    ( k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_648 ),
    inference(forward_demodulation,[],[f10106,f224])).

fof(f10106,plain,
    ( k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))) = k1_xboole_0
    | ~ spl7_648 ),
    inference(resolution,[],[f4082,f117])).

fof(f4082,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_648 ),
    inference(avatar_component_clause,[],[f4081])).

fof(f10105,plain,
    ( spl7_1326
    | spl7_648
    | ~ spl7_64
    | ~ spl7_642
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5237,f5040,f4053,f447,f4081,f10103])).

fof(f10103,plain,
    ( spl7_1326
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1326])])).

fof(f5237,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_642
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f4054])).

fof(f10098,plain,
    ( spl7_1324
    | ~ spl7_10
    | ~ spl7_52
    | spl7_117
    | ~ spl7_1226 ),
    inference(avatar_split_clause,[],[f8814,f8790,f681,f377,f186,f10096])).

fof(f10096,plain,
    ( spl7_1324
  <=> k1_funct_1(k3_struct_0(sK5),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1324])])).

fof(f8814,plain,
    ( k1_funct_1(k3_struct_0(sK5),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_117
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8800,f682])).

fof(f8800,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK5),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_1226 ),
    inference(resolution,[],[f8791,f5457])).

fof(f10091,plain,
    ( ~ spl7_1321
    | spl7_1322
    | ~ spl7_1318 ),
    inference(avatar_split_clause,[],[f10070,f10065,f10089,f10086])).

fof(f10086,plain,
    ( spl7_1321
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1321])])).

fof(f10089,plain,
    ( spl7_1322
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1322])])).

fof(f10065,plain,
    ( spl7_1318
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1318])])).

fof(f10070,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))) )
    | ~ spl7_1318 ),
    inference(resolution,[],[f10066,f113])).

fof(f10066,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
    | ~ spl7_1318 ),
    inference(avatar_component_clause,[],[f10065])).

fof(f10067,plain,
    ( ~ spl7_951
    | spl7_1318
    | ~ spl7_34
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f6258,f1250,f286,f10065,f6264])).

fof(f6264,plain,
    ( spl7_951
  <=> ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_951])])).

fof(f286,plain,
    ( spl7_34
  <=> l1_pre_topc(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1250,plain,
    ( spl7_216
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f6258,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) )
    | ~ spl7_34
    | ~ spl7_216 ),
    inference(subsumption_resolution,[],[f6256,f1251])).

fof(f1251,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
    | ~ spl7_216 ),
    inference(avatar_component_clause,[],[f1250])).

fof(f6256,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
        | ~ m1_subset_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) )
    | ~ spl7_34 ),
    inference(superposition,[],[f142,f4975])).

fof(f4975,plain,
    ( ! [X4] : k2_partfun1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))),k3_struct_0(sK3(sK3(sK0))),X4) = k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X4)
    | ~ spl7_34 ),
    inference(resolution,[],[f4970,f287])).

fof(f287,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f286])).

fof(f10063,plain,
    ( spl7_710
    | spl7_1316
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f4122,f186,f10061,f4417])).

fof(f10061,plain,
    ( spl7_1316
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(X6),k2_tmap_1(X5,X6,X4,sK5),X7),u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X6)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1316])])).

fof(f4122,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(X6),k2_tmap_1(X5,X6,X4,sK5),X7),u1_struct_0(X6))
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f4121,f2368])).

fof(f4121,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | ~ m1_subset_1(k2_tmap_1(X5,X6,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X6))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(X6),k2_tmap_1(X5,X6,X4,sK5),X7),u1_struct_0(X6))
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f4118,f2001])).

fof(f4118,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
        | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6))
        | ~ v1_funct_1(X4)
        | ~ l1_struct_0(X6)
        | ~ l1_struct_0(X5)
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | ~ m1_subset_1(k2_tmap_1(X5,X6,X4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X6))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(X6),k2_tmap_1(X5,X6,X4,sK5),X7),u1_struct_0(X6))
        | ~ v1_funct_1(k2_tmap_1(X5,X6,X4,sK5))
        | v1_xboole_0(u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f2217,f135])).

fof(f10059,plain,
    ( spl7_402
    | spl7_1314
    | ~ spl7_802 ),
    inference(avatar_split_clause,[],[f5116,f5109,f10057,f2339])).

fof(f10057,plain,
    ( spl7_1314
  <=> ! [X6] :
        ( v1_xboole_0(k7_relat_1(k3_struct_0(sK1),X6))
        | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k7_relat_1(k3_struct_0(sK1),X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1314])])).

fof(f5116,plain,
    ( ! [X6] :
        ( v1_xboole_0(k7_relat_1(k3_struct_0(sK1),X6))
        | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k7_relat_1(k3_struct_0(sK1),X6)) )
    | ~ spl7_802 ),
    inference(resolution,[],[f5110,f531])).

fof(f10055,plain,
    ( spl7_1310
    | spl7_1312
    | ~ spl7_664
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f10006,f8947,f4189,f10053,f10050])).

fof(f10053,plain,
    ( spl7_1312
  <=> ! [X7] :
        ( m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,sK4(k4_tmap_1(sK0,sK3(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1312])])).

fof(f4189,plain,
    ( spl7_664
  <=> m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_664])])).

fof(f10006,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(sK4(k4_tmap_1(sK0,sK3(sK0))))
        | ~ m1_subset_1(X7,sK4(k4_tmap_1(sK0,sK3(sK0)))) )
    | ~ spl7_664
    | ~ spl7_1248 ),
    inference(resolution,[],[f9904,f4190])).

fof(f4190,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),o_0_0_xboole_0)
    | ~ spl7_664 ),
    inference(avatar_component_clause,[],[f4189])).

fof(f10045,plain,
    ( spl7_1306
    | ~ spl7_1309
    | ~ spl7_814
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9900,f8947,f5169,f10043,f10037])).

fof(f10037,plain,
    ( spl7_1306
  <=> ! [X10] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK3(sK1)),X10) = k7_relat_1(k3_struct_0(sK3(sK1)),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1306])])).

fof(f10043,plain,
    ( spl7_1309
  <=> ~ m1_subset_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1309])])).

fof(f9900,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK3(sK1)),X10) = k7_relat_1(k3_struct_0(sK3(sK1)),X10) )
    | ~ spl7_814
    | ~ spl7_1248 ),
    inference(superposition,[],[f5191,f8948])).

fof(f5191,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_partfun1(X8,X9,k3_struct_0(sK3(sK1)),X10) = k7_relat_1(k3_struct_0(sK3(sK1)),X10) )
    | ~ spl7_814 ),
    inference(resolution,[],[f5170,f140])).

fof(f10035,plain,
    ( spl7_1304
    | spl7_485
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9933,f8947,f2881,f10033])).

fof(f9933,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_485
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f9914,f2882])).

fof(f9914,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1248 ),
    inference(superposition,[],[f3732,f8948])).

fof(f10028,plain,
    ( spl7_1300
    | ~ spl7_1303
    | ~ spl7_808
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9899,f8947,f5132,f10026,f10020])).

fof(f10020,plain,
    ( spl7_1300
  <=> ! [X9] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK3(sK0)),X9) = k7_relat_1(k3_struct_0(sK3(sK0)),X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1300])])).

fof(f10026,plain,
    ( spl7_1303
  <=> ~ m1_subset_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1303])])).

fof(f9899,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK3(sK0)),X9) = k7_relat_1(k3_struct_0(sK3(sK0)),X9) )
    | ~ spl7_808
    | ~ spl7_1248 ),
    inference(superposition,[],[f5157,f8948])).

fof(f5157,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_partfun1(X8,X9,k3_struct_0(sK3(sK0)),X10) = k7_relat_1(k3_struct_0(sK3(sK0)),X10) )
    | ~ spl7_808 ),
    inference(resolution,[],[f5133,f140])).

fof(f10001,plain,
    ( ~ spl7_1299
    | ~ spl7_1248
    | spl7_1293 ),
    inference(avatar_split_clause,[],[f10000,f9703,f8947,f9994])).

fof(f9994,plain,
    ( spl7_1299
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1299])])).

fof(f9703,plain,
    ( spl7_1293
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1293])])).

fof(f10000,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK0))
    | ~ spl7_1248
    | ~ spl7_1293 ),
    inference(forward_demodulation,[],[f9704,f8948])).

fof(f9704,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) != k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_1293 ),
    inference(avatar_component_clause,[],[f9703])).

fof(f9999,plain,
    ( spl7_1298
    | ~ spl7_1248
    | ~ spl7_1292 ),
    inference(avatar_split_clause,[],[f9885,f9706,f8947,f9997])).

fof(f9997,plain,
    ( spl7_1298
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1298])])).

fof(f9706,plain,
    ( spl7_1292
  <=> k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1292])])).

fof(f9885,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),o_0_0_xboole_0),k3_struct_0(sK0))
    | ~ spl7_1248
    | ~ spl7_1292 ),
    inference(superposition,[],[f9707,f8948])).

fof(f9707,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_1292 ),
    inference(avatar_component_clause,[],[f9706])).

fof(f9992,plain,
    ( spl7_1296
    | ~ spl7_1248
    | ~ spl7_1290 ),
    inference(avatar_split_clause,[],[f9884,f9699,f8947,f9990])).

fof(f9990,plain,
    ( spl7_1296
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1296])])).

fof(f9699,plain,
    ( spl7_1290
  <=> k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1290])])).

fof(f9884,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),o_0_0_xboole_0),k3_struct_0(sK0))
    | ~ spl7_1248
    | ~ spl7_1290 ),
    inference(superposition,[],[f9700,f8948])).

fof(f9700,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_1290 ),
    inference(avatar_component_clause,[],[f9699])).

fof(f9863,plain,
    ( spl7_1294
    | spl7_397 ),
    inference(avatar_split_clause,[],[f9668,f2316,f9861])).

fof(f9861,plain,
    ( spl7_1294
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) = sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1294])])).

fof(f9668,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) = sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_397 ),
    inference(resolution,[],[f2317,f858])).

fof(f9708,plain,
    ( spl7_1292
    | ~ spl7_62
    | ~ spl7_64
    | spl7_397
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f9678,f5040,f2316,f447,f438,f9706])).

fof(f9678,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_62
    | ~ spl7_64
    | ~ spl7_397
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f9666,f439])).

fof(f9666,plain,
    ( k1_funct_1(k3_struct_0(sK0),k6_partfun1(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl7_64
    | ~ spl7_397
    | ~ spl7_788 ),
    inference(resolution,[],[f2317,f5227])).

fof(f5227,plain,
    ( ! [X12] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X12,X12)))
        | k1_funct_1(k3_struct_0(sK0),k6_partfun1(X12)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(X12,X12))),k6_partfun1(X12)) )
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f108])).

fof(f9701,plain,
    ( spl7_1290
    | ~ spl7_62
    | ~ spl7_68
    | spl7_397
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f9677,f5067,f2316,f463,f438,f9699])).

fof(f9677,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0))
    | ~ spl7_62
    | ~ spl7_68
    | ~ spl7_397
    | ~ spl7_792 ),
    inference(forward_demodulation,[],[f9665,f439])).

fof(f9665,plain,
    ( k1_funct_1(k3_struct_0(sK1),k6_partfun1(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k6_partfun1(u1_struct_0(sK0)))
    | ~ spl7_68
    | ~ spl7_397
    | ~ spl7_792 ),
    inference(resolution,[],[f2317,f5367])).

fof(f5367,plain,
    ( ! [X12] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X12,X12)))
        | k1_funct_1(k3_struct_0(sK1),k6_partfun1(X12)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X12,X12))),k6_partfun1(X12)) )
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f108])).

fof(f9694,plain,
    ( ~ spl7_1289
    | ~ spl7_4
    | spl7_181
    | spl7_1255 ),
    inference(avatar_split_clause,[],[f9684,f9045,f1019,f165,f9692])).

fof(f9692,plain,
    ( spl7_1289
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1289])])).

fof(f9045,plain,
    ( spl7_1255
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1255])])).

fof(f9684,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_181
    | ~ spl7_1255 ),
    inference(subsumption_resolution,[],[f9683,f166])).

fof(f9683,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_181
    | ~ spl7_1255 ),
    inference(subsumption_resolution,[],[f9681,f1020])).

fof(f9681,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK0))
    | v1_xboole_0(k3_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1255 ),
    inference(resolution,[],[f9046,f2421])).

fof(f2421,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k3_struct_0(X1))
      | v1_xboole_0(k3_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f1008,f114])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | v1_xboole_0(k3_struct_0(X1))
      | ~ m1_subset_1(X0,k3_struct_0(X1))
      | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) ) ),
    inference(resolution,[],[f640,f112])).

fof(f9046,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1255 ),
    inference(avatar_component_clause,[],[f9045])).

fof(f9680,plain,
    ( spl7_1286
    | spl7_406
    | ~ spl7_1254 ),
    inference(avatar_split_clause,[],[f9052,f9048,f2352,f9662])).

fof(f9662,plain,
    ( spl7_1286
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1286])])).

fof(f2352,plain,
    ( spl7_406
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_406])])).

fof(f9048,plain,
    ( spl7_1254
  <=> m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1254])])).

fof(f9052,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_1254 ),
    inference(resolution,[],[f9049,f601])).

fof(f9049,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1254 ),
    inference(avatar_component_clause,[],[f9048])).

fof(f9664,plain,
    ( spl7_406
    | spl7_1286
    | spl7_485
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8999,f8947,f2881,f9662,f2352])).

fof(f8999,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_485
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f8998,f8948])).

fof(f8998,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) = sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_485
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f8976,f2882])).

fof(f8976,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) = sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_1248 ),
    inference(superposition,[],[f1211,f8948])).

fof(f9657,plain,
    ( ~ spl7_1283
    | spl7_1284
    | ~ spl7_664
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9068,f8947,f4189,f9655,f9652])).

fof(f9652,plain,
    ( spl7_1283
  <=> ~ v1_funct_1(sK4(k4_tmap_1(sK0,sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1283])])).

fof(f9655,plain,
    ( spl7_1284
  <=> ! [X5] : m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k4_tmap_1(sK0,sK3(sK0))),X5),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1284])])).

fof(f9068,plain,
    ( ! [X5] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k4_tmap_1(sK0,sK3(sK0))),X5),o_0_0_xboole_0)
        | ~ v1_funct_1(sK4(k4_tmap_1(sK0,sK3(sK0)))) )
    | ~ spl7_664
    | ~ spl7_1248 ),
    inference(resolution,[],[f8992,f4190])).

fof(f8992,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,o_0_0_xboole_0)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X2,X3),o_0_0_xboole_0)
        | ~ v1_funct_1(X2) )
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f8963,f8948])).

fof(f8963,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),X2,X3),o_0_0_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2) )
    | ~ spl7_1248 ),
    inference(superposition,[],[f142,f8948])).

fof(f9542,plain,
    ( spl7_1280
    | spl7_592
    | ~ spl7_18
    | ~ spl7_396 ),
    inference(avatar_split_clause,[],[f9173,f2319,f214,f3644,f9540])).

fof(f9540,plain,
    ( spl7_1280
  <=> m1_subset_1(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1280])])).

fof(f3644,plain,
    ( spl7_592
  <=> ! [X14] :
        ( ~ m1_subset_1(u1_struct_0(sK1),X14)
        | k1_funct_1(k6_partfun1(X14),sK4(X14)) = sK4(X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_592])])).

fof(f214,plain,
    ( spl7_18
  <=> r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f9173,plain,
    ( ! [X35] :
        ( ~ m1_subset_1(u1_struct_0(sK1),X35)
        | m1_subset_1(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(X35),sK4(X35)) = sK4(X35) )
    | ~ spl7_18
    | ~ spl7_396 ),
    inference(superposition,[],[f639,f8926])).

fof(f8926,plain,
    ( ! [X4] :
        ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = X4
        | k1_funct_1(k6_partfun1(X4),sK4(X4)) = sK4(X4) )
    | ~ spl7_396 ),
    inference(resolution,[],[f2320,f890])).

fof(f2320,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_396 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f639,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK2,X0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f133,f215])).

fof(f215,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f214])).

fof(f9535,plain,
    ( spl7_406
    | ~ spl7_1279
    | spl7_1124
    | spl7_485
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9002,f8947,f2881,f7978,f9533,f2352])).

fof(f9533,plain,
    ( spl7_1279
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1279])])).

fof(f9002,plain,
    ( v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_485
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f9001,f2882])).

fof(f9001,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f9000,f8948])).

fof(f9000,plain,
    ( v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f8977,f8948])).

fof(f8977,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_1248 ),
    inference(superposition,[],[f1212,f8948])).

fof(f9527,plain,
    ( spl7_800
    | spl7_1276
    | ~ spl7_396
    | ~ spl7_796 ),
    inference(avatar_split_clause,[],[f9322,f5090,f2319,f9525,f5105])).

fof(f5105,plain,
    ( spl7_800
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK0),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_800])])).

fof(f9525,plain,
    ( spl7_1276
  <=> ! [X46] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(X46)),sK4(k1_zfmisc_1(X46))) = sK4(k1_zfmisc_1(X46))
        | ~ v1_relat_1(X46) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1276])])).

fof(f9322,plain,
    ( ! [X47,X46] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(X46)),sK4(k1_zfmisc_1(X46))) = sK4(k1_zfmisc_1(X46))
        | v1_relat_1(k7_relat_1(k3_struct_0(sK0),X47))
        | ~ v1_relat_1(X46) )
    | ~ spl7_396
    | ~ spl7_796 ),
    inference(resolution,[],[f9154,f113])).

fof(f9154,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK0),X5),X4)
        | k1_funct_1(k6_partfun1(X4),sK4(X4)) = sK4(X4) )
    | ~ spl7_396
    | ~ spl7_796 ),
    inference(superposition,[],[f5091,f8926])).

fof(f9503,plain,
    ( spl7_1274
    | ~ spl7_495
    | ~ spl7_10
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8964,f8947,f186,f3130,f9501])).

fof(f9501,plain,
    ( spl7_1274
  <=> ! [X4] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK5),X4) = k7_relat_1(k3_struct_0(sK5),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1274])])).

fof(f3130,plain,
    ( spl7_495
  <=> ~ m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_495])])).

fof(f8964,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0)
        | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK5),X4) = k7_relat_1(k3_struct_0(sK5),X4) )
    | ~ spl7_10
    | ~ spl7_1248 ),
    inference(superposition,[],[f2984,f8948])).

fof(f2984,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,k3_struct_0(sK5),X2) = k7_relat_1(k3_struct_0(sK5),X2) )
    | ~ spl7_10 ),
    inference(resolution,[],[f1265,f187])).

fof(f9499,plain,
    ( spl7_1272
    | ~ spl7_1270 ),
    inference(avatar_split_clause,[],[f9490,f9485,f9497])).

fof(f9497,plain,
    ( spl7_1272
  <=> m1_subset_1(sK4(sK4(k3_struct_0(sK5))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1272])])).

fof(f9485,plain,
    ( spl7_1270
  <=> ! [X8] :
        ( m1_subset_1(X8,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,sK4(k3_struct_0(sK5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1270])])).

fof(f9490,plain,
    ( m1_subset_1(sK4(sK4(k3_struct_0(sK5))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1270 ),
    inference(resolution,[],[f9486,f121])).

fof(f9486,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,sK4(k3_struct_0(sK5)))
        | m1_subset_1(X8,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl7_1270 ),
    inference(avatar_component_clause,[],[f9485])).

fof(f9487,plain,
    ( spl7_1080
    | spl7_1270
    | ~ spl7_1166
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9103,f8947,f8349,f9485,f7643])).

fof(f7643,plain,
    ( spl7_1080
  <=> v1_xboole_0(sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1080])])).

fof(f8349,plain,
    ( spl7_1166
  <=> m1_subset_1(sK4(k3_struct_0(sK5)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1166])])).

fof(f9103,plain,
    ( ! [X8] :
        ( m1_subset_1(X8,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(sK4(k3_struct_0(sK5)))
        | ~ m1_subset_1(X8,sK4(k3_struct_0(sK5))) )
    | ~ spl7_1166
    | ~ spl7_1248 ),
    inference(resolution,[],[f8973,f8350])).

fof(f8350,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),o_0_0_xboole_0)
    | ~ spl7_1166 ),
    inference(avatar_component_clause,[],[f8349])).

fof(f8973,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,o_0_0_xboole_0)
        | m1_subset_1(X13,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X13,X12) )
    | ~ spl7_1248 ),
    inference(superposition,[],[f640,f8948])).

fof(f9425,plain,
    ( ~ spl7_1267
    | spl7_1268
    | ~ spl7_1166
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9069,f8947,f8349,f9423,f9420])).

fof(f9420,plain,
    ( spl7_1267
  <=> ~ v1_funct_1(sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1267])])).

fof(f9423,plain,
    ( spl7_1268
  <=> ! [X6] : m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k3_struct_0(sK5)),X6),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1268])])).

fof(f9069,plain,
    ( ! [X6] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k3_struct_0(sK5)),X6),o_0_0_xboole_0)
        | ~ v1_funct_1(sK4(k3_struct_0(sK5))) )
    | ~ spl7_1166
    | ~ spl7_1248 ),
    inference(resolution,[],[f8992,f8350])).

fof(f9410,plain,
    ( spl7_1264
    | spl7_406
    | ~ spl7_1260 ),
    inference(avatar_split_clause,[],[f9386,f9382,f2352,f9408])).

fof(f9408,plain,
    ( spl7_1264
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1264])])).

fof(f9382,plain,
    ( spl7_1260
  <=> m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1260])])).

fof(f9386,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1260 ),
    inference(resolution,[],[f9383,f601])).

fof(f9383,plain,
    ( m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1260 ),
    inference(avatar_component_clause,[],[f9382])).

fof(f9402,plain,
    ( spl7_1262
    | spl7_181
    | ~ spl7_1250 ),
    inference(avatar_split_clause,[],[f9368,f9010,f1019,f9400])).

fof(f9400,plain,
    ( spl7_1262
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK0)),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1262])])).

fof(f9010,plain,
    ( spl7_1250
  <=> m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1250])])).

fof(f9368,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK0)),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_181
    | ~ spl7_1250 ),
    inference(subsumption_resolution,[],[f9359,f1020])).

fof(f9359,plain,
    ( v1_xboole_0(k3_struct_0(sK0))
    | k1_funct_1(k6_partfun1(k3_struct_0(sK0)),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1250 ),
    inference(resolution,[],[f9011,f601])).

fof(f9011,plain,
    ( m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK0))
    | ~ spl7_1250 ),
    inference(avatar_component_clause,[],[f9010])).

fof(f9384,plain,
    ( spl7_1260
    | ~ spl7_182
    | ~ spl7_1250 ),
    inference(avatar_split_clause,[],[f9357,f9010,f1025,f9382])).

fof(f9357,plain,
    ( m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_182
    | ~ spl7_1250 ),
    inference(resolution,[],[f9011,f1026])).

fof(f9350,plain,
    ( spl7_1250
    | ~ spl7_394
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9349,f8947,f2310,f9010])).

fof(f2310,plain,
    ( spl7_394
  <=> m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_394])])).

fof(f9349,plain,
    ( m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK0))
    | ~ spl7_394
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f2311,f8948])).

fof(f2311,plain,
    ( m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl7_394 ),
    inference(avatar_component_clause,[],[f2310])).

fof(f9348,plain,
    ( spl7_1258
    | spl7_395
    | ~ spl7_396 ),
    inference(avatar_split_clause,[],[f9288,f2319,f2313,f9346])).

fof(f9346,plain,
    ( spl7_1258
  <=> k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK0))),sK4(sK4(k3_struct_0(sK0)))) = sK4(sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1258])])).

fof(f2313,plain,
    ( spl7_395
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_395])])).

fof(f9288,plain,
    ( k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK0))),sK4(sK4(k3_struct_0(sK0)))) = sK4(sK4(k3_struct_0(sK0)))
    | ~ spl7_395
    | ~ spl7_396 ),
    inference(resolution,[],[f9151,f121])).

fof(f9151,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK0))
        | k1_funct_1(k6_partfun1(X1),sK4(X1)) = sK4(X1) )
    | ~ spl7_395
    | ~ spl7_396 ),
    inference(superposition,[],[f2314,f8926])).

fof(f2314,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl7_395 ),
    inference(avatar_component_clause,[],[f2313])).

fof(f9086,plain,
    ( ~ spl7_701
    | spl7_1256
    | ~ spl7_10
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f9073,f8947,f3127,f186,f9084,f4380])).

fof(f9084,plain,
    ( spl7_1256
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1256])])).

fof(f9073,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),o_0_0_xboole_0)
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_10
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f9064,f8993])).

fof(f8993,plain,
    ( ! [X4] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK5),X4) = k7_relat_1(k3_struct_0(sK5),X4)
    | ~ spl7_10
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f8964,f3128])).

fof(f9064,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK5),X0),o_0_0_xboole_0)
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_494
    | ~ spl7_1248 ),
    inference(resolution,[],[f8992,f3128])).

fof(f9050,plain,
    ( spl7_1254
    | spl7_485
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8997,f8947,f2881,f9048])).

fof(f8997,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_485
    | ~ spl7_1248 ),
    inference(subsumption_resolution,[],[f8996,f2882])).

fof(f8996,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f8975,f8948])).

fof(f8975,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ spl7_1248 ),
    inference(superposition,[],[f1209,f8948])).

fof(f9043,plain,
    ( spl7_1252
    | ~ spl7_424
    | ~ spl7_432
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8990,f8947,f2554,f2446,f9041])).

fof(f2554,plain,
    ( spl7_432
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_432])])).

fof(f8990,plain,
    ( k1_funct_1(k3_struct_0(sK5),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_424
    | ~ spl7_432
    | ~ spl7_1248 ),
    inference(forward_demodulation,[],[f8952,f2447])).

fof(f8952,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_432
    | ~ spl7_1248 ),
    inference(superposition,[],[f2555,f8948])).

fof(f2555,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_432 ),
    inference(avatar_component_clause,[],[f2554])).

fof(f9016,plain,
    ( spl7_1116
    | ~ spl7_82
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8954,f8947,f518,f7952])).

fof(f8954,plain,
    ( m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl7_82
    | ~ spl7_1248 ),
    inference(superposition,[],[f519,f8948])).

fof(f9015,plain,
    ( ~ spl7_1251
    | spl7_395
    | ~ spl7_1248 ),
    inference(avatar_split_clause,[],[f8953,f8947,f2313,f9013])).

fof(f9013,plain,
    ( spl7_1251
  <=> ~ m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1251])])).

fof(f8953,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK0))
    | ~ spl7_395
    | ~ spl7_1248 ),
    inference(superposition,[],[f2314,f8948])).

fof(f8949,plain,
    ( spl7_1248
    | ~ spl7_20
    | ~ spl7_396 ),
    inference(avatar_split_clause,[],[f8933,f2319,f223,f8947])).

fof(f8933,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_396 ),
    inference(forward_demodulation,[],[f8921,f224])).

fof(f8921,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k1_xboole_0
    | ~ spl7_396 ),
    inference(resolution,[],[f2320,f117])).

fof(f8913,plain,
    ( spl7_396
    | spl7_1246
    | ~ spl7_796 ),
    inference(avatar_split_clause,[],[f5097,f5090,f8911,f2319])).

fof(f8911,plain,
    ( spl7_1246
  <=> ! [X6] :
        ( v1_xboole_0(k7_relat_1(k3_struct_0(sK0),X6))
        | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k7_relat_1(k3_struct_0(sK0),X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1246])])).

fof(f5097,plain,
    ( ! [X6] :
        ( v1_xboole_0(k7_relat_1(k3_struct_0(sK0),X6))
        | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k7_relat_1(k3_struct_0(sK0),X6)) )
    | ~ spl7_796 ),
    inference(resolution,[],[f5091,f531])).

fof(f8909,plain,
    ( spl7_1244
    | ~ spl7_62
    | spl7_117
    | ~ spl7_1238 ),
    inference(avatar_split_clause,[],[f8880,f8862,f681,f438,f8907])).

fof(f8907,plain,
    ( spl7_1244
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1244])])).

fof(f8862,plain,
    ( spl7_1238
  <=> m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1238])])).

fof(f8880,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ spl7_62
    | ~ spl7_117
    | ~ spl7_1238 ),
    inference(forward_demodulation,[],[f8879,f439])).

fof(f8879,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ spl7_117
    | ~ spl7_1238 ),
    inference(subsumption_resolution,[],[f8867,f682])).

fof(f8867,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ spl7_1238 ),
    inference(resolution,[],[f8863,f601])).

fof(f8863,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl7_1238 ),
    inference(avatar_component_clause,[],[f8862])).

fof(f8902,plain,
    ( ~ spl7_1241
    | spl7_1242
    | spl7_117
    | ~ spl7_1238 ),
    inference(avatar_split_clause,[],[f8878,f8862,f681,f8900,f8894])).

fof(f8894,plain,
    ( spl7_1241
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1241])])).

fof(f8900,plain,
    ( spl7_1242
  <=> v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1242])])).

fof(f8878,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ spl7_117
    | ~ spl7_1238 ),
    inference(subsumption_resolution,[],[f8866,f682])).

fof(f8866,plain,
    ( v1_xboole_0(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))))
    | ~ spl7_1238 ),
    inference(resolution,[],[f8863,f531])).

fof(f8864,plain,
    ( spl7_1238
    | ~ spl7_738
    | ~ spl7_1236 ),
    inference(avatar_split_clause,[],[f8857,f8854,f4733,f8862])).

fof(f4733,plain,
    ( spl7_738
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_738])])).

fof(f8854,plain,
    ( spl7_1236
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1236])])).

fof(f8857,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl7_738
    | ~ spl7_1236 ),
    inference(superposition,[],[f4734,f8855])).

fof(f8855,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1)))
    | ~ spl7_1236 ),
    inference(avatar_component_clause,[],[f8854])).

fof(f4734,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl7_738 ),
    inference(avatar_component_clause,[],[f4733])).

fof(f8856,plain,
    ( spl7_1236
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_451 ),
    inference(avatar_split_clause,[],[f8771,f2709,f200,f165,f158,f151,f8854])).

fof(f8771,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451 ),
    inference(resolution,[],[f6178,f121])).

fof(f8846,plain,
    ( spl7_1234
    | ~ spl7_64
    | spl7_117
    | ~ spl7_744
    | ~ spl7_788
    | ~ spl7_1224
    | ~ spl7_1226 ),
    inference(avatar_split_clause,[],[f8810,f8790,f8780,f5040,f4758,f681,f447,f8844])).

fof(f8844,plain,
    ( spl7_1234
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1234])])).

fof(f4758,plain,
    ( spl7_744
  <=> k1_funct_1(k3_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_744])])).

fof(f8780,plain,
    ( spl7_1224
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1224])])).

fof(f8810,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_744
    | ~ spl7_788
    | ~ spl7_1224
    | ~ spl7_1226 ),
    inference(forward_demodulation,[],[f8809,f8783])).

fof(f8783,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_744
    | ~ spl7_1224 ),
    inference(superposition,[],[f4759,f8781])).

fof(f8781,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_1224 ),
    inference(avatar_component_clause,[],[f8780])).

fof(f4759,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_744 ),
    inference(avatar_component_clause,[],[f4758])).

fof(f8809,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_788
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8796,f682])).

fof(f8796,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1226 ),
    inference(resolution,[],[f8791,f5055])).

fof(f8838,plain,
    ( spl7_1232
    | ~ spl7_4
    | spl7_117
    | ~ spl7_744
    | ~ spl7_1224
    | ~ spl7_1226 ),
    inference(avatar_split_clause,[],[f8806,f8790,f8780,f4758,f681,f165,f8836])).

fof(f8836,plain,
    ( spl7_1232
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1232])])).

fof(f8806,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_4
    | ~ spl7_117
    | ~ spl7_744
    | ~ spl7_1224
    | ~ spl7_1226 ),
    inference(forward_demodulation,[],[f8805,f8783])).

fof(f8805,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_4
    | ~ spl7_117
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8804,f166])).

fof(f8804,plain,
    ( k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_117
    | ~ spl7_1226 ),
    inference(subsumption_resolution,[],[f8793,f682])).

fof(f8793,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1226 ),
    inference(resolution,[],[f8791,f3337])).

fof(f8831,plain,
    ( spl7_1230
    | ~ spl7_744
    | ~ spl7_1224 ),
    inference(avatar_split_clause,[],[f8783,f8780,f4758,f8829])).

fof(f8829,plain,
    ( spl7_1230
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k1_funct_1(k3_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1230])])).

fof(f8824,plain,
    ( ~ spl7_1229
    | spl7_741
    | ~ spl7_1224 ),
    inference(avatar_split_clause,[],[f8784,f8780,f4745,f8822])).

fof(f8822,plain,
    ( spl7_1229
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1229])])).

fof(f4745,plain,
    ( spl7_741
  <=> ~ m1_subset_1(u1_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_741])])).

fof(f8784,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_funct_1(k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_741
    | ~ spl7_1224 ),
    inference(superposition,[],[f4746,f8781])).

fof(f4746,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_741 ),
    inference(avatar_component_clause,[],[f4745])).

fof(f8792,plain,
    ( spl7_1226
    | ~ spl7_736
    | ~ spl7_1224 ),
    inference(avatar_split_clause,[],[f8785,f8780,f4721,f8790])).

fof(f4721,plain,
    ( spl7_736
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_736])])).

fof(f8785,plain,
    ( m1_subset_1(k1_funct_1(k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl7_736
    | ~ spl7_1224 ),
    inference(superposition,[],[f4722,f8781])).

fof(f4722,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl7_736 ),
    inference(avatar_component_clause,[],[f4721])).

fof(f8782,plain,
    ( spl7_1224
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_26
    | spl7_451 ),
    inference(avatar_split_clause,[],[f8770,f2709,f246,f200,f165,f158,f151,f8780])).

fof(f246,plain,
    ( spl7_26
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f8770,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_451 ),
    inference(resolution,[],[f6178,f247])).

fof(f247,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f246])).

fof(f8759,plain,
    ( spl7_1222
    | spl7_346
    | ~ spl7_8
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f3770,f368,f179,f1943,f8757])).

fof(f8757,plain,
    ( spl7_1222
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1222])])).

fof(f1943,plain,
    ( spl7_346
  <=> k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_346])])).

fof(f368,plain,
    ( spl7_50
  <=> k3_struct_0(sK5) = k6_partfun1(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f3770,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | o_0_0_xboole_0 = sK4(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl7_8
    | ~ spl7_50 ),
    inference(superposition,[],[f3740,f369])).

fof(f369,plain,
    ( k3_struct_0(sK5) = k6_partfun1(u1_struct_0(sK5))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f368])).

fof(f8752,plain,
    ( spl7_1220
    | spl7_1071
    | ~ spl7_1214 ),
    inference(avatar_split_clause,[],[f8727,f8721,f7527,f8750])).

fof(f8750,plain,
    ( spl7_1220
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1220])])).

fof(f8721,plain,
    ( spl7_1214
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1214])])).

fof(f8727,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1071
    | ~ spl7_1214 ),
    inference(subsumption_resolution,[],[f8725,f7528])).

fof(f8725,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1214 ),
    inference(resolution,[],[f8722,f1209])).

fof(f8722,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),X0) = X0 )
    | ~ spl7_1214 ),
    inference(avatar_component_clause,[],[f8721])).

fof(f8745,plain,
    ( spl7_1218
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f8016,f7511,f8743])).

fof(f8743,plain,
    ( spl7_1218
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1218])])).

fof(f8016,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) = sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_1067 ),
    inference(resolution,[],[f7512,f858])).

fof(f8738,plain,
    ( spl7_1216
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f7600,f7527,f8736])).

fof(f8736,plain,
    ( spl7_1216
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1216])])).

fof(f7600,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k3_struct_0(sK5)))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1071 ),
    inference(resolution,[],[f7528,f858])).

fof(f8723,plain,
    ( spl7_1078
    | spl7_1214
    | spl7_349
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f7438,f2446,f1947,f8721,f7637])).

fof(f7438,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),X0) = X0 )
    | ~ spl7_349
    | ~ spl7_424 ),
    inference(subsumption_resolution,[],[f7437,f1948])).

fof(f7437,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_struct_0(sK5))
        | ~ m1_subset_1(X0,k3_struct_0(sK5))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),X0) = X0 )
    | ~ spl7_424 ),
    inference(forward_demodulation,[],[f7430,f2447])).

fof(f7430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | v1_xboole_0(k6_partfun1(o_0_0_xboole_0))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),X0) = X0 )
    | ~ spl7_424 ),
    inference(superposition,[],[f1207,f2447])).

fof(f8718,plain,
    ( spl7_1212
    | spl7_164
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f7226,f732,f377,f186,f940,f8716])).

fof(f940,plain,
    ( spl7_164
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f7226,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_126 ),
    inference(resolution,[],[f5457,f733])).

fof(f8711,plain,
    ( spl7_1210
    | ~ spl7_80
    | ~ spl7_200
    | spl7_415
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8566,f5476,f2377,f1132,f511,f8709])).

fof(f8709,plain,
    ( spl7_1210
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1210])])).

fof(f8566,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_80
    | ~ spl7_200
    | ~ spl7_415
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f8532,f2378])).

fof(f8532,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_80
    | ~ spl7_200
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f1133])).

fof(f8704,plain,
    ( spl7_1208
    | ~ spl7_80
    | ~ spl7_524
    | spl7_535
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8560,f5476,f3395,f3319,f511,f8702])).

fof(f8702,plain,
    ( spl7_1208
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1208])])).

fof(f8560,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_524
    | ~ spl7_535
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f8520,f3396])).

fof(f8520,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_524
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f3320])).

fof(f8697,plain,
    ( spl7_1206
    | ~ spl7_80
    | spl7_417
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8628,f5476,f2383,f511,f8695])).

fof(f8695,plain,
    ( spl7_1206
  <=> k1_funct_1(k3_struct_0(sK6),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1206])])).

fof(f8628,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_80
    | ~ spl7_417
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f2384])).

fof(f8690,plain,
    ( spl7_1204
    | ~ spl7_80
    | spl7_311
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8614,f5476,f1734,f511,f8688])).

fof(f8688,plain,
    ( spl7_1204
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1204])])).

fof(f8614,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_80
    | ~ spl7_311
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1735])).

fof(f8683,plain,
    ( spl7_1202
    | ~ spl7_80
    | spl7_305
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8610,f5476,f1705,f511,f8681])).

fof(f8681,plain,
    ( spl7_1202
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1202])])).

fof(f8610,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_80
    | ~ spl7_305
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1706])).

fof(f8676,plain,
    ( spl7_1200
    | ~ spl7_80
    | spl7_485
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8630,f5476,f2881,f511,f8674])).

fof(f8674,plain,
    ( spl7_1200
  <=> k1_funct_1(k3_struct_0(sK6),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1200])])).

fof(f8630,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_80
    | ~ spl7_485
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f2882])).

fof(f8664,plain,
    ( spl7_1198
    | ~ spl7_80
    | spl7_195
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8613,f5476,f1102,f511,f8662])).

fof(f8662,plain,
    ( spl7_1198
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1198])])).

fof(f8613,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_80
    | ~ spl7_195
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1103])).

fof(f8657,plain,
    ( spl7_1196
    | ~ spl7_80
    | spl7_181
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8612,f5476,f1019,f511,f8655])).

fof(f8655,plain,
    ( spl7_1196
  <=> k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1196])])).

fof(f8612,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_80
    | ~ spl7_181
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f1020])).

fof(f8650,plain,
    ( spl7_1194
    | ~ spl7_80
    | spl7_451
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8609,f5476,f2709,f511,f8648])).

fof(f8648,plain,
    ( spl7_1194
  <=> k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1194])])).

fof(f8609,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_80
    | ~ spl7_451
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f2710])).

fof(f8643,plain,
    ( spl7_1192
    | ~ spl7_80
    | spl7_117
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8608,f5476,f681,f511,f8641])).

fof(f8641,plain,
    ( spl7_1192
  <=> k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1192])])).

fof(f8608,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_80
    | ~ spl7_117
    | ~ spl7_832 ),
    inference(resolution,[],[f8527,f682])).

fof(f8594,plain,
    ( spl7_1190
    | ~ spl7_80
    | ~ spl7_126
    | spl7_165
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8561,f5476,f937,f732,f511,f8592])).

fof(f8592,plain,
    ( spl7_1190
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1190])])).

fof(f8561,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_126
    | ~ spl7_165
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f8521,f938])).

fof(f8521,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_126
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f733])).

fof(f8587,plain,
    ( spl7_1188
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1100
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8562,f7903,f7880,f5476,f511,f8585])).

fof(f8585,plain,
    ( spl7_1188
  <=> k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1188])])).

fof(f8562,plain,
    ( k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1100
    | ~ spl7_1105 ),
    inference(subsumption_resolution,[],[f8522,f7904])).

fof(f8522,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK6),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_80
    | ~ spl7_832
    | ~ spl7_1100 ),
    inference(resolution,[],[f5500,f7881])).

fof(f8580,plain,
    ( spl7_1186
    | ~ spl7_16
    | ~ spl7_80
    | spl7_117
    | ~ spl7_832 ),
    inference(avatar_split_clause,[],[f8564,f5476,f681,f511,f207,f8578])).

fof(f8578,plain,
    ( spl7_1186
  <=> k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1186])])).

fof(f8564,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_80
    | ~ spl7_117
    | ~ spl7_832 ),
    inference(subsumption_resolution,[],[f8525,f682])).

fof(f8525,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_80
    | ~ spl7_832 ),
    inference(resolution,[],[f5500,f208])).

fof(f8462,plain,
    ( ~ spl7_38
    | spl7_1185 ),
    inference(avatar_contradiction_clause,[],[f8461])).

fof(f8461,plain,
    ( $false
    | ~ spl7_38
    | ~ spl7_1185 ),
    inference(subsumption_resolution,[],[f8460,f307])).

fof(f307,plain,
    ( l1_pre_topc(sK3(sK6))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl7_38
  <=> l1_pre_topc(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f8460,plain,
    ( ~ l1_pre_topc(sK3(sK6))
    | ~ spl7_1185 ),
    inference(resolution,[],[f8458,f114])).

fof(f8458,plain,
    ( ~ l1_struct_0(sK3(sK6))
    | ~ spl7_1185 ),
    inference(avatar_component_clause,[],[f8457])).

fof(f8457,plain,
    ( spl7_1185
  <=> ~ l1_struct_0(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1185])])).

fof(f8459,plain,
    ( ~ spl7_1185
    | spl7_1181 ),
    inference(avatar_split_clause,[],[f8452,f8446,f8457])).

fof(f8446,plain,
    ( spl7_1181
  <=> ~ v1_funct_1(k3_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1181])])).

fof(f8452,plain,
    ( ~ l1_struct_0(sK3(sK6))
    | ~ spl7_1181 ),
    inference(resolution,[],[f8447,f110])).

fof(f8447,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3(sK6)))
    | ~ spl7_1181 ),
    inference(avatar_component_clause,[],[f8446])).

fof(f8451,plain,
    ( ~ spl7_1181
    | spl7_1182
    | ~ spl7_38
    | ~ spl7_224 ),
    inference(avatar_split_clause,[],[f8441,f1300,f306,f8449,f8446])).

fof(f8449,plain,
    ( spl7_1182
  <=> ! [X4] : v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1182])])).

fof(f8441,plain,
    ( ! [X4] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),X4))
        | ~ v1_funct_1(k3_struct_0(sK3(sK6))) )
    | ~ spl7_38
    | ~ spl7_224 ),
    inference(subsumption_resolution,[],[f8435,f1301])).

fof(f8435,plain,
    ( ! [X4] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),X4))
        | ~ m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK6))) )
    | ~ spl7_38 ),
    inference(superposition,[],[f141,f5026])).

fof(f5026,plain,
    ( ! [X55] : k2_partfun1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)),k3_struct_0(sK3(sK6)),X55) = k7_relat_1(k3_struct_0(sK3(sK6)),X55)
    | ~ spl7_38 ),
    inference(resolution,[],[f4970,f307])).

fof(f8423,plain,
    ( spl7_1178
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_200
    | spl7_415 ),
    inference(avatar_split_clause,[],[f7259,f2377,f1132,f377,f186,f8421])).

fof(f8421,plain,
    ( spl7_1178
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1178])])).

fof(f7259,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_200
    | ~ spl7_415 ),
    inference(subsumption_resolution,[],[f7236,f2378])).

fof(f7236,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_200 ),
    inference(resolution,[],[f5457,f1133])).

fof(f8416,plain,
    ( spl7_1176
    | spl7_349
    | spl7_1071 ),
    inference(avatar_split_clause,[],[f7608,f7527,f1947,f8414])).

fof(f8414,plain,
    ( spl7_1176
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1176])])).

fof(f7608,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_349
    | ~ spl7_1071 ),
    inference(subsumption_resolution,[],[f7598,f1948])).

fof(f7598,plain,
    ( v1_xboole_0(k3_struct_0(sK5))
    | k1_funct_1(k6_partfun1(k3_struct_0(sK5)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1071 ),
    inference(resolution,[],[f7528,f1211])).

fof(f8409,plain,
    ( spl7_1174
    | ~ spl7_68
    | ~ spl7_792
    | spl7_1079 ),
    inference(avatar_split_clause,[],[f8386,f7634,f5067,f463,f8407])).

fof(f8407,plain,
    ( spl7_1174
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1174])])).

fof(f8386,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1079 ),
    inference(resolution,[],[f7635,f5386])).

fof(f8402,plain,
    ( spl7_1108
    | spl7_1079 ),
    inference(avatar_split_clause,[],[f8384,f7634,f7920])).

fof(f7920,plain,
    ( spl7_1108
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1108])])).

fof(f8384,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1079 ),
    inference(resolution,[],[f7635,f858])).

fof(f8401,plain,
    ( spl7_1172
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_124
    | spl7_165
    | ~ spl7_850 ),
    inference(avatar_split_clause,[],[f8293,f5626,f937,f717,f377,f186,f8399])).

fof(f8399,plain,
    ( spl7_1172
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1172])])).

fof(f8293,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_124
    | ~ spl7_165
    | ~ spl7_850 ),
    inference(forward_demodulation,[],[f8292,f5627])).

fof(f8380,plain,
    ( spl7_349
    | ~ spl7_424
    | spl7_1065
    | spl7_1071
    | ~ spl7_1164 ),
    inference(avatar_contradiction_clause,[],[f8379])).

fof(f8379,plain,
    ( $false
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1065
    | ~ spl7_1071
    | ~ spl7_1164 ),
    inference(subsumption_resolution,[],[f8376,f7528])).

fof(f8376,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1065
    | ~ spl7_1164 ),
    inference(resolution,[],[f8338,f1209])).

fof(f8338,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k3_struct_0(sK5))
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1065
    | ~ spl7_1164 ),
    inference(subsumption_resolution,[],[f8337,f7499])).

fof(f7499,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)) != sK4(o_0_0_xboole_0)
    | ~ spl7_1065 ),
    inference(avatar_component_clause,[],[f7498])).

fof(f7498,plain,
    ( spl7_1065
  <=> k1_funct_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)) != sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1065])])).

fof(f8337,plain,
    ( ! [X1] :
        ( k1_funct_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0)
        | ~ m1_subset_1(X1,k3_struct_0(sK5)) )
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1164 ),
    inference(forward_demodulation,[],[f8336,f2447])).

fof(f8336,plain,
    ( ! [X1] :
        ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0)
        | ~ m1_subset_1(X1,k3_struct_0(sK5)) )
    | ~ spl7_349
    | ~ spl7_1164 ),
    inference(subsumption_resolution,[],[f8324,f1948])).

fof(f8324,plain,
    ( ! [X1] :
        ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0)
        | v1_xboole_0(k3_struct_0(sK5))
        | ~ m1_subset_1(X1,k3_struct_0(sK5)) )
    | ~ spl7_1164 ),
    inference(resolution,[],[f8321,f1929])).

fof(f8321,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_1164 ),
    inference(avatar_component_clause,[],[f8320])).

fof(f8320,plain,
    ( spl7_1164
  <=> m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1164])])).

fof(f8378,plain,
    ( spl7_349
    | ~ spl7_424
    | spl7_1065
    | ~ spl7_1164 ),
    inference(avatar_contradiction_clause,[],[f8375])).

fof(f8375,plain,
    ( $false
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1065
    | ~ spl7_1164 ),
    inference(resolution,[],[f8338,f121])).

fof(f8374,plain,
    ( ~ spl7_1171
    | spl7_1077
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8229,f8198,f7631,f8372])).

fof(f8372,plain,
    ( spl7_1171
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1171])])).

fof(f7631,plain,
    ( spl7_1077
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1077])])).

fof(f8198,plain,
    ( spl7_1156
  <=> k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1156])])).

fof(f8229,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK5)))
    | ~ spl7_1077
    | ~ spl7_1156 ),
    inference(superposition,[],[f7632,f8199])).

fof(f8199,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1156 ),
    inference(avatar_component_clause,[],[f8198])).

fof(f7632,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k3_struct_0(sK5)))
    | ~ spl7_1077 ),
    inference(avatar_component_clause,[],[f7631])).

fof(f8367,plain,
    ( ~ spl7_1169
    | spl7_1069
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8227,f8198,f7520,f8365])).

fof(f8365,plain,
    ( spl7_1169
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1169])])).

fof(f7520,plain,
    ( spl7_1069
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1069])])).

fof(f8227,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k3_struct_0(sK5))
    | ~ spl7_1069
    | ~ spl7_1156 ),
    inference(superposition,[],[f7521,f8199])).

fof(f7521,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k3_struct_0(sK5))
    | ~ spl7_1069 ),
    inference(avatar_component_clause,[],[f7520])).

fof(f8351,plain,
    ( spl7_1166
    | ~ spl7_1060
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8225,f8198,f7461,f8349])).

fof(f8225,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),o_0_0_xboole_0)
    | ~ spl7_1060
    | ~ spl7_1156 ),
    inference(superposition,[],[f7462,f8199])).

fof(f8322,plain,
    ( spl7_1164
    | ~ spl7_852
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8223,f8198,f5633,f8320])).

fof(f8223,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_852
    | ~ spl7_1156 ),
    inference(superposition,[],[f5634,f8199])).

fof(f8315,plain,
    ( ~ spl7_1163
    | spl7_1123
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8233,f8198,f7972,f8313])).

fof(f8313,plain,
    ( spl7_1163
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1163])])).

fof(f7972,plain,
    ( spl7_1123
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1123])])).

fof(f8233,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_1123
    | ~ spl7_1156 ),
    inference(superposition,[],[f7973,f8199])).

fof(f7973,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_1123 ),
    inference(avatar_component_clause,[],[f7972])).

fof(f8300,plain,
    ( ~ spl7_1161
    | spl7_1093
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8232,f8198,f7771,f8298])).

fof(f8298,plain,
    ( spl7_1161
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1161])])).

fof(f7771,plain,
    ( spl7_1093
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1093])])).

fof(f8232,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_1093
    | ~ spl7_1156 ),
    inference(superposition,[],[f7772,f8199])).

fof(f7772,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1093 ),
    inference(avatar_component_clause,[],[f7771])).

fof(f8276,plain,
    ( ~ spl7_165
    | spl7_1067
    | ~ spl7_1156 ),
    inference(avatar_split_clause,[],[f8226,f8198,f7511,f937])).

fof(f8226,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_1067
    | ~ spl7_1156 ),
    inference(superposition,[],[f7512,f8199])).

fof(f8219,plain,
    ( spl7_1158
    | ~ spl7_64
    | ~ spl7_788
    | spl7_1079 ),
    inference(avatar_split_clause,[],[f8203,f7634,f5040,f447,f8217])).

fof(f8217,plain,
    ( spl7_1158
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1158])])).

fof(f8203,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1079 ),
    inference(resolution,[],[f7635,f5246])).

fof(f8200,plain,
    ( spl7_1156
    | ~ spl7_20
    | ~ spl7_1078 ),
    inference(avatar_split_clause,[],[f8183,f7637,f223,f8198])).

fof(f8183,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1078 ),
    inference(forward_demodulation,[],[f8171,f224])).

fof(f8171,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = k1_xboole_0
    | ~ spl7_1078 ),
    inference(resolution,[],[f7638,f117])).

fof(f7638,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1078 ),
    inference(avatar_component_clause,[],[f7637])).

fof(f8170,plain,
    ( spl7_1154
    | spl7_1078
    | ~ spl7_1060 ),
    inference(avatar_split_clause,[],[f7465,f7461,f7637,f8168])).

fof(f8168,plain,
    ( spl7_1154
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5))) = sK4(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1154])])).

fof(f7465,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k3_struct_0(sK5))) = sK4(k3_struct_0(sK5))
    | ~ spl7_1060 ),
    inference(resolution,[],[f7462,f601])).

fof(f8162,plain,
    ( spl7_1152
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_524
    | spl7_535 ),
    inference(avatar_split_clause,[],[f7253,f3395,f3319,f377,f186,f8160])).

fof(f8160,plain,
    ( spl7_1152
  <=> k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1152])])).

fof(f7253,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_524
    | ~ spl7_535 ),
    inference(subsumption_resolution,[],[f7225,f3396])).

fof(f7225,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_524 ),
    inference(resolution,[],[f5457,f3320])).

fof(f8155,plain,
    ( spl7_1140
    | spl7_1104
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7891,f7880,f5169,f495,f7906,f8112])).

fof(f7891,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f5193])).

fof(f8154,plain,
    ( spl7_1138
    | spl7_1104
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7890,f7880,f5132,f479,f7906,f8105])).

fof(f7890,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f5159])).

fof(f8153,plain,
    ( spl7_1106
    | spl7_1136
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7861,f7836,f5067,f463,f223,f8098,f7913])).

fof(f8098,plain,
    ( spl7_1136
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1136])])).

fof(f7861,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1096 ),
    inference(superposition,[],[f5445,f7837])).

fof(f8152,plain,
    ( spl7_1106
    | spl7_1134
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7860,f7836,f5040,f447,f223,f8091,f7913])).

fof(f8091,plain,
    ( spl7_1134
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1134])])).

fof(f7860,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1096 ),
    inference(superposition,[],[f5328,f7837])).

fof(f8151,plain,
    ( spl7_1150
    | spl7_1102
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7857,f7836,f7900,f8149])).

fof(f8149,plain,
    ( spl7_1150
  <=> ! [X6] :
        ( k1_zfmisc_1(sK4(o_0_0_xboole_0)) = X6
        | k1_funct_1(k6_partfun1(X6),sK4(X6)) = sK4(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1150])])).

fof(f7900,plain,
    ( spl7_1102
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1102])])).

fof(f7857,plain,
    ( ! [X6] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
        | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = X6
        | k1_funct_1(k6_partfun1(X6),sK4(X6)) = sK4(X6) )
    | ~ spl7_1096 ),
    inference(superposition,[],[f1295,f7837])).

fof(f8147,plain,
    ( spl7_1148
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8084,f7903,f7836,f6299,f575,f8145])).

fof(f8084,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8076,f7837])).

fof(f8076,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_94
    | ~ spl7_956
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f6667])).

fof(f8140,plain,
    ( spl7_1146
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8083,f7903,f7836,f6261,f556,f8138])).

fof(f8083,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8075,f7837])).

fof(f8075,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_90
    | ~ spl7_950
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f6386])).

fof(f8133,plain,
    ( spl7_1136
    | spl7_1104
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7889,f7880,f5067,f463,f7906,f8098])).

fof(f7889,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f5082])).

fof(f8132,plain,
    ( spl7_1134
    | spl7_1104
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7888,f7880,f5040,f447,f7906,f8091])).

fof(f7888,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f5055])).

fof(f8128,plain,
    ( spl7_1144
    | ~ spl7_64
    | ~ spl7_424
    | ~ spl7_788
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f8025,f7511,f5040,f2446,f447,f8126])).

fof(f8025,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_64
    | ~ spl7_424
    | ~ spl7_788
    | ~ spl7_1067 ),
    inference(forward_demodulation,[],[f8014,f2447])).

fof(f8014,plain,
    ( k1_funct_1(k3_struct_0(sK0),k6_partfun1(o_0_0_xboole_0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1067 ),
    inference(resolution,[],[f7512,f5227])).

fof(f8121,plain,
    ( spl7_1142
    | ~ spl7_68
    | ~ spl7_424
    | ~ spl7_792
    | spl7_1067 ),
    inference(avatar_split_clause,[],[f8024,f7511,f5067,f2446,f463,f8119])).

fof(f8024,plain,
    ( k1_funct_1(k3_struct_0(sK1),k3_struct_0(sK5)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5))
    | ~ spl7_68
    | ~ spl7_424
    | ~ spl7_792
    | ~ spl7_1067 ),
    inference(forward_demodulation,[],[f8013,f2447])).

fof(f8013,plain,
    ( k1_funct_1(k3_struct_0(sK1),k6_partfun1(o_0_0_xboole_0)) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1067 ),
    inference(resolution,[],[f7512,f5367])).

fof(f8114,plain,
    ( spl7_1140
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8082,f7903,f7836,f5169,f495,f8112])).

fof(f8082,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8074,f7837])).

fof(f8074,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_76
    | ~ spl7_814
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f5949])).

fof(f8107,plain,
    ( spl7_1138
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8081,f7903,f7836,f5132,f479,f8105])).

fof(f8081,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8073,f7837])).

fof(f8073,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_72
    | ~ spl7_808
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f5807])).

fof(f8100,plain,
    ( spl7_1136
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8080,f7903,f7836,f5067,f463,f8098])).

fof(f8080,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8072,f7837])).

fof(f8072,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_68
    | ~ spl7_792
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f5386])).

fof(f8093,plain,
    ( spl7_1134
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1096
    | spl7_1105 ),
    inference(avatar_split_clause,[],[f8079,f7903,f7836,f5040,f447,f8091])).

fof(f8079,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1096
    | ~ spl7_1105 ),
    inference(forward_demodulation,[],[f8071,f7837])).

fof(f8071,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))),sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_64
    | ~ spl7_788
    | ~ spl7_1105 ),
    inference(resolution,[],[f7904,f5246])).

fof(f8069,plain,
    ( spl7_1106
    | ~ spl7_20
    | ~ spl7_1104 ),
    inference(avatar_split_clause,[],[f8058,f7906,f223,f7913])).

fof(f8058,plain,
    ( k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1104 ),
    inference(forward_demodulation,[],[f8046,f224])).

fof(f8046,plain,
    ( k1_zfmisc_1(sK4(o_0_0_xboole_0)) = k1_xboole_0
    | ~ spl7_1104 ),
    inference(resolution,[],[f7907,f117])).

fof(f7907,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_1104 ),
    inference(avatar_component_clause,[],[f7906])).

fof(f8045,plain,
    ( spl7_1104
    | spl7_1132
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_850
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7895,f7880,f5626,f377,f186,f8043,f7906])).

fof(f7895,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_850
    | ~ spl7_1100 ),
    inference(forward_demodulation,[],[f7892,f5627])).

fof(f8038,plain,
    ( ~ spl7_1131
    | spl7_349
    | ~ spl7_424
    | spl7_1093 ),
    inference(avatar_split_clause,[],[f8031,f7771,f2446,f1947,f8036])).

fof(f8036,plain,
    ( spl7_1131
  <=> ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1131])])).

fof(f8031,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k3_struct_0(sK5))
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1093 ),
    inference(forward_demodulation,[],[f8030,f2447])).

fof(f8030,plain,
    ( ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_349
    | ~ spl7_424
    | ~ spl7_1093 ),
    inference(subsumption_resolution,[],[f8029,f1948])).

fof(f8029,plain,
    ( v1_xboole_0(k3_struct_0(sK5))
    | ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_424
    | ~ spl7_1093 ),
    inference(forward_demodulation,[],[f8028,f2447])).

fof(f8028,plain,
    ( v1_xboole_0(k6_partfun1(o_0_0_xboole_0))
    | ~ m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_1093 ),
    inference(resolution,[],[f7772,f1015])).

fof(f8027,plain,
    ( spl7_1128
    | spl7_1078
    | ~ spl7_1092 ),
    inference(avatar_split_clause,[],[f7778,f7774,f7637,f8010])).

fof(f8010,plain,
    ( spl7_1128
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1128])])).

fof(f7778,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_1092 ),
    inference(resolution,[],[f7775,f601])).

fof(f8012,plain,
    ( spl7_1078
    | spl7_1128
    | spl7_485
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7744,f7696,f2881,f8010,f7637])).

fof(f7744,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7743,f7697])).

fof(f7743,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))) = sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(subsumption_resolution,[],[f7723,f2882])).

fof(f7723,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))) = sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_1088 ),
    inference(superposition,[],[f1211,f7697])).

fof(f7987,plain,
    ( spl7_1126
    | spl7_1102
    | ~ spl7_8
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7859,f7836,f179,f7900,f7985])).

fof(f7985,plain,
    ( spl7_1126
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1126])])).

fof(f7859,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_8
    | ~ spl7_1096 ),
    inference(superposition,[],[f3740,f7837])).

fof(f7980,plain,
    ( spl7_1078
    | ~ spl7_1123
    | spl7_1124
    | spl7_485
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7747,f7696,f2881,f7978,f7972,f7637])).

fof(f7747,plain,
    ( v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(subsumption_resolution,[],[f7746,f2882])).

fof(f7746,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7745,f7697])).

fof(f7745,plain,
    ( v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7724,f7697])).

fof(f7724,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | v1_xboole_0(sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_1088 ),
    inference(superposition,[],[f1212,f7697])).

fof(f7967,plain,
    ( spl7_1118
    | ~ spl7_1121
    | ~ spl7_792
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7714,f7696,f5067,f7965,f7959])).

fof(f7959,plain,
    ( spl7_1118
  <=> ! [X8] : k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK1),X8) = k7_relat_1(k3_struct_0(sK1),X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1118])])).

fof(f7965,plain,
    ( spl7_1121
  <=> ~ m1_subset_1(k3_struct_0(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1121])])).

fof(f7714,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k3_struct_0(sK1),o_0_0_xboole_0)
        | k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK1),X8) = k7_relat_1(k3_struct_0(sK1),X8) )
    | ~ spl7_792
    | ~ spl7_1088 ),
    inference(superposition,[],[f5080,f7697])).

fof(f5080,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_partfun1(X8,X9,k3_struct_0(sK1),X10) = k7_relat_1(k3_struct_0(sK1),X10) )
    | ~ spl7_792 ),
    inference(resolution,[],[f5068,f140])).

fof(f7957,plain,
    ( spl7_1114
    | ~ spl7_1117
    | ~ spl7_788
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7713,f7696,f5040,f7955,f7949])).

fof(f7713,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(k3_struct_0(sK0),o_0_0_xboole_0)
        | k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK0),X7) = k7_relat_1(k3_struct_0(sK0),X7) )
    | ~ spl7_788
    | ~ spl7_1088 ),
    inference(superposition,[],[f5053,f7697])).

fof(f7947,plain,
    ( ~ spl7_1111
    | spl7_1112
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7927,f7696,f7945,f7942])).

fof(f7942,plain,
    ( spl7_1111
  <=> ~ v1_funct_1(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1111])])).

fof(f7945,plain,
    ( spl7_1112
  <=> ! [X5] : m1_subset_1(k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK4(o_0_0_xboole_0),X5),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1112])])).

fof(f7927,plain,
    ( ! [X5] :
        ( m1_subset_1(k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK4(o_0_0_xboole_0),X5),o_0_0_xboole_0)
        | ~ v1_funct_1(sK4(o_0_0_xboole_0)) )
    | ~ spl7_1088 ),
    inference(resolution,[],[f7738,f121])).

fof(f7738,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,o_0_0_xboole_0)
        | m1_subset_1(k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,X2,X3),o_0_0_xboole_0)
        | ~ v1_funct_1(X2) )
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7710,f7697])).

fof(f7710,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k2_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,X2,X3),o_0_0_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
        | ~ v1_funct_1(X2) )
    | ~ spl7_1088 ),
    inference(superposition,[],[f142,f7697])).

fof(f7922,plain,
    ( spl7_1108
    | spl7_485
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7751,f7696,f2881,f7920])).

fof(f7751,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(subsumption_resolution,[],[f7730,f2882])).

fof(f7730,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) = sK4(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1088 ),
    inference(superposition,[],[f3732,f7697])).

fof(f7915,plain,
    ( spl7_1106
    | spl7_1102
    | ~ spl7_8
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7856,f7836,f179,f7900,f7913])).

fof(f7856,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | k1_zfmisc_1(sK4(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_1096 ),
    inference(superposition,[],[f889,f7837])).

fof(f7908,plain,
    ( spl7_1102
    | spl7_1104
    | ~ spl7_1100 ),
    inference(avatar_split_clause,[],[f7887,f7880,f7906,f7900])).

fof(f7887,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(sK4(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_1100 ),
    inference(resolution,[],[f7881,f601])).

fof(f7882,plain,
    ( spl7_1100
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7854,f7836,f7880])).

fof(f7854,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_1096 ),
    inference(superposition,[],[f121,f7837])).

fof(f7875,plain,
    ( ~ spl7_1099
    | spl7_189
    | ~ spl7_1096 ),
    inference(avatar_split_clause,[],[f7868,f7836,f1061,f7873])).

fof(f7873,plain,
    ( spl7_1099
  <=> ~ v1_relat_1(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1099])])).

fof(f7868,plain,
    ( ~ v1_relat_1(sK4(o_0_0_xboole_0))
    | ~ spl7_189
    | ~ spl7_1096 ),
    inference(subsumption_resolution,[],[f7842,f1062])).

fof(f7842,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(sK4(o_0_0_xboole_0))
    | ~ spl7_1096 ),
    inference(superposition,[],[f400,f7837])).

fof(f7867,plain,
    ( spl7_667
    | ~ spl7_1096 ),
    inference(avatar_contradiction_clause,[],[f7866])).

fof(f7866,plain,
    ( $false
    | ~ spl7_667
    | ~ spl7_1096 ),
    inference(subsumption_resolution,[],[f7841,f121])).

fof(f7841,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl7_667
    | ~ spl7_1096 ),
    inference(superposition,[],[f4196,f7837])).

fof(f4196,plain,
    ( ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),o_0_0_xboole_0)
    | ~ spl7_667 ),
    inference(avatar_component_clause,[],[f4195])).

fof(f4195,plain,
    ( spl7_667
  <=> ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_667])])).

fof(f7838,plain,
    ( spl7_1096
    | ~ spl7_20
    | ~ spl7_542 ),
    inference(avatar_split_clause,[],[f7821,f3428,f223,f7836])).

fof(f3428,plain,
    ( spl7_542
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_542])])).

fof(f7821,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_20
    | ~ spl7_542 ),
    inference(forward_demodulation,[],[f7809,f224])).

fof(f7809,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl7_542 ),
    inference(resolution,[],[f3429,f117])).

fof(f3429,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_542 ),
    inference(avatar_component_clause,[],[f3428])).

fof(f7808,plain,
    ( spl7_1094
    | spl7_542
    | spl7_485
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7750,f7696,f2881,f3428,f7806])).

fof(f7806,plain,
    ( spl7_1094
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1094])])).

fof(f7750,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7749,f7697])).

fof(f7749,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(subsumption_resolution,[],[f7748,f2882])).

fof(f7748,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))))
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7726,f7697])).

fof(f7726,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))))
    | ~ spl7_1088 ),
    inference(superposition,[],[f1218,f7697])).

fof(f7776,plain,
    ( spl7_1092
    | spl7_485
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7742,f7696,f2881,f7774])).

fof(f7742,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_1088 ),
    inference(subsumption_resolution,[],[f7741,f2882])).

fof(f7741,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_1088 ),
    inference(forward_demodulation,[],[f7722,f7697])).

fof(f7722,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl7_1088 ),
    inference(superposition,[],[f1209,f7697])).

fof(f7760,plain,
    ( spl7_494
    | ~ spl7_852
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7702,f7696,f5633,f3127])).

fof(f7702,plain,
    ( m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0)
    | ~ spl7_852
    | ~ spl7_1088 ),
    inference(superposition,[],[f5634,f7697])).

fof(f7759,plain,
    ( ~ spl7_1091
    | spl7_1069
    | ~ spl7_1088 ),
    inference(avatar_split_clause,[],[f7700,f7696,f7520,f7757])).

fof(f7757,plain,
    ( spl7_1091
  <=> ~ m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1091])])).

fof(f7700,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k3_struct_0(sK5))
    | ~ spl7_1069
    | ~ spl7_1088 ),
    inference(superposition,[],[f7521,f7697])).

fof(f7698,plain,
    ( spl7_1088
    | ~ spl7_20
    | ~ spl7_1066 ),
    inference(avatar_split_clause,[],[f7681,f7514,f223,f7696])).

fof(f7681,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_1066 ),
    inference(forward_demodulation,[],[f7669,f224])).

fof(f7669,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = k1_xboole_0
    | ~ spl7_1066 ),
    inference(resolution,[],[f7515,f117])).

fof(f7515,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_1066 ),
    inference(avatar_component_clause,[],[f7514])).

fof(f7668,plain,
    ( spl7_1086
    | spl7_1066
    | ~ spl7_852 ),
    inference(avatar_split_clause,[],[f7445,f5633,f7514,f7666])).

fof(f7445,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k3_struct_0(sK5)) = k3_struct_0(sK5)
    | ~ spl7_852 ),
    inference(resolution,[],[f5634,f601])).

fof(f7661,plain,
    ( spl7_1082
    | ~ spl7_1085
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f7648,f2428,f165,f158,f151,f7659,f7653])).

fof(f7653,plain,
    ( spl7_1082
  <=> v1_funct_2(k4_tmap_1(sK0,sK5),o_0_0_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1082])])).

fof(f7659,plain,
    ( spl7_1085
  <=> ~ m1_pre_topc(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1085])])).

fof(f7648,plain,
    ( ~ m1_pre_topc(sK5,sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK5),o_0_0_xboole_0,u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_422 ),
    inference(subsumption_resolution,[],[f7647,f152])).

fof(f7647,plain,
    ( ~ m1_pre_topc(sK5,sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK5),o_0_0_xboole_0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_422 ),
    inference(subsumption_resolution,[],[f7646,f166])).

fof(f7646,plain,
    ( ~ m1_pre_topc(sK5,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_2(k4_tmap_1(sK0,sK5),o_0_0_xboole_0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_422 ),
    inference(resolution,[],[f7416,f159])).

fof(f7416,plain,
    ( ! [X8] :
        ( ~ v2_pre_topc(X8)
        | ~ m1_pre_topc(sK5,X8)
        | ~ l1_pre_topc(X8)
        | v1_funct_2(k4_tmap_1(X8,sK5),o_0_0_xboole_0,u1_struct_0(X8))
        | v2_struct_0(X8) )
    | ~ spl7_422 ),
    inference(superposition,[],[f128,f2429])).

fof(f7645,plain,
    ( ~ spl7_1077
    | spl7_1078
    | spl7_1080
    | ~ spl7_1060 ),
    inference(avatar_split_clause,[],[f7464,f7461,f7643,f7637,f7631])).

fof(f7464,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK5)))
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k3_struct_0(sK5)))
    | ~ spl7_1060 ),
    inference(resolution,[],[f7462,f531])).

fof(f7597,plain,
    ( ~ spl7_52
    | spl7_189
    | ~ spl7_1074 ),
    inference(avatar_contradiction_clause,[],[f7596])).

fof(f7596,plain,
    ( $false
    | ~ spl7_52
    | ~ spl7_189
    | ~ spl7_1074 ),
    inference(subsumption_resolution,[],[f7595,f378])).

fof(f7595,plain,
    ( ~ v1_relat_1(k3_struct_0(sK5))
    | ~ spl7_189
    | ~ spl7_1074 ),
    inference(subsumption_resolution,[],[f7571,f1062])).

fof(f7571,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(k3_struct_0(sK5))
    | ~ spl7_1074 ),
    inference(superposition,[],[f400,f7567])).

fof(f7567,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK5)))
    | ~ spl7_1074 ),
    inference(avatar_component_clause,[],[f7566])).

fof(f7566,plain,
    ( spl7_1074
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1074])])).

fof(f7568,plain,
    ( spl7_1074
    | ~ spl7_20
    | ~ spl7_1070 ),
    inference(avatar_split_clause,[],[f7551,f7530,f223,f7566])).

fof(f7530,plain,
    ( spl7_1070
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1070])])).

fof(f7551,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK5)))
    | ~ spl7_20
    | ~ spl7_1070 ),
    inference(forward_demodulation,[],[f7539,f224])).

fof(f7539,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k3_struct_0(sK5)))
    | ~ spl7_1070 ),
    inference(resolution,[],[f7531,f117])).

fof(f7531,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_1070 ),
    inference(avatar_component_clause,[],[f7530])).

fof(f7538,plain,
    ( spl7_1070
    | spl7_1072
    | ~ spl7_350
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f7455,f2428,f1953,f7536,f7530])).

fof(f7536,plain,
    ( spl7_1072
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1072])])).

fof(f7455,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK5)))),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK5))))
    | ~ spl7_350
    | ~ spl7_422 ),
    inference(resolution,[],[f2431,f1209])).

fof(f2431,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK5))
        | m1_subset_1(X0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) )
    | ~ spl7_350
    | ~ spl7_422 ),
    inference(superposition,[],[f1954,f2429])).

fof(f7522,plain,
    ( spl7_1066
    | ~ spl7_1069
    | spl7_349
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f7436,f2446,f1947,f7520,f7514])).

fof(f7436,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k3_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_349
    | ~ spl7_424 ),
    inference(subsumption_resolution,[],[f7435,f1948])).

fof(f7435,plain,
    ( v1_xboole_0(k3_struct_0(sK5))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k3_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_424 ),
    inference(forward_demodulation,[],[f7428,f2447])).

fof(f7428,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k3_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | v1_xboole_0(k6_partfun1(o_0_0_xboole_0))
    | ~ spl7_424 ),
    inference(superposition,[],[f670,f2447])).

fof(f670,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(X0,X0)),k6_partfun1(X0))
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_xboole_0(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f531,f108])).

fof(f7501,plain,
    ( ~ spl7_1063
    | ~ spl7_422
    | spl7_907 ),
    inference(avatar_split_clause,[],[f7492,f6089,f2428,f7486])).

fof(f7486,plain,
    ( spl7_1063
  <=> k3_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK5),sK4(o_0_0_xboole_0)) != sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1063])])).

fof(f6089,plain,
    ( spl7_907
  <=> k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5))) != sK4(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_907])])).

fof(f7492,plain,
    ( k3_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK5),sK4(o_0_0_xboole_0)) != sK4(o_0_0_xboole_0)
    | ~ spl7_422
    | ~ spl7_907 ),
    inference(forward_demodulation,[],[f6090,f2429])).

fof(f6090,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5))) != sK4(u1_struct_0(sK5))
    | ~ spl7_907 ),
    inference(avatar_component_clause,[],[f6089])).

fof(f7500,plain,
    ( ~ spl7_1065
    | spl7_347
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f7493,f2428,f1940,f7498])).

fof(f1940,plain,
    ( spl7_347
  <=> k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) != sK4(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_347])])).

fof(f7493,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)) != sK4(o_0_0_xboole_0)
    | ~ spl7_347
    | ~ spl7_422 ),
    inference(forward_demodulation,[],[f1941,f2429])).

fof(f1941,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) != sK4(u1_struct_0(sK5))
    | ~ spl7_347 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f7491,plain,
    ( spl7_1062
    | ~ spl7_422
    | ~ spl7_906 ),
    inference(avatar_split_clause,[],[f7411,f6092,f2428,f7489])).

fof(f7489,plain,
    ( spl7_1062
  <=> k3_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK5),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1062])])).

fof(f6092,plain,
    ( spl7_906
  <=> k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_906])])).

fof(f7411,plain,
    ( k3_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,k3_struct_0(sK5),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0)
    | ~ spl7_422
    | ~ spl7_906 ),
    inference(superposition,[],[f6093,f2429])).

fof(f6093,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | ~ spl7_906 ),
    inference(avatar_component_clause,[],[f6092])).

fof(f7463,plain,
    ( spl7_1060
    | ~ spl7_350
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f7454,f2428,f1953,f7461])).

fof(f7454,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK5)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_350
    | ~ spl7_422 ),
    inference(resolution,[],[f2431,f121])).

fof(f7377,plain,
    ( spl7_1058
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_346
    | spl7_711 ),
    inference(avatar_split_clause,[],[f7310,f4414,f1943,f377,f186,f7375])).

fof(f7375,plain,
    ( spl7_1058
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1058])])).

fof(f4414,plain,
    ( spl7_711
  <=> ~ v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_711])])).

fof(f7310,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_346
    | ~ spl7_711 ),
    inference(forward_demodulation,[],[f7291,f1944])).

fof(f1944,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | ~ spl7_346 ),
    inference(avatar_component_clause,[],[f1943])).

fof(f7291,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_711 ),
    inference(resolution,[],[f7231,f4415])).

fof(f4415,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl7_711 ),
    inference(avatar_component_clause,[],[f4414])).

fof(f7370,plain,
    ( spl7_1056
    | ~ spl7_10
    | ~ spl7_52
    | spl7_417 ),
    inference(avatar_split_clause,[],[f7308,f2383,f377,f186,f7368])).

fof(f7368,plain,
    ( spl7_1056
  <=> k1_funct_1(k3_struct_0(sK5),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1056])])).

fof(f7308,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_417 ),
    inference(resolution,[],[f7231,f2384])).

fof(f7363,plain,
    ( spl7_1054
    | ~ spl7_10
    | ~ spl7_52
    | spl7_311 ),
    inference(avatar_split_clause,[],[f7296,f1734,f377,f186,f7361])).

fof(f7361,plain,
    ( spl7_1054
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1054])])).

fof(f7296,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_311 ),
    inference(resolution,[],[f7231,f1735])).

fof(f7356,plain,
    ( spl7_1052
    | ~ spl7_10
    | ~ spl7_52
    | spl7_305 ),
    inference(avatar_split_clause,[],[f7292,f1705,f377,f186,f7354])).

fof(f7354,plain,
    ( spl7_1052
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1052])])).

fof(f7292,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_305 ),
    inference(resolution,[],[f7231,f1706])).

fof(f7347,plain,
    ( spl7_1050
    | ~ spl7_10
    | ~ spl7_52
    | spl7_485 ),
    inference(avatar_split_clause,[],[f7306,f2881,f377,f186,f7345])).

fof(f7345,plain,
    ( spl7_1050
  <=> k1_funct_1(k3_struct_0(sK5),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1050])])).

fof(f7306,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_485 ),
    inference(resolution,[],[f7231,f2882])).

fof(f7340,plain,
    ( spl7_1048
    | ~ spl7_10
    | ~ spl7_52
    | spl7_451 ),
    inference(avatar_split_clause,[],[f7290,f2709,f377,f186,f7338])).

fof(f7338,plain,
    ( spl7_1048
  <=> k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1048])])).

fof(f7290,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_451 ),
    inference(resolution,[],[f7231,f2710])).

fof(f7333,plain,
    ( spl7_1046
    | ~ spl7_10
    | ~ spl7_52
    | spl7_195 ),
    inference(avatar_split_clause,[],[f7295,f1102,f377,f186,f7331])).

fof(f7331,plain,
    ( spl7_1046
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1046])])).

fof(f7295,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_195 ),
    inference(resolution,[],[f7231,f1103])).

fof(f7326,plain,
    ( spl7_1044
    | ~ spl7_10
    | ~ spl7_52
    | spl7_181 ),
    inference(avatar_split_clause,[],[f7294,f1019,f377,f186,f7324])).

fof(f7324,plain,
    ( spl7_1044
  <=> k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1044])])).

fof(f7294,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_181 ),
    inference(resolution,[],[f7231,f1020])).

fof(f7319,plain,
    ( spl7_1042
    | ~ spl7_10
    | ~ spl7_52
    | spl7_117 ),
    inference(avatar_split_clause,[],[f7289,f681,f377,f186,f7317])).

fof(f7317,plain,
    ( spl7_1042
  <=> k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1042])])).

fof(f7289,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_117 ),
    inference(resolution,[],[f7231,f682])).

fof(f7275,plain,
    ( spl7_1040
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_524
    | spl7_535
    | ~ spl7_850 ),
    inference(avatar_split_clause,[],[f7254,f5626,f3395,f3319,f377,f186,f7273])).

fof(f7273,plain,
    ( spl7_1040
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1040])])).

fof(f7254,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK5),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_10
    | ~ spl7_52
    | ~ spl7_524
    | ~ spl7_535
    | ~ spl7_850 ),
    inference(forward_demodulation,[],[f7253,f5627])).

fof(f7268,plain,
    ( spl7_1038
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_52
    | spl7_117 ),
    inference(avatar_split_clause,[],[f7257,f681,f377,f207,f186,f7266])).

fof(f7266,plain,
    ( spl7_1038
  <=> k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1038])])).

fof(f7257,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),sK2)
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_52
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f7229,f682])).

fof(f7229,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK0)),sK2)
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(resolution,[],[f5457,f208])).

fof(f7179,plain,
    ( spl7_1036
    | ~ spl7_94
    | spl7_485
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6730,f6299,f2881,f575,f7177])).

fof(f7177,plain,
    ( spl7_1036
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1036])])).

fof(f6730,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_94
    | ~ spl7_485
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f2882])).

fof(f7172,plain,
    ( spl7_1034
    | ~ spl7_94
    | spl7_357
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6724,f6299,f1983,f575,f7170])).

fof(f7170,plain,
    ( spl7_1034
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1034])])).

fof(f6724,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_94
    | ~ spl7_357
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f1984])).

fof(f7165,plain,
    ( spl7_1032
    | ~ spl7_94
    | spl7_349
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6723,f6299,f1947,f575,f7163])).

fof(f7163,plain,
    ( spl7_1032
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1032])])).

fof(f6723,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_94
    | ~ spl7_349
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f1948])).

fof(f7156,plain,
    ( spl7_1030
    | ~ spl7_94
    | spl7_195
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6719,f6299,f1102,f575,f7154])).

fof(f7154,plain,
    ( spl7_1030
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1030])])).

fof(f6719,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_94
    | ~ spl7_195
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f1103])).

fof(f7149,plain,
    ( spl7_1028
    | ~ spl7_94
    | spl7_181
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6718,f6299,f1019,f575,f7147])).

fof(f7147,plain,
    ( spl7_1028
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1028])])).

fof(f6718,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_94
    | ~ spl7_181
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f1020])).

fof(f7142,plain,
    ( spl7_1026
    | ~ spl7_94
    | spl7_711
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6715,f6299,f4414,f575,f7140])).

fof(f7140,plain,
    ( spl7_1026
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1026])])).

fof(f6715,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_94
    | ~ spl7_711
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f4415])).

fof(f7135,plain,
    ( spl7_1024
    | ~ spl7_94
    | spl7_451
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6714,f6299,f2709,f575,f7133])).

fof(f7133,plain,
    ( spl7_1024
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1024])])).

fof(f6714,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_94
    | ~ spl7_451
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f2710])).

fof(f7128,plain,
    ( spl7_1022
    | ~ spl7_94
    | spl7_117
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6713,f6299,f681,f575,f7126])).

fof(f7126,plain,
    ( spl7_1022
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1022])])).

fof(f6713,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_94
    | ~ spl7_117
    | ~ spl7_956 ),
    inference(resolution,[],[f6667,f682])).

fof(f7118,plain,
    ( spl7_1020
    | ~ spl7_90
    | spl7_485
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6445,f6261,f2881,f556,f7116])).

fof(f7116,plain,
    ( spl7_1020
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1020])])).

fof(f6445,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_90
    | ~ spl7_485
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f2882])).

fof(f7111,plain,
    ( spl7_1018
    | ~ spl7_90
    | spl7_357
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6440,f6261,f1983,f556,f7109])).

fof(f7109,plain,
    ( spl7_1018
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1018])])).

fof(f6440,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_90
    | ~ spl7_357
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f1984])).

fof(f7104,plain,
    ( spl7_1016
    | ~ spl7_90
    | spl7_349
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6439,f6261,f1947,f556,f7102])).

fof(f7102,plain,
    ( spl7_1016
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1016])])).

fof(f6439,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_90
    | ~ spl7_349
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f1948])).

fof(f7097,plain,
    ( spl7_1014
    | ~ spl7_90
    | spl7_195
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6435,f6261,f1102,f556,f7095])).

fof(f7095,plain,
    ( spl7_1014
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1014])])).

fof(f6435,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_90
    | ~ spl7_195
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f1103])).

fof(f7090,plain,
    ( spl7_1012
    | ~ spl7_90
    | spl7_181
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6434,f6261,f1019,f556,f7088])).

fof(f7088,plain,
    ( spl7_1012
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1012])])).

fof(f6434,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_90
    | ~ spl7_181
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f1020])).

fof(f7083,plain,
    ( spl7_1010
    | ~ spl7_90
    | spl7_711
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6431,f6261,f4414,f556,f7081])).

fof(f7081,plain,
    ( spl7_1010
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1010])])).

fof(f6431,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_90
    | ~ spl7_711
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f4415])).

fof(f7076,plain,
    ( spl7_1008
    | ~ spl7_90
    | spl7_451
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6430,f6261,f2709,f556,f7074])).

fof(f7074,plain,
    ( spl7_1008
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1008])])).

fof(f6430,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_90
    | ~ spl7_451
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f2710])).

fof(f7035,plain,
    ( spl7_1006
    | ~ spl7_90
    | spl7_117
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6429,f6261,f681,f556,f7033])).

fof(f7033,plain,
    ( spl7_1006
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1006])])).

fof(f6429,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_90
    | ~ spl7_117
    | ~ spl7_950 ),
    inference(resolution,[],[f6386,f682])).

fof(f7017,plain,
    ( spl7_1004
    | ~ spl7_68
    | ~ spl7_200
    | spl7_415
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5410,f5067,f2377,f1132,f463,f7015])).

fof(f7015,plain,
    ( spl7_1004
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1004])])).

fof(f5410,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_68
    | ~ spl7_200
    | ~ spl7_415
    | ~ spl7_792 ),
    inference(subsumption_resolution,[],[f5391,f2378])).

fof(f5391,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_68
    | ~ spl7_200
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f1133])).

fof(f6997,plain,
    ( spl7_1002
    | ~ spl7_64
    | ~ spl7_200
    | spl7_415
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5273,f5040,f2377,f1132,f447,f6995])).

fof(f6995,plain,
    ( spl7_1002
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1002])])).

fof(f5273,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_64
    | ~ spl7_200
    | ~ spl7_415
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5251,f2378])).

fof(f5251,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1)))
    | ~ spl7_64
    | ~ spl7_200
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f1133])).

fof(f6958,plain,
    ( spl7_1000
    | spl7_164
    | ~ spl7_94
    | ~ spl7_126
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6661,f6299,f732,f575,f940,f6956])).

fof(f6956,plain,
    ( spl7_1000
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1000])])).

fof(f6661,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_126
    | ~ spl7_956 ),
    inference(resolution,[],[f6323,f733])).

fof(f6951,plain,
    ( spl7_998
    | ~ spl7_68
    | spl7_417
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f6901,f5067,f2383,f463,f6949])).

fof(f6949,plain,
    ( spl7_998
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_998])])).

fof(f6901,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_68
    | ~ spl7_417
    | ~ spl7_792 ),
    inference(resolution,[],[f2384,f5386])).

fof(f6913,plain,
    ( spl7_996
    | ~ spl7_64
    | spl7_417
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f6900,f5040,f2383,f447,f6911])).

fof(f6911,plain,
    ( spl7_996
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_996])])).

fof(f6900,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(k3_struct_0(sK1)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1))))
    | ~ spl7_64
    | ~ spl7_417
    | ~ spl7_788 ),
    inference(resolution,[],[f2384,f5246])).

fof(f6906,plain,
    ( spl7_536
    | spl7_417 ),
    inference(avatar_split_clause,[],[f6899,f2383,f3405])).

fof(f3405,plain,
    ( spl7_536
  <=> k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) = sK4(sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_536])])).

fof(f6899,plain,
    ( k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) = sK4(sK4(k3_struct_0(sK1)))
    | ~ spl7_417 ),
    inference(resolution,[],[f2384,f858])).

fof(f6898,plain,
    ( spl7_994
    | ~ spl7_20
    | ~ spl7_416 ),
    inference(avatar_split_clause,[],[f6881,f2386,f223,f6896])).

fof(f6896,plain,
    ( spl7_994
  <=> o_0_0_xboole_0 = sK4(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_994])])).

fof(f2386,plain,
    ( spl7_416
  <=> v1_xboole_0(sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_416])])).

fof(f6881,plain,
    ( o_0_0_xboole_0 = sK4(k3_struct_0(sK1))
    | ~ spl7_20
    | ~ spl7_416 ),
    inference(forward_demodulation,[],[f6869,f224])).

fof(f6869,plain,
    ( k1_xboole_0 = sK4(k3_struct_0(sK1))
    | ~ spl7_416 ),
    inference(resolution,[],[f2387,f117])).

fof(f2387,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | ~ spl7_416 ),
    inference(avatar_component_clause,[],[f2386])).

fof(f6868,plain,
    ( spl7_992
    | spl7_416
    | ~ spl7_72
    | ~ spl7_518
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5804,f5132,f3259,f479,f2386,f6866])).

fof(f6866,plain,
    ( spl7_992
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_992])])).

fof(f3259,plain,
    ( spl7_518
  <=> m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_518])])).

fof(f5804,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_518
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f3260])).

fof(f3260,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK1)))
    | ~ spl7_518 ),
    inference(avatar_component_clause,[],[f3259])).

fof(f6741,plain,
    ( spl7_990
    | ~ spl7_94
    | ~ spl7_524
    | spl7_535
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6686,f6299,f3395,f3319,f575,f6739])).

fof(f6739,plain,
    ( spl7_990
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_990])])).

fof(f6686,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_524
    | ~ spl7_535
    | ~ spl7_956 ),
    inference(subsumption_resolution,[],[f6660,f3396])).

fof(f6660,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_94
    | ~ spl7_524
    | ~ spl7_956 ),
    inference(resolution,[],[f6323,f3320])).

fof(f6699,plain,
    ( spl7_988
    | ~ spl7_16
    | ~ spl7_94
    | spl7_117
    | ~ spl7_956 ),
    inference(avatar_split_clause,[],[f6688,f6299,f681,f575,f207,f6697])).

fof(f6697,plain,
    ( spl7_988
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_988])])).

fof(f6688,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_94
    | ~ spl7_117
    | ~ spl7_956 ),
    inference(subsumption_resolution,[],[f6665,f682])).

fof(f6665,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_94
    | ~ spl7_956 ),
    inference(resolution,[],[f6323,f208])).

fof(f6606,plain,
    ( spl7_548
    | spl7_894
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_230
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5705,f5067,f1326,f463,f223,f6023,f3447])).

fof(f6023,plain,
    ( spl7_894
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_894])])).

fof(f5705,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_68
    | ~ spl7_230
    | ~ spl7_792 ),
    inference(superposition,[],[f5445,f1327])).

fof(f6605,plain,
    ( spl7_548
    | spl7_892
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_230
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5656,f5040,f1326,f447,f223,f6016,f3447])).

fof(f6016,plain,
    ( spl7_892
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_892])])).

fof(f5656,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_64
    | ~ spl7_230
    | ~ spl7_788 ),
    inference(superposition,[],[f5328,f1327])).

fof(f6604,plain,
    ( spl7_986
    | spl7_164
    | ~ spl7_90
    | ~ spl7_126
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6380,f6261,f732,f556,f940,f6602])).

fof(f6602,plain,
    ( spl7_986
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_986])])).

fof(f6380,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_126
    | ~ spl7_950 ),
    inference(resolution,[],[f6287,f733])).

fof(f6597,plain,
    ( spl7_984
    | ~ spl7_90
    | ~ spl7_230
    | spl7_535
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6583,f6261,f3395,f1326,f556,f6595])).

fof(f6583,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_90
    | ~ spl7_230
    | ~ spl7_535
    | ~ spl7_950 ),
    inference(forward_demodulation,[],[f6577,f1327])).

fof(f6577,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_90
    | ~ spl7_535
    | ~ spl7_950 ),
    inference(resolution,[],[f3396,f6386])).

fof(f6576,plain,
    ( spl7_548
    | ~ spl7_20
    | ~ spl7_534 ),
    inference(avatar_split_clause,[],[f6566,f3398,f223,f3447])).

fof(f6566,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_534 ),
    inference(forward_demodulation,[],[f6555,f224])).

fof(f6555,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = k1_xboole_0
    | ~ spl7_534 ),
    inference(resolution,[],[f3399,f117])).

fof(f3399,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_534 ),
    inference(avatar_component_clause,[],[f3398])).

fof(f6554,plain,
    ( spl7_982
    | spl7_534
    | ~ spl7_76
    | ~ spl7_524
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5942,f5169,f3319,f495,f3398,f6552])).

fof(f5942,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_524
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f3320])).

fof(f6536,plain,
    ( spl7_980
    | ~ spl7_68
    | spl7_719
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5436,f5067,f4589,f463,f6534])).

fof(f6534,plain,
    ( spl7_980
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_980])])).

fof(f5436,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6))))
    | ~ spl7_68
    | ~ spl7_719
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f4590])).

fof(f6529,plain,
    ( spl7_978
    | ~ spl7_68
    | spl7_311
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5434,f5067,f1734,f463,f6527])).

fof(f6527,plain,
    ( spl7_978
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_978])])).

fof(f5434,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_68
    | ~ spl7_311
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1735])).

fof(f6522,plain,
    ( spl7_976
    | ~ spl7_68
    | spl7_305
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5430,f5067,f1705,f463,f6520])).

fof(f6520,plain,
    ( spl7_976
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_976])])).

fof(f5430,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_68
    | ~ spl7_305
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1706])).

fof(f6511,plain,
    ( spl7_974
    | ~ spl7_64
    | spl7_719
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5319,f5040,f4589,f447,f6509])).

fof(f6509,plain,
    ( spl7_974
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_974])])).

fof(f5319,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK6)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6))))
    | ~ spl7_64
    | ~ spl7_719
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f4590])).

fof(f6504,plain,
    ( spl7_972
    | ~ spl7_64
    | spl7_311
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5317,f5040,f1734,f447,f6502])).

fof(f6502,plain,
    ( spl7_972
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_972])])).

fof(f5317,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK3(sK0)))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_64
    | ~ spl7_311
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1735])).

fof(f6496,plain,
    ( spl7_970
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_100
    | spl7_451 ),
    inference(avatar_split_clause,[],[f6481,f2709,f607,f258,f246,f6494])).

fof(f6494,plain,
    ( spl7_970
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_970])])).

fof(f607,plain,
    ( spl7_100
  <=> k1_funct_1(k3_struct_0(sK1),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f6481,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK2) = sK2
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_100
    | ~ spl7_451 ),
    inference(forward_demodulation,[],[f6480,f608])).

fof(f608,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = sK2
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f607])).

fof(f6480,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK2)
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_451 ),
    inference(subsumption_resolution,[],[f6479,f259])).

fof(f6479,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_26
    | ~ spl7_451 ),
    inference(subsumption_resolution,[],[f6465,f2710])).

fof(f6465,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k1_funct_1(k3_struct_0(sK1),sK2) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_26 ),
    inference(resolution,[],[f3337,f247])).

fof(f6488,plain,
    ( spl7_968
    | ~ spl7_4
    | ~ spl7_16
    | spl7_117
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f6478,f865,f681,f207,f165,f6486])).

fof(f6486,plain,
    ( spl7_968
  <=> k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_968])])).

fof(f865,plain,
    ( spl7_150
  <=> k1_funct_1(k3_struct_0(sK0),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f6478,plain,
    ( k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK2) = sK2
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_117
    | ~ spl7_150 ),
    inference(forward_demodulation,[],[f6477,f866])).

fof(f866,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = sK2
    | ~ spl7_150 ),
    inference(avatar_component_clause,[],[f865])).

fof(f6477,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK2)
    | ~ spl7_4
    | ~ spl7_16
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f6476,f166])).

fof(f6476,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_16
    | ~ spl7_117 ),
    inference(subsumption_resolution,[],[f6464,f682])).

fof(f6464,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),sK2) = k3_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),k3_struct_0(sK0),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f3337,f208])).

fof(f6459,plain,
    ( spl7_966
    | ~ spl7_64
    | spl7_305
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5313,f5040,f1705,f447,f6457])).

fof(f6457,plain,
    ( spl7_966
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_966])])).

fof(f5313,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k4_tmap_1(sK0,sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_64
    | ~ spl7_305
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1706])).

fof(f6417,plain,
    ( spl7_964
    | ~ spl7_16
    | ~ spl7_90
    | spl7_117
    | ~ spl7_950 ),
    inference(avatar_split_clause,[],[f6406,f6261,f681,f556,f207,f6415])).

fof(f6415,plain,
    ( spl7_964
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_964])])).

fof(f6406,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_90
    | ~ spl7_117
    | ~ spl7_950 ),
    inference(subsumption_resolution,[],[f6384,f682])).

fof(f6384,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_90
    | ~ spl7_950 ),
    inference(resolution,[],[f6287,f208])).

fof(f6336,plain,
    ( spl7_962
    | spl7_534
    | ~ spl7_72
    | ~ spl7_524
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5800,f5132,f3319,f479,f3398,f6334])).

fof(f5800,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_524
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f3320])).

fof(f6318,plain,
    ( ~ spl7_36
    | spl7_961 ),
    inference(avatar_contradiction_clause,[],[f6317])).

fof(f6317,plain,
    ( $false
    | ~ spl7_36
    | ~ spl7_961 ),
    inference(subsumption_resolution,[],[f6316,f297])).

fof(f6316,plain,
    ( ~ l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl7_961 ),
    inference(resolution,[],[f6314,f114])).

fof(f6314,plain,
    ( ~ l1_struct_0(sK3(sK3(sK1)))
    | ~ spl7_961 ),
    inference(avatar_component_clause,[],[f6313])).

fof(f6313,plain,
    ( spl7_961
  <=> ~ l1_struct_0(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_961])])).

fof(f6315,plain,
    ( ~ spl7_961
    | spl7_957 ),
    inference(avatar_split_clause,[],[f6308,f6302,f6313])).

fof(f6308,plain,
    ( ~ l1_struct_0(sK3(sK3(sK1)))
    | ~ spl7_957 ),
    inference(resolution,[],[f6303,f110])).

fof(f6303,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_957 ),
    inference(avatar_component_clause,[],[f6302])).

fof(f6307,plain,
    ( ~ spl7_957
    | spl7_958
    | ~ spl7_36
    | ~ spl7_218 ),
    inference(avatar_split_clause,[],[f6297,f1261,f296,f6305,f6302])).

fof(f6305,plain,
    ( spl7_958
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_958])])).

fof(f6297,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X1))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) )
    | ~ spl7_36
    | ~ spl7_218 ),
    inference(subsumption_resolution,[],[f6295,f1262])).

fof(f6295,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),X1))
        | ~ m1_subset_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK1)))) )
    | ~ spl7_36 ),
    inference(superposition,[],[f141,f4976])).

fof(f6282,plain,
    ( ~ spl7_34
    | spl7_955 ),
    inference(avatar_contradiction_clause,[],[f6281])).

fof(f6281,plain,
    ( $false
    | ~ spl7_34
    | ~ spl7_955 ),
    inference(subsumption_resolution,[],[f6280,f287])).

fof(f6280,plain,
    ( ~ l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_955 ),
    inference(resolution,[],[f6278,f114])).

fof(f6278,plain,
    ( ~ l1_struct_0(sK3(sK3(sK0)))
    | ~ spl7_955 ),
    inference(avatar_component_clause,[],[f6277])).

fof(f6277,plain,
    ( spl7_955
  <=> ~ l1_struct_0(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_955])])).

fof(f6279,plain,
    ( ~ spl7_955
    | spl7_951 ),
    inference(avatar_split_clause,[],[f6272,f6264,f6277])).

fof(f6272,plain,
    ( ~ l1_struct_0(sK3(sK3(sK0)))
    | ~ spl7_951 ),
    inference(resolution,[],[f6265,f110])).

fof(f6265,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0))))
    | ~ spl7_951 ),
    inference(avatar_component_clause,[],[f6264])).

fof(f6269,plain,
    ( ~ spl7_951
    | spl7_952
    | ~ spl7_34
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f6259,f1250,f286,f6267,f6264])).

fof(f6267,plain,
    ( spl7_952
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_952])])).

fof(f6259,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X1))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) )
    | ~ spl7_34
    | ~ spl7_216 ),
    inference(subsumption_resolution,[],[f6257,f1251])).

fof(f6257,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),X1))
        | ~ m1_subset_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK3(sK0)))) )
    | ~ spl7_34 ),
    inference(superposition,[],[f141,f4975])).

fof(f6252,plain,
    ( spl7_948
    | ~ spl7_76
    | spl7_485
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6008,f5169,f2881,f495,f6250])).

fof(f6250,plain,
    ( spl7_948
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_948])])).

fof(f6008,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_76
    | ~ spl7_485
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f2882])).

fof(f6245,plain,
    ( spl7_946
    | ~ spl7_76
    | spl7_357
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6003,f5169,f1983,f495,f6243])).

fof(f6243,plain,
    ( spl7_946
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_946])])).

fof(f6003,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_76
    | ~ spl7_357
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1984])).

fof(f6238,plain,
    ( spl7_944
    | ~ spl7_76
    | spl7_349
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f6002,f5169,f1947,f495,f6236])).

fof(f6236,plain,
    ( spl7_944
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_944])])).

fof(f6002,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_76
    | ~ spl7_349
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1948])).

fof(f6231,plain,
    ( spl7_942
    | ~ spl7_76
    | spl7_195
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5998,f5169,f1102,f495,f6229])).

fof(f6229,plain,
    ( spl7_942
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_942])])).

fof(f5998,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_76
    | ~ spl7_195
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1103])).

fof(f6224,plain,
    ( spl7_940
    | ~ spl7_76
    | spl7_181
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5997,f5169,f1019,f495,f6222])).

fof(f6222,plain,
    ( spl7_940
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_940])])).

fof(f5997,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_76
    | ~ spl7_181
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f1020])).

fof(f6217,plain,
    ( spl7_938
    | ~ spl7_76
    | spl7_711
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5994,f5169,f4414,f495,f6215])).

fof(f6215,plain,
    ( spl7_938
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_938])])).

fof(f5994,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_76
    | ~ spl7_711
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f4415])).

fof(f6210,plain,
    ( spl7_936
    | ~ spl7_76
    | spl7_451
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5993,f5169,f2709,f495,f6208])).

fof(f6208,plain,
    ( spl7_936
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_936])])).

fof(f5993,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_76
    | ~ spl7_451
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f2710])).

fof(f6203,plain,
    ( spl7_934
    | ~ spl7_76
    | spl7_117
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5992,f5169,f681,f495,f6201])).

fof(f6201,plain,
    ( spl7_934
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_934])])).

fof(f5992,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_76
    | ~ spl7_117
    | ~ spl7_814 ),
    inference(resolution,[],[f5949,f682])).

fof(f6196,plain,
    ( spl7_932
    | ~ spl7_72
    | spl7_485
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5866,f5132,f2881,f479,f6194])).

fof(f6194,plain,
    ( spl7_932
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_932])])).

fof(f5866,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_72
    | ~ spl7_485
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f2882])).

fof(f6186,plain,
    ( spl7_930
    | ~ spl7_72
    | spl7_357
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5861,f5132,f1983,f479,f6184])).

fof(f6184,plain,
    ( spl7_930
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_930])])).

fof(f5861,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_72
    | ~ spl7_357
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1984])).

fof(f6175,plain,
    ( spl7_928
    | ~ spl7_72
    | spl7_349
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5860,f5132,f1947,f479,f6173])).

fof(f6173,plain,
    ( spl7_928
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_928])])).

fof(f5860,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_72
    | ~ spl7_349
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1948])).

fof(f6168,plain,
    ( spl7_926
    | ~ spl7_72
    | spl7_195
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5856,f5132,f1102,f479,f6166])).

fof(f6166,plain,
    ( spl7_926
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_926])])).

fof(f5856,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_72
    | ~ spl7_195
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1103])).

fof(f6161,plain,
    ( spl7_924
    | ~ spl7_72
    | spl7_181
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5855,f5132,f1019,f479,f6159])).

fof(f6159,plain,
    ( spl7_924
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_924])])).

fof(f5855,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_72
    | ~ spl7_181
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f1020])).

fof(f6154,plain,
    ( spl7_922
    | ~ spl7_72
    | spl7_711
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5852,f5132,f4414,f479,f6152])).

fof(f6152,plain,
    ( spl7_922
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_922])])).

fof(f5852,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_72
    | ~ spl7_711
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f4415])).

fof(f6147,plain,
    ( spl7_920
    | ~ spl7_72
    | spl7_451
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5851,f5132,f2709,f479,f6145])).

fof(f6145,plain,
    ( spl7_920
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_920])])).

fof(f5851,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_72
    | ~ spl7_451
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f2710])).

fof(f6140,plain,
    ( spl7_918
    | ~ spl7_72
    | spl7_117
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5850,f5132,f681,f479,f6138])).

fof(f6138,plain,
    ( spl7_918
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_918])])).

fof(f5850,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_808 ),
    inference(resolution,[],[f5807,f682])).

fof(f6133,plain,
    ( spl7_916
    | ~ spl7_68
    | ~ spl7_390
    | spl7_473
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5403,f5067,f2805,f2232,f463,f6131])).

fof(f6131,plain,
    ( spl7_916
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_916])])).

fof(f2232,plain,
    ( spl7_390
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_390])])).

fof(f5403,plain,
    ( k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_390
    | ~ spl7_473
    | ~ spl7_792 ),
    inference(subsumption_resolution,[],[f5378,f2806])).

fof(f5378,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_390
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f2233])).

fof(f2233,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_390 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f6126,plain,
    ( spl7_914
    | ~ spl7_64
    | ~ spl7_390
    | spl7_473
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5265,f5040,f2805,f2232,f447,f6124])).

fof(f5265,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_390
    | ~ spl7_473
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5238,f2806])).

fof(f5238,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_390
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f2233])).

fof(f6119,plain,
    ( ~ spl7_911
    | spl7_912
    | ~ spl7_908 ),
    inference(avatar_split_clause,[],[f6103,f6098,f6117,f6114])).

fof(f6114,plain,
    ( spl7_911
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_911])])).

fof(f6117,plain,
    ( spl7_912
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK6),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_912])])).

fof(f6098,plain,
    ( spl7_908
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK6),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_908])])).

fof(f6103,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK6),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))) )
    | ~ spl7_908 ),
    inference(resolution,[],[f6099,f113])).

fof(f6099,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK6),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ spl7_908 ),
    inference(avatar_component_clause,[],[f6098])).

fof(f6100,plain,
    ( ~ spl7_833
    | spl7_908
    | ~ spl7_12
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f5473,f693,f193,f6098,f5479])).

fof(f5479,plain,
    ( spl7_833
  <=> ~ v1_funct_1(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_833])])).

fof(f193,plain,
    ( spl7_12
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f5473,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK6),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
        | ~ v1_funct_1(k3_struct_0(sK6)) )
    | ~ spl7_12
    | ~ spl7_118 ),
    inference(subsumption_resolution,[],[f5471,f694])).

fof(f5471,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK6),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
        | ~ m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
        | ~ v1_funct_1(k3_struct_0(sK6)) )
    | ~ spl7_12 ),
    inference(superposition,[],[f142,f5027])).

fof(f5027,plain,
    ( ! [X56] : k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK6),k3_struct_0(sK6),X56) = k7_relat_1(k3_struct_0(sK6),X56)
    | ~ spl7_12 ),
    inference(resolution,[],[f4970,f194])).

fof(f194,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f6094,plain,
    ( spl7_906
    | ~ spl7_346
    | ~ spl7_844 ),
    inference(avatar_split_clause,[],[f5880,f5549,f1943,f6092])).

fof(f5549,plain,
    ( spl7_844
  <=> ! [X0] :
        ( k1_funct_1(k3_struct_0(sK5),X0) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_844])])).

fof(f5880,plain,
    ( k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | ~ spl7_346
    | ~ spl7_844 ),
    inference(forward_demodulation,[],[f5876,f1944])).

fof(f5876,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),sK4(u1_struct_0(sK5)))
    | ~ spl7_844 ),
    inference(resolution,[],[f5550,f121])).

fof(f5550,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK5))
        | k1_funct_1(k3_struct_0(sK5),X0) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0) )
    | ~ spl7_844 ),
    inference(avatar_component_clause,[],[f5549])).

fof(f6084,plain,
    ( spl7_904
    | ~ spl7_64
    | ~ spl7_490
    | spl7_507
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5264,f5040,f3168,f2935,f447,f6082])).

fof(f6082,plain,
    ( spl7_904
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_904])])).

fof(f2935,plain,
    ( spl7_490
  <=> m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_490])])).

fof(f5264,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_490
    | ~ spl7_507
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5236,f3169])).

fof(f5236,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_490
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f2936])).

fof(f2936,plain,
    ( m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_490 ),
    inference(avatar_component_clause,[],[f2935])).

fof(f6077,plain,
    ( spl7_902
    | spl7_416
    | ~ spl7_68
    | ~ spl7_518
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5383,f5067,f3259,f463,f2386,f6075])).

fof(f6075,plain,
    ( spl7_902
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_902])])).

fof(f5383,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_518
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f3260])).

fof(f6070,plain,
    ( spl7_900
    | spl7_416
    | ~ spl7_64
    | ~ spl7_518
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5243,f5040,f3259,f447,f2386,f6068])).

fof(f6068,plain,
    ( spl7_900
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_900])])).

fof(f5243,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_518
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f3260])).

fof(f6061,plain,
    ( spl7_898
    | spl7_164
    | ~ spl7_76
    | ~ spl7_126
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5943,f5169,f732,f495,f940,f6059])).

fof(f6059,plain,
    ( spl7_898
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_898])])).

fof(f5943,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK1)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_76
    | ~ spl7_126
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f733])).

fof(f6032,plain,
    ( spl7_896
    | spl7_164
    | ~ spl7_72
    | ~ spl7_126
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5801,f5132,f732,f479,f940,f6030])).

fof(f6030,plain,
    ( spl7_896
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_896])])).

fof(f5801,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK3(sK0)),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_72
    | ~ spl7_126
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f733])).

fof(f6025,plain,
    ( spl7_894
    | spl7_534
    | ~ spl7_68
    | ~ spl7_524
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5379,f5067,f3319,f463,f3398,f6023])).

fof(f5379,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_524
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f3320])).

fof(f6018,plain,
    ( spl7_892
    | spl7_534
    | ~ spl7_64
    | ~ spl7_524
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5239,f5040,f3319,f447,f3398,f6016])).

fof(f5239,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_524
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f3320])).

fof(f5982,plain,
    ( spl7_890
    | ~ spl7_16
    | ~ spl7_76
    | spl7_117
    | ~ spl7_814 ),
    inference(avatar_split_clause,[],[f5971,f5169,f681,f495,f207,f5980])).

fof(f5980,plain,
    ( spl7_890
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_890])])).

fof(f5971,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_76
    | ~ spl7_117
    | ~ spl7_814 ),
    inference(subsumption_resolution,[],[f5947,f682])).

fof(f5947,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_76
    | ~ spl7_814 ),
    inference(resolution,[],[f5193,f208])).

fof(f5898,plain,
    ( ~ spl7_887
    | spl7_888
    | ~ spl7_884 ),
    inference(avatar_split_clause,[],[f5883,f5871,f5896,f5893])).

fof(f5893,plain,
    ( spl7_887
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_887])])).

fof(f5896,plain,
    ( spl7_888
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK1)),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_888])])).

fof(f5871,plain,
    ( spl7_884
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_884])])).

fof(f5883,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK1)),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))) )
    | ~ spl7_884 ),
    inference(resolution,[],[f5872,f113])).

fof(f5872,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
    | ~ spl7_884 ),
    inference(avatar_component_clause,[],[f5871])).

fof(f5873,plain,
    ( ~ spl7_815
    | spl7_884
    | ~ spl7_32
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f5166,f755,f276,f5871,f5172])).

fof(f5172,plain,
    ( spl7_815
  <=> ~ v1_funct_1(k3_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_815])])).

fof(f276,plain,
    ( spl7_32
  <=> l1_pre_topc(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f755,plain,
    ( spl7_130
  <=> m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f5166,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK1))) )
    | ~ spl7_32
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f5164,f756])).

fof(f756,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
    | ~ spl7_130 ),
    inference(avatar_component_clause,[],[f755])).

fof(f5164,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK1)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
        | ~ m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK1))) )
    | ~ spl7_32 ),
    inference(superposition,[],[f142,f4974])).

fof(f4974,plain,
    ( ! [X3] : k2_partfun1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)),k3_struct_0(sK3(sK1)),X3) = k7_relat_1(k3_struct_0(sK3(sK1)),X3)
    | ~ spl7_32 ),
    inference(resolution,[],[f4970,f277])).

fof(f277,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f5840,plain,
    ( spl7_882
    | ~ spl7_16
    | ~ spl7_72
    | spl7_117
    | ~ spl7_808 ),
    inference(avatar_split_clause,[],[f5829,f5132,f681,f479,f207,f5838])).

fof(f5838,plain,
    ( spl7_882
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_882])])).

fof(f5829,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_72
    | ~ spl7_117
    | ~ spl7_808 ),
    inference(subsumption_resolution,[],[f5805,f682])).

fof(f5805,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_72
    | ~ spl7_808 ),
    inference(resolution,[],[f5159,f208])).

fof(f5757,plain,
    ( ~ spl7_879
    | spl7_880
    | ~ spl7_876 ),
    inference(avatar_split_clause,[],[f5743,f5738,f5755,f5752])).

fof(f5752,plain,
    ( spl7_879
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_879])])).

fof(f5755,plain,
    ( spl7_880
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK0)),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_880])])).

fof(f5738,plain,
    ( spl7_876
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_876])])).

fof(f5743,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK3(sK0)),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))) )
    | ~ spl7_876 ),
    inference(resolution,[],[f5739,f113])).

fof(f5739,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
    | ~ spl7_876 ),
    inference(avatar_component_clause,[],[f5738])).

fof(f5740,plain,
    ( ~ spl7_809
    | spl7_876
    | ~ spl7_30
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f5129,f744,f266,f5738,f5135])).

fof(f5135,plain,
    ( spl7_809
  <=> ~ v1_funct_1(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_809])])).

fof(f5129,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK0))) )
    | ~ spl7_30
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f5127,f745])).

fof(f5127,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK3(sK0)),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
        | ~ m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK0))) )
    | ~ spl7_30 ),
    inference(superposition,[],[f142,f4973])).

fof(f4973,plain,
    ( ! [X2] : k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)),k3_struct_0(sK3(sK0)),X2) = k7_relat_1(k3_struct_0(sK3(sK0)),X2)
    | ~ spl7_30 ),
    inference(resolution,[],[f4970,f267])).

fof(f5736,plain,
    ( spl7_874
    | ~ spl7_68
    | spl7_485
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5443,f5067,f2881,f463,f5734])).

fof(f5734,plain,
    ( spl7_874
  <=> k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_874])])).

fof(f5443,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_68
    | ~ spl7_485
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f2882])).

fof(f5729,plain,
    ( spl7_872
    | ~ spl7_64
    | spl7_485
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5326,f5040,f2881,f447,f5727])).

fof(f5727,plain,
    ( spl7_872
  <=> k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_872])])).

fof(f5326,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(sK4(o_0_0_xboole_0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl7_64
    | ~ spl7_485
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f2882])).

fof(f5722,plain,
    ( spl7_870
    | ~ spl7_64
    | spl7_711
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5637,f5040,f4414,f447,f5720])).

fof(f5720,plain,
    ( spl7_870
  <=> k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_870])])).

fof(f5637,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_64
    | ~ spl7_711
    | ~ spl7_788 ),
    inference(resolution,[],[f4415,f5246])).

fof(f5715,plain,
    ( spl7_868
    | ~ spl7_68
    | spl7_711
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5636,f5067,f4414,f463,f5713])).

fof(f5713,plain,
    ( spl7_868
  <=> k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_868])])).

fof(f5636,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK5)),sK4(u1_struct_0(sK5)))
    | ~ spl7_68
    | ~ spl7_711
    | ~ spl7_792 ),
    inference(resolution,[],[f4415,f5386])).

fof(f5703,plain,
    ( spl7_866
    | ~ spl7_68
    | spl7_357
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5438,f5067,f1983,f463,f5701])).

fof(f5701,plain,
    ( spl7_866
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_866])])).

fof(f5438,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_68
    | ~ spl7_357
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1984])).

fof(f5696,plain,
    ( spl7_864
    | ~ spl7_68
    | spl7_349
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5437,f5067,f1947,f463,f5694])).

fof(f5694,plain,
    ( spl7_864
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_864])])).

fof(f5437,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_68
    | ~ spl7_349
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1948])).

fof(f5689,plain,
    ( spl7_862
    | ~ spl7_68
    | spl7_195
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5433,f5067,f1102,f463,f5687])).

fof(f5687,plain,
    ( spl7_862
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_862])])).

fof(f5433,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_68
    | ~ spl7_195
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1103])).

fof(f5673,plain,
    ( spl7_860
    | ~ spl7_68
    | spl7_181
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5432,f5067,f1019,f463,f5671])).

fof(f5671,plain,
    ( spl7_860
  <=> k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_860])])).

fof(f5432,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_68
    | ~ spl7_181
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f1020])).

fof(f5666,plain,
    ( spl7_858
    | ~ spl7_68
    | spl7_117
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5428,f5067,f681,f463,f5664])).

fof(f5664,plain,
    ( spl7_858
  <=> k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_858])])).

fof(f5428,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_68
    | ~ spl7_117
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f682])).

fof(f5654,plain,
    ( spl7_856
    | ~ spl7_64
    | spl7_357
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5321,f5040,f1983,f447,f5652])).

fof(f5652,plain,
    ( spl7_856
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_856])])).

fof(f5321,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK6))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK6)),sK4(k3_struct_0(sK6)))
    | ~ spl7_64
    | ~ spl7_357
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1984])).

fof(f5647,plain,
    ( spl7_854
    | ~ spl7_64
    | spl7_349
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5320,f5040,f1947,f447,f5645])).

fof(f5645,plain,
    ( spl7_854
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_854])])).

fof(f5320,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK5))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK5)),sK4(k3_struct_0(sK5)))
    | ~ spl7_64
    | ~ spl7_349
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1948])).

fof(f5640,plain,
    ( spl7_852
    | ~ spl7_424 ),
    inference(avatar_split_clause,[],[f5593,f2446,f5633])).

fof(f5593,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_424 ),
    inference(superposition,[],[f108,f2447])).

fof(f5635,plain,
    ( spl7_852
    | ~ spl7_112
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f2432,f2428,f665,f5633])).

fof(f2432,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl7_112
    | ~ spl7_422 ),
    inference(superposition,[],[f666,f2429])).

fof(f5628,plain,
    ( spl7_850
    | ~ spl7_424
    | ~ spl7_526 ),
    inference(avatar_split_clause,[],[f5592,f3333,f2446,f5626])).

fof(f3333,plain,
    ( spl7_526
  <=> k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_526])])).

fof(f5592,plain,
    ( k1_funct_1(k3_struct_0(sK5),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_424
    | ~ spl7_526 ),
    inference(superposition,[],[f3334,f2447])).

fof(f3334,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_526 ),
    inference(avatar_component_clause,[],[f3333])).

fof(f5619,plain,
    ( spl7_848
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f5588,f2428,f186,f5617])).

fof(f5588,plain,
    ( v1_funct_2(k3_struct_0(sK5),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl7_10
    | ~ spl7_422 ),
    inference(subsumption_resolution,[],[f5579,f187])).

fof(f5579,plain,
    ( v1_funct_2(k3_struct_0(sK5),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ l1_struct_0(sK5)
    | ~ spl7_422 ),
    inference(superposition,[],[f111,f2429])).

fof(f5612,plain,
    ( ~ spl7_847
    | ~ spl7_422
    | spl7_707 ),
    inference(avatar_split_clause,[],[f5576,f4405,f2428,f5610])).

fof(f5610,plain,
    ( spl7_847
  <=> ~ v1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_847])])).

fof(f4405,plain,
    ( spl7_707
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_707])])).

fof(f5576,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl7_422
    | ~ spl7_707 ),
    inference(superposition,[],[f4406,f2429])).

fof(f4406,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))
    | ~ spl7_707 ),
    inference(avatar_component_clause,[],[f4405])).

fof(f5568,plain,
    ( spl7_422
    | ~ spl7_20
    | ~ spl7_710 ),
    inference(avatar_split_clause,[],[f5561,f4417,f223,f2428])).

fof(f5561,plain,
    ( u1_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_710 ),
    inference(forward_demodulation,[],[f5553,f224])).

fof(f5553,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | ~ spl7_710 ),
    inference(resolution,[],[f4418,f117])).

fof(f4418,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ spl7_710 ),
    inference(avatar_component_clause,[],[f4417])).

fof(f5551,plain,
    ( spl7_710
    | spl7_844
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f3336,f186,f5549,f4417])).

fof(f3336,plain,
    ( ! [X0] :
        ( k1_funct_1(k3_struct_0(sK5),X0) = k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0)
        | v1_xboole_0(u1_struct_0(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f1853,f187])).

fof(f5547,plain,
    ( spl7_842
    | ~ spl7_64
    | spl7_195
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5316,f5040,f1102,f447,f5545])).

fof(f5545,plain,
    ( spl7_842
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_842])])).

fof(f5316,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_64
    | ~ spl7_195
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1103])).

fof(f5540,plain,
    ( spl7_840
    | ~ spl7_64
    | spl7_181
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5315,f5040,f1019,f447,f5538])).

fof(f5538,plain,
    ( spl7_840
  <=> k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_840])])).

fof(f5315,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(k3_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k3_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_64
    | ~ spl7_181
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f1020])).

fof(f5533,plain,
    ( spl7_838
    | ~ spl7_64
    | spl7_451
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5312,f5040,f2709,f447,f5531])).

fof(f5531,plain,
    ( spl7_838
  <=> k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_838])])).

fof(f5312,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_64
    | ~ spl7_451
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f2710])).

fof(f5495,plain,
    ( ~ spl7_12
    | spl7_837 ),
    inference(avatar_contradiction_clause,[],[f5494])).

fof(f5494,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_837 ),
    inference(subsumption_resolution,[],[f5493,f194])).

fof(f5493,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl7_837 ),
    inference(resolution,[],[f5491,f114])).

fof(f5491,plain,
    ( ~ l1_struct_0(sK6)
    | ~ spl7_837 ),
    inference(avatar_component_clause,[],[f5490])).

fof(f5490,plain,
    ( spl7_837
  <=> ~ l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_837])])).

fof(f5492,plain,
    ( ~ spl7_837
    | spl7_833 ),
    inference(avatar_split_clause,[],[f5485,f5479,f5490])).

fof(f5485,plain,
    ( ~ l1_struct_0(sK6)
    | ~ spl7_833 ),
    inference(resolution,[],[f5480,f110])).

fof(f5480,plain,
    ( ~ v1_funct_1(k3_struct_0(sK6))
    | ~ spl7_833 ),
    inference(avatar_component_clause,[],[f5479])).

fof(f5484,plain,
    ( ~ spl7_833
    | spl7_834
    | ~ spl7_12
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f5474,f693,f193,f5482,f5479])).

fof(f5482,plain,
    ( spl7_834
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK6),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_834])])).

fof(f5474,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK6),X1))
        | ~ v1_funct_1(k3_struct_0(sK6)) )
    | ~ spl7_12
    | ~ spl7_118 ),
    inference(subsumption_resolution,[],[f5472,f694])).

fof(f5472,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK6),X1))
        | ~ m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
        | ~ v1_funct_1(k3_struct_0(sK6)) )
    | ~ spl7_12 ),
    inference(superposition,[],[f141,f5027])).

fof(f5465,plain,
    ( spl7_830
    | spl7_164
    | ~ spl7_68
    | ~ spl7_126
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5380,f5067,f732,f463,f940,f5463])).

fof(f5463,plain,
    ( spl7_830
  <=> k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_830])])).

fof(f5380,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK1),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_68
    | ~ spl7_126
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f733])).

fof(f5458,plain,
    ( spl7_822
    | spl7_164
    | ~ spl7_64
    | ~ spl7_126
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5240,f5040,f732,f447,f940,f5286])).

fof(f5286,plain,
    ( spl7_822
  <=> k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_822])])).

fof(f5240,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_126
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f733])).

fof(f5454,plain,
    ( spl7_828
    | ~ spl7_68
    | ~ spl7_156
    | spl7_451
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5446,f5067,f2709,f911,f463,f5452])).

fof(f5452,plain,
    ( spl7_828
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_828])])).

fof(f5446,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1))
    | ~ spl7_68
    | ~ spl7_156
    | ~ spl7_451
    | ~ spl7_792 ),
    inference(forward_demodulation,[],[f5429,f912])).

fof(f5429,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK4(u1_struct_0(sK1)))
    | ~ spl7_68
    | ~ spl7_451
    | ~ spl7_792 ),
    inference(resolution,[],[f5386,f2710])).

fof(f5418,plain,
    ( spl7_826
    | ~ spl7_16
    | ~ spl7_68
    | ~ spl7_100
    | spl7_117
    | ~ spl7_792 ),
    inference(avatar_split_clause,[],[f5406,f5067,f681,f607,f463,f207,f5416])).

fof(f5416,plain,
    ( spl7_826
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_826])])).

fof(f5406,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK2) = sK2
    | ~ spl7_16
    | ~ spl7_68
    | ~ spl7_100
    | ~ spl7_117
    | ~ spl7_792 ),
    inference(forward_demodulation,[],[f5405,f608])).

fof(f5405,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_68
    | ~ spl7_117
    | ~ spl7_792 ),
    inference(subsumption_resolution,[],[f5384,f682])).

fof(f5384,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_68
    | ~ spl7_792 ),
    inference(resolution,[],[f5082,f208])).

fof(f5337,plain,
    ( spl7_824
    | ~ spl7_64
    | spl7_117
    | ~ spl7_154
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5329,f5040,f901,f681,f447,f5335])).

fof(f5335,plain,
    ( spl7_824
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_824])])).

fof(f5329,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0))
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_154
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f5311,f902])).

fof(f5311,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_788 ),
    inference(resolution,[],[f5246,f682])).

fof(f5301,plain,
    ( ~ spl7_8
    | ~ spl7_164
    | spl7_659 ),
    inference(avatar_contradiction_clause,[],[f5300])).

fof(f5300,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_164
    | ~ spl7_659 ),
    inference(subsumption_resolution,[],[f5293,f4156])).

fof(f4156,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_659 ),
    inference(avatar_component_clause,[],[f4155])).

fof(f4155,plain,
    ( spl7_659
  <=> k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_659])])).

fof(f5293,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_164 ),
    inference(resolution,[],[f941,f350])).

fof(f941,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_164 ),
    inference(avatar_component_clause,[],[f940])).

fof(f5299,plain,
    ( ~ spl7_20
    | ~ spl7_164
    | spl7_659 ),
    inference(avatar_contradiction_clause,[],[f5298])).

fof(f5298,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_164
    | ~ spl7_659 ),
    inference(subsumption_resolution,[],[f5297,f4156])).

fof(f5297,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_164 ),
    inference(forward_demodulation,[],[f5289,f224])).

fof(f5289,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = k1_xboole_0
    | ~ spl7_164 ),
    inference(resolution,[],[f941,f117])).

fof(f5288,plain,
    ( spl7_822
    | ~ spl7_64
    | ~ spl7_126
    | spl7_165
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5266,f5040,f937,f732,f447,f5286])).

fof(f5266,plain,
    ( k1_funct_1(k3_struct_0(sK0),o_0_0_xboole_0) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_126
    | ~ spl7_165
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5240,f938])).

fof(f5281,plain,
    ( spl7_820
    | ~ spl7_16
    | ~ spl7_64
    | spl7_117
    | ~ spl7_150
    | ~ spl7_788 ),
    inference(avatar_split_clause,[],[f5269,f5040,f865,f681,f447,f207,f5279])).

fof(f5279,plain,
    ( spl7_820
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_820])])).

fof(f5269,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK2) = sK2
    | ~ spl7_16
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_150
    | ~ spl7_788 ),
    inference(forward_demodulation,[],[f5268,f866])).

fof(f5268,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_64
    | ~ spl7_117
    | ~ spl7_788 ),
    inference(subsumption_resolution,[],[f5244,f682])).

fof(f5244,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k3_struct_0(sK0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK0)),sK2)
    | ~ spl7_16
    | ~ spl7_64
    | ~ spl7_788 ),
    inference(resolution,[],[f5055,f208])).

fof(f5188,plain,
    ( ~ spl7_32
    | spl7_819 ),
    inference(avatar_contradiction_clause,[],[f5187])).

fof(f5187,plain,
    ( $false
    | ~ spl7_32
    | ~ spl7_819 ),
    inference(subsumption_resolution,[],[f5186,f277])).

fof(f5186,plain,
    ( ~ l1_pre_topc(sK3(sK1))
    | ~ spl7_819 ),
    inference(resolution,[],[f5184,f114])).

fof(f5184,plain,
    ( ~ l1_struct_0(sK3(sK1))
    | ~ spl7_819 ),
    inference(avatar_component_clause,[],[f5183])).

fof(f5183,plain,
    ( spl7_819
  <=> ~ l1_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_819])])).

fof(f5185,plain,
    ( ~ spl7_819
    | spl7_815 ),
    inference(avatar_split_clause,[],[f5178,f5172,f5183])).

fof(f5178,plain,
    ( ~ l1_struct_0(sK3(sK1))
    | ~ spl7_815 ),
    inference(resolution,[],[f5173,f110])).

fof(f5173,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3(sK1)))
    | ~ spl7_815 ),
    inference(avatar_component_clause,[],[f5172])).

fof(f5177,plain,
    ( ~ spl7_815
    | spl7_816
    | ~ spl7_32
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f5167,f755,f276,f5175,f5172])).

fof(f5175,plain,
    ( spl7_816
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_816])])).

fof(f5167,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X1))
        | ~ v1_funct_1(k3_struct_0(sK3(sK1))) )
    | ~ spl7_32
    | ~ spl7_130 ),
    inference(subsumption_resolution,[],[f5165,f756])).

fof(f5165,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),X1))
        | ~ m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK1))) )
    | ~ spl7_32 ),
    inference(superposition,[],[f141,f4974])).

fof(f5151,plain,
    ( ~ spl7_30
    | spl7_813 ),
    inference(avatar_contradiction_clause,[],[f5150])).

fof(f5150,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_813 ),
    inference(subsumption_resolution,[],[f5149,f267])).

fof(f5149,plain,
    ( ~ l1_pre_topc(sK3(sK0))
    | ~ spl7_813 ),
    inference(resolution,[],[f5147,f114])).

fof(f5147,plain,
    ( ~ l1_struct_0(sK3(sK0))
    | ~ spl7_813 ),
    inference(avatar_component_clause,[],[f5146])).

fof(f5146,plain,
    ( spl7_813
  <=> ~ l1_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_813])])).

fof(f5148,plain,
    ( ~ spl7_813
    | spl7_809 ),
    inference(avatar_split_clause,[],[f5141,f5135,f5146])).

fof(f5141,plain,
    ( ~ l1_struct_0(sK3(sK0))
    | ~ spl7_809 ),
    inference(resolution,[],[f5136,f110])).

fof(f5136,plain,
    ( ~ v1_funct_1(k3_struct_0(sK3(sK0)))
    | ~ spl7_809 ),
    inference(avatar_component_clause,[],[f5135])).

fof(f5140,plain,
    ( ~ spl7_809
    | spl7_810
    | ~ spl7_30
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f5130,f744,f266,f5138,f5135])).

fof(f5138,plain,
    ( spl7_810
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_810])])).

fof(f5130,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X1))
        | ~ v1_funct_1(k3_struct_0(sK3(sK0))) )
    | ~ spl7_30
    | ~ spl7_128 ),
    inference(subsumption_resolution,[],[f5128,f745])).

fof(f5128,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),X1))
        | ~ m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
        | ~ v1_funct_1(k3_struct_0(sK3(sK0))) )
    | ~ spl7_30 ),
    inference(superposition,[],[f141,f4973])).

fof(f5126,plain,
    ( ~ spl7_805
    | spl7_806
    | ~ spl7_802 ),
    inference(avatar_split_clause,[],[f5114,f5109,f5124,f5121])).

fof(f5121,plain,
    ( spl7_805
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_805])])).

fof(f5124,plain,
    ( spl7_806
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK1),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_806])])).

fof(f5114,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK1),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) )
    | ~ spl7_802 ),
    inference(resolution,[],[f5110,f113])).

fof(f5111,plain,
    ( ~ spl7_793
    | spl7_802
    | ~ spl7_28
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f5064,f526,f258,f5109,f5070])).

fof(f5070,plain,
    ( spl7_793
  <=> ~ v1_funct_1(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_793])])).

fof(f526,plain,
    ( spl7_84
  <=> m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f5064,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_struct_0(sK1)) )
    | ~ spl7_28
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f5062,f527])).

fof(f527,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f526])).

fof(f5062,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK1),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_struct_0(sK1)) )
    | ~ spl7_28 ),
    inference(superposition,[],[f142,f4972])).

fof(f4972,plain,
    ( ! [X1] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),X1) = k7_relat_1(k3_struct_0(sK1),X1)
    | ~ spl7_28 ),
    inference(resolution,[],[f4970,f259])).

fof(f5107,plain,
    ( ~ spl7_799
    | spl7_800
    | ~ spl7_796 ),
    inference(avatar_split_clause,[],[f5095,f5090,f5105,f5102])).

fof(f5102,plain,
    ( spl7_799
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_799])])).

fof(f5095,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK0),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )
    | ~ spl7_796 ),
    inference(resolution,[],[f5091,f113])).

fof(f5092,plain,
    ( ~ spl7_789
    | spl7_796
    | ~ spl7_4
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f5030,f518,f165,f5090,f5043])).

fof(f5043,plain,
    ( spl7_789
  <=> ~ v1_funct_1(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_789])])).

fof(f5030,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k3_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f5028,f519])).

fof(f5028,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK0),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k3_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(superposition,[],[f142,f4971])).

fof(f5077,plain,
    ( ~ spl7_203
    | spl7_793 ),
    inference(avatar_split_clause,[],[f5076,f5070,f1147])).

fof(f1147,plain,
    ( spl7_203
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).

fof(f5076,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_793 ),
    inference(resolution,[],[f5071,f110])).

fof(f5071,plain,
    ( ~ v1_funct_1(k3_struct_0(sK1))
    | ~ spl7_793 ),
    inference(avatar_component_clause,[],[f5070])).

fof(f5075,plain,
    ( ~ spl7_793
    | spl7_794
    | ~ spl7_28
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f5065,f526,f258,f5073,f5070])).

fof(f5073,plain,
    ( spl7_794
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_794])])).

fof(f5065,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK1),X1))
        | ~ v1_funct_1(k3_struct_0(sK1)) )
    | ~ spl7_28
    | ~ spl7_84 ),
    inference(subsumption_resolution,[],[f5063,f527])).

fof(f5063,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK1),X1))
        | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k3_struct_0(sK1)) )
    | ~ spl7_28 ),
    inference(superposition,[],[f141,f4972])).

fof(f5050,plain,
    ( ~ spl7_153
    | spl7_789 ),
    inference(avatar_split_clause,[],[f5049,f5043,f882])).

fof(f5049,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_789 ),
    inference(resolution,[],[f5044,f110])).

fof(f5044,plain,
    ( ~ v1_funct_1(k3_struct_0(sK0))
    | ~ spl7_789 ),
    inference(avatar_component_clause,[],[f5043])).

fof(f5048,plain,
    ( ~ spl7_789
    | spl7_790
    | ~ spl7_4
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f5031,f518,f165,f5046,f5043])).

fof(f5046,plain,
    ( spl7_790
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_790])])).

fof(f5031,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK0),X1))
        | ~ v1_funct_1(k3_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f5029,f519])).

fof(f5029,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK0),X1))
        | ~ m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(k3_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(superposition,[],[f141,f4971])).

fof(f4948,plain,
    ( spl7_786
    | ~ spl7_698 ),
    inference(avatar_split_clause,[],[f4941,f4364,f4946])).

fof(f4946,plain,
    ( spl7_786
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_786])])).

fof(f4364,plain,
    ( spl7_698
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_698])])).

fof(f4941,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))))
    | ~ spl7_698 ),
    inference(subsumption_resolution,[],[f4940,f4365])).

fof(f4365,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))
    | ~ spl7_698 ),
    inference(avatar_component_clause,[],[f4364])).

fof(f4940,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))
    | ~ spl7_698 ),
    inference(resolution,[],[f4369,f116])).

fof(f4369,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_698 ),
    inference(resolution,[],[f4365,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_m1_pre_topc)).

fof(f4936,plain,
    ( spl7_784
    | ~ spl7_696 ),
    inference(avatar_split_clause,[],[f4929,f4349,f4934])).

fof(f4934,plain,
    ( spl7_784
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_784])])).

fof(f4349,plain,
    ( spl7_696
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_696])])).

fof(f4929,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))))
    | ~ spl7_696 ),
    inference(subsumption_resolution,[],[f4928,f4350])).

fof(f4350,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))
    | ~ spl7_696 ),
    inference(avatar_component_clause,[],[f4349])).

fof(f4928,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))
    | ~ spl7_696 ),
    inference(resolution,[],[f4354,f116])).

fof(f4354,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_696 ),
    inference(resolution,[],[f4350,f115])).

fof(f4925,plain,
    ( spl7_782
    | ~ spl7_780 ),
    inference(avatar_split_clause,[],[f4909,f4905,f4923])).

fof(f4923,plain,
    ( spl7_782
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_782])])).

fof(f4905,plain,
    ( spl7_780
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_780])])).

fof(f4909,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_780 ),
    inference(superposition,[],[f145,f4906])).

fof(f4906,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_780 ),
    inference(avatar_component_clause,[],[f4905])).

fof(f145,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f106,f107])).

fof(f106,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_k6_relat_1)).

fof(f4907,plain,
    ( spl7_780
    | ~ spl7_148 ),
    inference(avatar_split_clause,[],[f845,f842,f4905])).

fof(f842,plain,
    ( spl7_148
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f845,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_148 ),
    inference(resolution,[],[f843,f362])).

fof(f362,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f109,f114])).

fof(f109,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',d4_struct_0)).

fof(f843,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_148 ),
    inference(avatar_component_clause,[],[f842])).

fof(f4898,plain,
    ( spl7_778
    | ~ spl7_776 ),
    inference(avatar_split_clause,[],[f4882,f4878,f4896])).

fof(f4896,plain,
    ( spl7_778
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_778])])).

fof(f4878,plain,
    ( spl7_776
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_776])])).

fof(f4882,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_776 ),
    inference(superposition,[],[f145,f4879])).

fof(f4879,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_776 ),
    inference(avatar_component_clause,[],[f4878])).

fof(f4880,plain,
    ( spl7_776
    | ~ spl7_146 ),
    inference(avatar_split_clause,[],[f834,f831,f4878])).

fof(f831,plain,
    ( spl7_146
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f834,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_146 ),
    inference(resolution,[],[f832,f362])).

fof(f832,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_146 ),
    inference(avatar_component_clause,[],[f831])).

fof(f4873,plain,
    ( spl7_774
    | ~ spl7_18
    | ~ spl7_56
    | ~ spl7_252 ),
    inference(avatar_split_clause,[],[f1493,f1428,f396,f214,f4871])).

fof(f4871,plain,
    ( spl7_774
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_774])])).

fof(f396,plain,
    ( spl7_56
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f1428,plain,
    ( spl7_252
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_252])])).

fof(f1493,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_56
    | ~ spl7_252 ),
    inference(subsumption_resolution,[],[f1474,f397])).

fof(f397,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f396])).

fof(f1474,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_18
    | ~ spl7_252 ),
    inference(resolution,[],[f1454,f1429])).

fof(f1429,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_252 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1454,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k3_struct_0(X0))
        | k1_funct_1(k3_struct_0(X0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(X0),u1_struct_0(sK1)),sK2)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f1098,f114])).

fof(f1098,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ v1_relat_1(k3_struct_0(X0))
        | k1_funct_1(k3_struct_0(X0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(X0),u1_struct_0(sK1)),sK2) )
    | ~ spl7_18 ),
    inference(resolution,[],[f1068,f110])).

fof(f1068,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK2) = k1_funct_1(k7_relat_1(X0,u1_struct_0(sK1)),sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f132,f215])).

fof(f4861,plain,
    ( spl7_772
    | ~ spl7_250 ),
    inference(avatar_split_clause,[],[f1422,f1418,f4859])).

fof(f4859,plain,
    ( spl7_772
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_772])])).

fof(f1418,plain,
    ( spl7_250
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_250])])).

fof(f1422,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))),u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_250 ),
    inference(superposition,[],[f108,f1419])).

fof(f1419,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_250 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f4854,plain,
    ( spl7_770
    | ~ spl7_18
    | ~ spl7_140
    | ~ spl7_604 ),
    inference(avatar_split_clause,[],[f3803,f3799,f798,f214,f4852])).

fof(f4852,plain,
    ( spl7_770
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_770])])).

fof(f798,plain,
    ( spl7_140
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f3799,plain,
    ( spl7_604
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_604])])).

fof(f3803,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_140
    | ~ spl7_604 ),
    inference(subsumption_resolution,[],[f3802,f799])).

fof(f799,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f798])).

fof(f3802,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_18
    | ~ spl7_604 ),
    inference(resolution,[],[f3800,f1454])).

fof(f3800,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_604 ),
    inference(avatar_component_clause,[],[f3799])).

fof(f4843,plain,
    ( spl7_768
    | ~ spl7_18
    | ~ spl7_54
    | ~ spl7_248 ),
    inference(avatar_split_clause,[],[f1492,f1411,f386,f214,f4841])).

fof(f4841,plain,
    ( spl7_768
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_768])])).

fof(f386,plain,
    ( spl7_54
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f1411,plain,
    ( spl7_248
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).

fof(f1492,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_54
    | ~ spl7_248 ),
    inference(subsumption_resolution,[],[f1473,f387])).

fof(f387,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f386])).

fof(f1473,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_18
    | ~ spl7_248 ),
    inference(resolution,[],[f1454,f1412])).

fof(f1412,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_248 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f4831,plain,
    ( spl7_766
    | ~ spl7_246 ),
    inference(avatar_split_clause,[],[f1405,f1401,f4829])).

fof(f4829,plain,
    ( spl7_766
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_766])])).

fof(f1401,plain,
    ( spl7_246
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).

fof(f1405,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))),u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_246 ),
    inference(superposition,[],[f108,f1402])).

fof(f1402,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_246 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f4824,plain,
    ( spl7_762
    | ~ spl7_765
    | ~ spl7_760 ),
    inference(avatar_split_clause,[],[f4809,f4806,f4822,f4816])).

fof(f4816,plain,
    ( spl7_762
  <=> v1_xboole_0(sK4(k3_struct_0(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_762])])).

fof(f4822,plain,
    ( spl7_765
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))),sK4(k3_struct_0(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_765])])).

fof(f4806,plain,
    ( spl7_760
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK1)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))),X1)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_760])])).

fof(f4809,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))),sK4(k3_struct_0(sK3(sK1))))
    | v1_xboole_0(sK4(k3_struct_0(sK3(sK1))))
    | ~ spl7_760 ),
    inference(resolution,[],[f4807,f121])).

fof(f4807,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK1)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))),X1)
        | v1_xboole_0(X1) )
    | ~ spl7_760 ),
    inference(avatar_component_clause,[],[f4806])).

fof(f4808,plain,
    ( spl7_758
    | spl7_760
    | ~ spl7_320 ),
    inference(avatar_split_clause,[],[f1780,f1776,f4806,f4803])).

fof(f4803,plain,
    ( spl7_758
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_758])])).

fof(f1776,plain,
    ( spl7_320
  <=> ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))
        | ~ m1_subset_1(X5,k3_struct_0(sK3(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_320])])).

fof(f1780,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK1)))
        | v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))),X1) )
    | ~ spl7_320 ),
    inference(resolution,[],[f1777,f531])).

fof(f1777,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))
        | ~ m1_subset_1(X5,k3_struct_0(sK3(sK1))) )
    | ~ spl7_320 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f4798,plain,
    ( spl7_756
    | spl7_414
    | ~ spl7_242 ),
    inference(avatar_split_clause,[],[f1395,f1386,f2380,f4796])).

fof(f2380,plain,
    ( spl7_414
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_414])])).

fof(f1386,plain,
    ( spl7_242
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_242])])).

fof(f1395,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))
    | ~ spl7_242 ),
    inference(resolution,[],[f1387,f601])).

fof(f1387,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_242 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f4791,plain,
    ( spl7_684
    | ~ spl7_193
    | spl7_754
    | ~ spl7_390
    | ~ spl7_392 ),
    inference(avatar_split_clause,[],[f2288,f2283,f2232,f4789,f1090,f4310])).

fof(f1090,plain,
    ( spl7_193
  <=> ~ v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).

fof(f4789,plain,
    ( spl7_754
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3(sK0)))
        | k1_funct_1(o_0_0_xboole_0,X0) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_754])])).

fof(f2288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3(sK0)))
        | k1_funct_1(o_0_0_xboole_0,X0) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X0)
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK3(sK0))) )
    | ~ spl7_390
    | ~ spl7_392 ),
    inference(subsumption_resolution,[],[f2286,f2233])).

fof(f2286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3(sK0)))
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | k1_funct_1(o_0_0_xboole_0,X0) = k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X0)
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK3(sK0))) )
    | ~ spl7_392 ),
    inference(resolution,[],[f2284,f136])).

fof(f4787,plain,
    ( spl7_750
    | ~ spl7_753
    | ~ spl7_748 ),
    inference(avatar_split_clause,[],[f4772,f4769,f4785,f4779])).

fof(f4779,plain,
    ( spl7_750
  <=> v1_xboole_0(sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_750])])).

fof(f4785,plain,
    ( spl7_753
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_753])])).

fof(f4772,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0))))
    | v1_xboole_0(sK4(k3_struct_0(sK3(sK0))))
    | ~ spl7_748 ),
    inference(resolution,[],[f4770,f121])).

fof(f4771,plain,
    ( spl7_746
    | spl7_748
    | ~ spl7_312 ),
    inference(avatar_split_clause,[],[f1761,f1740,f4769,f4766])).

fof(f4766,plain,
    ( spl7_746
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_746])])).

fof(f1740,plain,
    ( spl7_312
  <=> ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))
        | ~ m1_subset_1(X4,k3_struct_0(sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_312])])).

fof(f1761,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k3_struct_0(sK3(sK0)))
        | v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))),X1) )
    | ~ spl7_312 ),
    inference(resolution,[],[f1741,f531])).

fof(f1741,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))
        | ~ m1_subset_1(X4,k3_struct_0(sK3(sK0))) )
    | ~ spl7_312 ),
    inference(avatar_component_clause,[],[f1740])).

fof(f4761,plain,
    ( spl7_716
    | spl7_406
    | ~ spl7_238 ),
    inference(avatar_split_clause,[],[f1380,f1371,f2352,f4503])).

fof(f4503,plain,
    ( spl7_716
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_716])])).

fof(f1371,plain,
    ( spl7_238
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_238])])).

fof(f1380,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_238 ),
    inference(resolution,[],[f1372,f601])).

fof(f1372,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_238 ),
    inference(avatar_component_clause,[],[f1371])).

fof(f4760,plain,
    ( spl7_744
    | ~ spl7_62
    | spl7_117
    | ~ spl7_736 ),
    inference(avatar_split_clause,[],[f4727,f4721,f681,f438,f4758])).

fof(f4727,plain,
    ( k1_funct_1(k3_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_62
    | ~ spl7_117
    | ~ spl7_736 ),
    inference(forward_demodulation,[],[f4726,f439])).

fof(f4726,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_117
    | ~ spl7_736 ),
    inference(subsumption_resolution,[],[f4724,f682])).

fof(f4724,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK0)),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)
    | ~ spl7_736 ),
    inference(resolution,[],[f4722,f601])).

fof(f4753,plain,
    ( ~ spl7_741
    | spl7_742
    | spl7_117
    | ~ spl7_736 ),
    inference(avatar_split_clause,[],[f4728,f4721,f681,f4751,f4745])).

fof(f4751,plain,
    ( spl7_742
  <=> v1_xboole_0(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_742])])).

fof(f4728,plain,
    ( v1_xboole_0(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2))
    | ~ m1_subset_1(u1_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_117
    | ~ spl7_736 ),
    inference(subsumption_resolution,[],[f4725,f682])).

fof(f4725,plain,
    ( v1_xboole_0(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2))
    | ~ spl7_736 ),
    inference(resolution,[],[f4722,f531])).

fof(f4735,plain,
    ( spl7_738
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | spl7_451 ),
    inference(avatar_split_clause,[],[f4714,f2709,f200,f165,f158,f151,f4733])).

fof(f4714,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK4(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_451 ),
    inference(resolution,[],[f4709,f121])).

fof(f4723,plain,
    ( spl7_736
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_26
    | spl7_451 ),
    inference(avatar_split_clause,[],[f4713,f2709,f246,f200,f165,f158,f151,f4721])).

fof(f4713,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),k4_tmap_1(sK0,sK1),sK2),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_451 ),
    inference(resolution,[],[f4709,f247])).

fof(f4703,plain,
    ( spl7_734
    | ~ spl7_674 ),
    inference(avatar_split_clause,[],[f4696,f4259,f4701])).

fof(f4701,plain,
    ( spl7_734
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_734])])).

fof(f4259,plain,
    ( spl7_674
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_674])])).

fof(f4696,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))))
    | ~ spl7_674 ),
    inference(subsumption_resolution,[],[f4695,f4260])).

fof(f4260,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))
    | ~ spl7_674 ),
    inference(avatar_component_clause,[],[f4259])).

fof(f4695,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))
    | ~ spl7_674 ),
    inference(resolution,[],[f4264,f116])).

fof(f4264,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_674 ),
    inference(resolution,[],[f4260,f115])).

fof(f4692,plain,
    ( spl7_732
    | ~ spl7_730 ),
    inference(avatar_split_clause,[],[f4676,f4672,f4690])).

fof(f4690,plain,
    ( spl7_732
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_732])])).

fof(f4672,plain,
    ( spl7_730
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_730])])).

fof(f4676,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_730 ),
    inference(superposition,[],[f145,f4673])).

fof(f4673,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_730 ),
    inference(avatar_component_clause,[],[f4672])).

fof(f4674,plain,
    ( spl7_730
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f952,f949,f4672])).

fof(f949,plain,
    ( spl7_166
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f952,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_166 ),
    inference(resolution,[],[f950,f362])).

fof(f950,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f949])).

fof(f4655,plain,
    ( spl7_728
    | ~ spl7_232 ),
    inference(avatar_split_clause,[],[f1343,f1339,f4653])).

fof(f4653,plain,
    ( spl7_728
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK6)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK6)))),u1_struct_0(sK3(sK3(sK3(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_728])])).

fof(f1339,plain,
    ( spl7_232
  <=> k3_struct_0(sK3(sK3(sK3(sK6)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_232])])).

fof(f1343,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK6)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK6)))),u1_struct_0(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_232 ),
    inference(superposition,[],[f108,f1340])).

fof(f1340,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK6)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK6)))))
    | ~ spl7_232 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f4639,plain,
    ( spl7_726
    | spl7_719 ),
    inference(avatar_split_clause,[],[f4620,f4589,f4637])).

fof(f4637,plain,
    ( spl7_726
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) = sK4(k3_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_726])])).

fof(f4620,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK6))),sK4(k3_struct_0(sK3(sK6)))) = sK4(k3_struct_0(sK3(sK6)))
    | ~ spl7_719 ),
    inference(resolution,[],[f4590,f858])).

fof(f4630,plain,
    ( spl7_724
    | ~ spl7_720 ),
    inference(avatar_split_clause,[],[f4621,f4595,f4628])).

fof(f4595,plain,
    ( spl7_720
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6))))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK6))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_720])])).

fof(f4621,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK3(sK6))),k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6))))
    | ~ spl7_720 ),
    inference(resolution,[],[f4596,f121])).

fof(f4596,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK3(sK6)))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)))) )
    | ~ spl7_720 ),
    inference(avatar_component_clause,[],[f4595])).

fof(f4619,plain,
    ( spl7_722
    | ~ spl7_20
    | ~ spl7_718 ),
    inference(avatar_split_clause,[],[f4606,f4592,f223,f4617])).

fof(f4617,plain,
    ( spl7_722
  <=> k3_struct_0(sK3(sK6)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_722])])).

fof(f4592,plain,
    ( spl7_718
  <=> v1_xboole_0(k3_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_718])])).

fof(f4606,plain,
    ( k3_struct_0(sK3(sK6)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_718 ),
    inference(forward_demodulation,[],[f4598,f224])).

fof(f4598,plain,
    ( k3_struct_0(sK3(sK6)) = k1_xboole_0
    | ~ spl7_718 ),
    inference(resolution,[],[f4593,f117])).

fof(f4593,plain,
    ( v1_xboole_0(k3_struct_0(sK3(sK6)))
    | ~ spl7_718 ),
    inference(avatar_component_clause,[],[f4592])).

fof(f4597,plain,
    ( spl7_718
    | spl7_720
    | ~ spl7_224 ),
    inference(avatar_split_clause,[],[f1331,f1300,f4595,f4592])).

fof(f1331,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6))))
        | v1_xboole_0(k3_struct_0(sK3(sK6)))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK6))) )
    | ~ spl7_224 ),
    inference(resolution,[],[f1301,f640])).

fof(f4505,plain,
    ( spl7_240
    | spl7_716
    | ~ spl7_714 ),
    inference(avatar_split_clause,[],[f4497,f4493,f4503,f1377])).

fof(f4493,plain,
    ( spl7_714
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK0))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_714])])).

fof(f4497,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) = sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | ~ spl7_714 ),
    inference(resolution,[],[f4494,f1209])).

fof(f4494,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK0))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_714 ),
    inference(avatar_component_clause,[],[f4493])).

fof(f4495,plain,
    ( spl7_406
    | spl7_714
    | ~ spl7_62
    | spl7_181 ),
    inference(avatar_split_clause,[],[f4468,f1019,f438,f4493,f2352])).

fof(f4468,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK0))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_62
    | ~ spl7_181 ),
    inference(subsumption_resolution,[],[f4467,f1020])).

fof(f4467,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_struct_0(sK0))
        | ~ m1_subset_1(X0,k3_struct_0(sK0))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f4442,f439])).

fof(f4442,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k3_struct_0(sK0))
        | v1_xboole_0(k6_partfun1(u1_struct_0(sK0)))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_62 ),
    inference(superposition,[],[f1207,f439])).

fof(f4435,plain,
    ( ~ spl7_8
    | spl7_423
    | ~ spl7_710 ),
    inference(avatar_contradiction_clause,[],[f4434])).

fof(f4434,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_423
    | ~ spl7_710 ),
    inference(subsumption_resolution,[],[f4428,f2426])).

fof(f2426,plain,
    ( u1_struct_0(sK5) != o_0_0_xboole_0
    | ~ spl7_423 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2425,plain,
    ( spl7_423
  <=> u1_struct_0(sK5) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_423])])).

fof(f4428,plain,
    ( u1_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_710 ),
    inference(resolution,[],[f4418,f350])).

fof(f4433,plain,
    ( ~ spl7_20
    | spl7_423
    | ~ spl7_710 ),
    inference(avatar_contradiction_clause,[],[f4432])).

fof(f4432,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_423
    | ~ spl7_710 ),
    inference(subsumption_resolution,[],[f4431,f2426])).

fof(f4431,plain,
    ( u1_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_710 ),
    inference(forward_demodulation,[],[f4424,f224])).

fof(f4424,plain,
    ( u1_struct_0(sK5) = k1_xboole_0
    | ~ spl7_710 ),
    inference(resolution,[],[f4418,f117])).

fof(f4422,plain,
    ( spl7_710
    | spl7_712
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f3231,f186,f4420,f4417])).

fof(f4420,plain,
    ( spl7_712
  <=> ! [X0] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0),u1_struct_0(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_712])])).

fof(f3231,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0),u1_struct_0(sK5))
        | v1_xboole_0(u1_struct_0(sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK5)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f1730,f187])).

fof(f1730,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0),u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1729,f110])).

fof(f1729,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0),u1_struct_0(X1))
      | ~ v1_funct_1(k3_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f1727,f112])).

fof(f1727,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k3_struct_0(X1),X0),u1_struct_0(X1))
      | ~ v1_funct_1(k3_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f135,f111])).

fof(f4410,plain,
    ( ~ spl7_707
    | spl7_708
    | ~ spl7_704 ),
    inference(avatar_split_clause,[],[f4398,f4393,f4408,f4405])).

fof(f4408,plain,
    ( spl7_708
  <=> ! [X4] : v1_relat_1(k7_relat_1(k3_struct_0(sK5),X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_708])])).

fof(f4393,plain,
    ( spl7_704
  <=> ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_704])])).

fof(f4398,plain,
    ( ! [X4] :
        ( v1_relat_1(k7_relat_1(k3_struct_0(sK5),X4))
        | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))) )
    | ~ spl7_704 ),
    inference(resolution,[],[f4394,f113])).

fof(f4394,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ spl7_704 ),
    inference(avatar_component_clause,[],[f4393])).

fof(f4395,plain,
    ( ~ spl7_701
    | spl7_704
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f4374,f665,f186,f4393,f4380])).

fof(f4374,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f4372,f666])).

fof(f4372,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(k3_struct_0(sK5),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(superposition,[],[f142,f4370])).

fof(f4370,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK5),k3_struct_0(sK5),X0) = k7_relat_1(k3_struct_0(sK5),X0)
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(resolution,[],[f2984,f666])).

fof(f4388,plain,
    ( ~ spl7_10
    | spl7_701 ),
    inference(avatar_contradiction_clause,[],[f4387])).

fof(f4387,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_701 ),
    inference(subsumption_resolution,[],[f4386,f187])).

fof(f4386,plain,
    ( ~ l1_struct_0(sK5)
    | ~ spl7_701 ),
    inference(resolution,[],[f4381,f110])).

fof(f4381,plain,
    ( ~ v1_funct_1(k3_struct_0(sK5))
    | ~ spl7_701 ),
    inference(avatar_component_clause,[],[f4380])).

fof(f4385,plain,
    ( ~ spl7_701
    | spl7_702
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f4375,f665,f186,f4383,f4380])).

fof(f4383,plain,
    ( spl7_702
  <=> ! [X1] : v1_funct_1(k7_relat_1(k3_struct_0(sK5),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_702])])).

fof(f4375,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK5),X1))
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(subsumption_resolution,[],[f4373,f666])).

fof(f4373,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(k3_struct_0(sK5),X1))
        | ~ m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
        | ~ v1_funct_1(k3_struct_0(sK5)) )
    | ~ spl7_10
    | ~ spl7_112 ),
    inference(superposition,[],[f141,f4370])).

fof(f4366,plain,
    ( spl7_698
    | ~ spl7_638 ),
    inference(avatar_split_clause,[],[f4356,f3964,f4364])).

fof(f3964,plain,
    ( spl7_638
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_638])])).

fof(f4356,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))
    | ~ spl7_638 ),
    inference(subsumption_resolution,[],[f4355,f3965])).

fof(f3965,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))
    | ~ spl7_638 ),
    inference(avatar_component_clause,[],[f3964])).

fof(f4355,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))
    | ~ spl7_638 ),
    inference(resolution,[],[f3969,f116])).

fof(f3969,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_638 ),
    inference(resolution,[],[f3965,f115])).

fof(f4351,plain,
    ( spl7_696
    | ~ spl7_636 ),
    inference(avatar_split_clause,[],[f4344,f3952,f4349])).

fof(f3952,plain,
    ( spl7_636
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_636])])).

fof(f4344,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))
    | ~ spl7_636 ),
    inference(subsumption_resolution,[],[f4343,f3953])).

fof(f3953,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))
    | ~ spl7_636 ),
    inference(avatar_component_clause,[],[f3952])).

fof(f4343,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))
    | ~ spl7_636 ),
    inference(resolution,[],[f3957,f116])).

fof(f3957,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_636 ),
    inference(resolution,[],[f3953,f115])).

fof(f4342,plain,
    ( spl7_694
    | spl7_507 ),
    inference(avatar_split_clause,[],[f4208,f3168,f4340])).

fof(f4208,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_507 ),
    inference(resolution,[],[f3169,f858])).

fof(f4335,plain,
    ( spl7_692
    | spl7_590
    | ~ spl7_8
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f1225,f566,f179,f3640,f4333])).

fof(f4333,plain,
    ( spl7_692
  <=> u1_struct_0(sK3(sK3(sK1))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_692])])).

fof(f3640,plain,
    ( spl7_590
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK3(sK3(sK1))))) = sK4(u1_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_590])])).

fof(f566,plain,
    ( spl7_92
  <=> k3_struct_0(sK3(sK3(sK1))) = k6_partfun1(u1_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1225,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK3(sK3(sK1))))) = sK4(u1_struct_0(sK3(sK3(sK1))))
    | u1_struct_0(sK3(sK3(sK1))) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_92 ),
    inference(superposition,[],[f889,f567])).

fof(f567,plain,
    ( k3_struct_0(sK3(sK3(sK1))) = k6_partfun1(u1_struct_0(sK3(sK3(sK1))))
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f566])).

fof(f4328,plain,
    ( ~ spl7_689
    | spl7_414
    | spl7_690
    | ~ spl7_242 ),
    inference(avatar_split_clause,[],[f1396,f1386,f4326,f2380,f4320])).

fof(f4320,plain,
    ( spl7_689
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_689])])).

fof(f4326,plain,
    ( spl7_690
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_690])])).

fof(f1396,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))))
    | ~ spl7_242 ),
    inference(resolution,[],[f1387,f531])).

fof(f4315,plain,
    ( spl7_684
    | ~ spl7_193
    | spl7_686
    | ~ spl7_390
    | ~ spl7_392 ),
    inference(avatar_split_clause,[],[f2290,f2283,f2232,f4313,f1090,f4310])).

fof(f4313,plain,
    ( spl7_686
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_686])])).

fof(f2290,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0))
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK3(sK0))) )
    | ~ spl7_390
    | ~ spl7_392 ),
    inference(subsumption_resolution,[],[f2287,f2233])).

fof(f2287,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3(sK0)))
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0))
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK3(sK0))) )
    | ~ spl7_392 ),
    inference(resolution,[],[f2284,f135])).

fof(f4305,plain,
    ( ~ spl7_681
    | spl7_406
    | spl7_682
    | ~ spl7_238 ),
    inference(avatar_split_clause,[],[f1381,f1371,f4303,f2352,f4297])).

fof(f4297,plain,
    ( spl7_681
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_681])])).

fof(f4303,plain,
    ( spl7_682
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_682])])).

fof(f1381,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))))
    | ~ spl7_238 ),
    inference(resolution,[],[f1372,f531])).

fof(f4292,plain,
    ( spl7_678
    | ~ spl7_88
    | ~ spl7_676 ),
    inference(avatar_split_clause,[],[f4274,f4269,f547,f4290])).

fof(f4290,plain,
    ( spl7_678
  <=> k3_struct_0(sK3(sK3(sK0))) = k6_partfun1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_678])])).

fof(f547,plain,
    ( spl7_88
  <=> k3_struct_0(sK3(sK3(sK0))) = k6_partfun1(u1_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f4269,plain,
    ( spl7_676
  <=> u1_struct_0(sK3(sK3(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_676])])).

fof(f4274,plain,
    ( k3_struct_0(sK3(sK3(sK0))) = k6_partfun1(o_0_0_xboole_0)
    | ~ spl7_88
    | ~ spl7_676 ),
    inference(superposition,[],[f548,f4270])).

fof(f4270,plain,
    ( u1_struct_0(sK3(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_676 ),
    inference(avatar_component_clause,[],[f4269])).

fof(f548,plain,
    ( k3_struct_0(sK3(sK3(sK0))) = k6_partfun1(u1_struct_0(sK3(sK3(sK0))))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f547])).

fof(f4271,plain,
    ( spl7_676
    | spl7_586
    | ~ spl7_8
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f1224,f547,f179,f3627,f4269])).

fof(f3627,plain,
    ( spl7_586
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK3(sK3(sK0))))) = sK4(u1_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_586])])).

fof(f1224,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK3(sK3(sK0))))) = sK4(u1_struct_0(sK3(sK3(sK0))))
    | u1_struct_0(sK3(sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_88 ),
    inference(superposition,[],[f889,f548])).

fof(f4261,plain,
    ( spl7_674
    | ~ spl7_606 ),
    inference(avatar_split_clause,[],[f4254,f3810,f4259])).

fof(f3810,plain,
    ( spl7_606
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_606])])).

fof(f4254,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))
    | ~ spl7_606 ),
    inference(subsumption_resolution,[],[f4253,f3811])).

fof(f3811,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))
    | ~ spl7_606 ),
    inference(avatar_component_clause,[],[f3810])).

fof(f4253,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))
    | ~ spl7_606 ),
    inference(resolution,[],[f3815,f116])).

fof(f3815,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_606 ),
    inference(resolution,[],[f3811,f115])).

fof(f4250,plain,
    ( spl7_670
    | spl7_672
    | ~ spl7_38
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f2100,f614,f306,f4248,f4242])).

fof(f4242,plain,
    ( spl7_670
  <=> v2_struct_0(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_670])])).

fof(f2100,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK6)),sK4(u1_struct_0(sK3(sK6)))) = sK4(u1_struct_0(sK3(sK6)))
    | v2_struct_0(sK3(sK6))
    | ~ spl7_38
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f2058,f615])).

fof(f2058,plain,
    ( v2_struct_0(sK3(sK6))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK6))),sK4(u1_struct_0(sK3(sK6)))) = sK4(u1_struct_0(sK3(sK6)))
    | ~ spl7_38 ),
    inference(resolution,[],[f1931,f307])).

fof(f1931,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k1_funct_1(k6_partfun1(u1_struct_0(X0)),sK4(u1_struct_0(X0))) = sK4(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f893,f114])).

fof(f893,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k1_funct_1(k6_partfun1(u1_struct_0(X9)),sK4(u1_struct_0(X9))) = sK4(u1_struct_0(X9))
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f858,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',fc2_struct_0)).

fof(f4215,plain,
    ( spl7_668
    | spl7_646
    | ~ spl7_8
    | ~ spl7_582 ),
    inference(avatar_split_clause,[],[f4039,f3611,f179,f4075,f4213])).

fof(f4213,plain,
    ( spl7_668
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_668])])).

fof(f4075,plain,
    ( spl7_646
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_646])])).

fof(f4039,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_8
    | ~ spl7_582 ),
    inference(superposition,[],[f3740,f3612])).

fof(f4205,plain,
    ( ~ spl7_8
    | spl7_383
    | ~ spl7_662 ),
    inference(avatar_contradiction_clause,[],[f4203])).

fof(f4203,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_383
    | ~ spl7_662 ),
    inference(resolution,[],[f4184,f121])).

fof(f4184,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_8
    | ~ spl7_383
    | ~ spl7_662 ),
    inference(subsumption_resolution,[],[f4183,f2176])).

fof(f4183,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_8
    | ~ spl7_662 ),
    inference(resolution,[],[f4172,f126])).

fof(f4172,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_8
    | ~ spl7_662 ),
    inference(resolution,[],[f4170,f559])).

fof(f559,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f134,f180])).

fof(f4170,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_662 ),
    inference(avatar_component_clause,[],[f4169])).

fof(f4169,plain,
    ( spl7_662
  <=> m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_662])])).

fof(f4202,plain,
    ( ~ spl7_667
    | spl7_545
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4201,f4127,f3431,f4195])).

fof(f4127,plain,
    ( spl7_656
  <=> k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_656])])).

fof(f4201,plain,
    ( ~ m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),o_0_0_xboole_0)
    | ~ spl7_545
    | ~ spl7_656 ),
    inference(forward_demodulation,[],[f3432,f4128])).

fof(f4128,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) = o_0_0_xboole_0
    | ~ spl7_656 ),
    inference(avatar_component_clause,[],[f4127])).

fof(f4200,plain,
    ( spl7_666
    | ~ spl7_544
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4140,f4127,f3434,f4198])).

fof(f4198,plain,
    ( spl7_666
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_666])])).

fof(f3434,plain,
    ( spl7_544
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_544])])).

fof(f4140,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),o_0_0_xboole_0)
    | ~ spl7_544
    | ~ spl7_656 ),
    inference(superposition,[],[f3435,f4128])).

fof(f3435,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_544 ),
    inference(avatar_component_clause,[],[f3434])).

fof(f4191,plain,
    ( spl7_664
    | ~ spl7_530
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4139,f4127,f3363,f4189])).

fof(f4139,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),o_0_0_xboole_0)
    | ~ spl7_530
    | ~ spl7_656 ),
    inference(superposition,[],[f3364,f4128])).

fof(f4171,plain,
    ( spl7_662
    | ~ spl7_298
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4130,f4127,f1684,f4169])).

fof(f4130,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_298
    | ~ spl7_656 ),
    inference(superposition,[],[f1685,f4128])).

fof(f4164,plain,
    ( ~ spl7_661
    | spl7_651
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4143,f4127,f4088,f4162])).

fof(f4162,plain,
    ( spl7_661
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_661])])).

fof(f4143,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl7_651
    | ~ spl7_656 ),
    inference(superposition,[],[f4089,f4128])).

fof(f4157,plain,
    ( ~ spl7_659
    | spl7_475
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4135,f4127,f2821,f4155])).

fof(f4135,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl7_475
    | ~ spl7_656 ),
    inference(superposition,[],[f2822,f4128])).

fof(f4148,plain,
    ( ~ spl7_165
    | spl7_473
    | ~ spl7_656 ),
    inference(avatar_split_clause,[],[f4134,f4127,f2805,f937])).

fof(f4134,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_473
    | ~ spl7_656 ),
    inference(superposition,[],[f2806,f4128])).

fof(f4129,plain,
    ( spl7_656
    | ~ spl7_20
    | ~ spl7_506 ),
    inference(avatar_split_clause,[],[f4112,f3171,f223,f4127])).

fof(f4112,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_506 ),
    inference(forward_demodulation,[],[f4105,f224])).

fof(f4105,plain,
    ( k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)) = k1_xboole_0
    | ~ spl7_506 ),
    inference(resolution,[],[f3172,f117])).

fof(f3172,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_506 ),
    inference(avatar_component_clause,[],[f3171])).

fof(f4104,plain,
    ( spl7_654
    | spl7_506
    | ~ spl7_644 ),
    inference(avatar_split_clause,[],[f4068,f4065,f3171,f4102])).

fof(f4102,plain,
    ( spl7_654
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_654])])).

fof(f4065,plain,
    ( spl7_644
  <=> m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_644])])).

fof(f4068,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),sK4(o_0_0_xboole_0)) = sK4(o_0_0_xboole_0)
    | ~ spl7_644 ),
    inference(resolution,[],[f4066,f601])).

fof(f4066,plain,
    ( m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_644 ),
    inference(avatar_component_clause,[],[f4065])).

fof(f4097,plain,
    ( spl7_652
    | spl7_646
    | ~ spl7_8
    | ~ spl7_582 ),
    inference(avatar_split_clause,[],[f4038,f3611,f179,f4075,f4095])).

fof(f4038,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_582 ),
    inference(superposition,[],[f889,f3612])).

fof(f4090,plain,
    ( ~ spl7_651
    | spl7_506
    | spl7_485
    | ~ spl7_644 ),
    inference(avatar_split_clause,[],[f4070,f4065,f2881,f3171,f4088])).

fof(f4070,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl7_485
    | ~ spl7_644 ),
    inference(subsumption_resolution,[],[f4069,f2882])).

fof(f4069,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl7_644 ),
    inference(resolution,[],[f4066,f531])).

fof(f4083,plain,
    ( spl7_646
    | spl7_648
    | ~ spl7_642 ),
    inference(avatar_split_clause,[],[f4059,f4053,f4081,f4075])).

fof(f4059,plain,
    ( v1_xboole_0(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_642 ),
    inference(resolution,[],[f4054,f601])).

fof(f4067,plain,
    ( spl7_644
    | ~ spl7_580
    | ~ spl7_582 ),
    inference(avatar_split_clause,[],[f4026,f3611,f3595,f4065])).

fof(f3595,plain,
    ( spl7_580
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_580])])).

fof(f4026,plain,
    ( m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_580
    | ~ spl7_582 ),
    inference(superposition,[],[f3596,f3612])).

fof(f3596,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_580 ),
    inference(avatar_component_clause,[],[f3595])).

fof(f4055,plain,
    ( spl7_642
    | ~ spl7_582 ),
    inference(avatar_split_clause,[],[f4036,f3611,f4053])).

fof(f4036,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_582 ),
    inference(superposition,[],[f121,f3612])).

fof(f4048,plain,
    ( ~ spl7_303
    | spl7_189
    | ~ spl7_582 ),
    inference(avatar_split_clause,[],[f4040,f3611,f1061,f1698])).

fof(f1698,plain,
    ( spl7_303
  <=> ~ v1_relat_1(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_303])])).

fof(f4040,plain,
    ( ~ v1_relat_1(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_189
    | ~ spl7_582 ),
    inference(subsumption_resolution,[],[f4027,f1062])).

fof(f4027,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_582 ),
    inference(superposition,[],[f400,f3612])).

fof(f4024,plain,
    ( spl7_640
    | spl7_383
    | spl7_579 ),
    inference(avatar_split_clause,[],[f4016,f3586,f2175,f4022])).

fof(f4022,plain,
    ( spl7_640
  <=> k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK3(sK0))),sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))) = sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_640])])).

fof(f3586,plain,
    ( spl7_579
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_579])])).

fof(f4016,plain,
    ( k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK3(sK0))),sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))) = sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_383
    | ~ spl7_579 ),
    inference(subsumption_resolution,[],[f4005,f2176])).

fof(f4005,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
    | k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK3(sK0))),sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))) = sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_579 ),
    inference(resolution,[],[f1211,f3587])).

fof(f3587,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_579 ),
    inference(avatar_component_clause,[],[f3586])).

fof(f3966,plain,
    ( spl7_638
    | ~ spl7_600 ),
    inference(avatar_split_clause,[],[f3959,f3691,f3964])).

fof(f3691,plain,
    ( spl7_600
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_600])])).

fof(f3959,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))
    | ~ spl7_600 ),
    inference(subsumption_resolution,[],[f3958,f3692])).

fof(f3692,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))
    | ~ spl7_600 ),
    inference(avatar_component_clause,[],[f3691])).

fof(f3958,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))
    | ~ spl7_600 ),
    inference(resolution,[],[f3696,f116])).

fof(f3696,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_600 ),
    inference(resolution,[],[f3692,f115])).

fof(f3954,plain,
    ( spl7_636
    | ~ spl7_598 ),
    inference(avatar_split_clause,[],[f3947,f3679,f3952])).

fof(f3679,plain,
    ( spl7_598
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_598])])).

fof(f3947,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))
    | ~ spl7_598 ),
    inference(subsumption_resolution,[],[f3946,f3680])).

fof(f3680,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))
    | ~ spl7_598 ),
    inference(avatar_component_clause,[],[f3679])).

fof(f3946,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))
    | ~ spl7_598 ),
    inference(resolution,[],[f3684,f116])).

fof(f3684,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_598 ),
    inference(resolution,[],[f3680,f115])).

fof(f3940,plain,
    ( spl7_634
    | ~ spl7_632 ),
    inference(avatar_split_clause,[],[f3929,f3925,f3938])).

fof(f3938,plain,
    ( spl7_634
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_634])])).

fof(f3925,plain,
    ( spl7_632
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_632])])).

fof(f3929,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_632 ),
    inference(superposition,[],[f145,f3926])).

fof(f3926,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_632 ),
    inference(avatar_component_clause,[],[f3925])).

fof(f3927,plain,
    ( spl7_632
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f823,f820,f3925])).

fof(f820,plain,
    ( spl7_144
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f823,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_144 ),
    inference(resolution,[],[f821,f362])).

fof(f821,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_144 ),
    inference(avatar_component_clause,[],[f820])).

fof(f3918,plain,
    ( spl7_630
    | ~ spl7_628 ),
    inference(avatar_split_clause,[],[f3907,f3903,f3916])).

fof(f3916,plain,
    ( spl7_630
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_630])])).

fof(f3903,plain,
    ( spl7_628
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_628])])).

fof(f3907,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_628 ),
    inference(superposition,[],[f145,f3904])).

fof(f3904,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_628 ),
    inference(avatar_component_clause,[],[f3903])).

fof(f3905,plain,
    ( spl7_628
    | ~ spl7_142 ),
    inference(avatar_split_clause,[],[f812,f809,f3903])).

fof(f809,plain,
    ( spl7_142
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f812,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_142 ),
    inference(resolution,[],[f810,f362])).

fof(f810,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_142 ),
    inference(avatar_component_clause,[],[f809])).

fof(f3898,plain,
    ( spl7_626
    | ~ spl7_18
    | ~ spl7_46
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f1491,f983,f346,f214,f3896])).

fof(f3896,plain,
    ( spl7_626
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_626])])).

fof(f346,plain,
    ( spl7_46
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f983,plain,
    ( spl7_174
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f1491,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_46
    | ~ spl7_174 ),
    inference(subsumption_resolution,[],[f1472,f347])).

fof(f347,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f346])).

fof(f1472,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl7_18
    | ~ spl7_174 ),
    inference(resolution,[],[f1454,f984])).

fof(f984,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_174 ),
    inference(avatar_component_clause,[],[f983])).

fof(f3891,plain,
    ( spl7_624
    | ~ spl7_18
    | ~ spl7_106
    | ~ spl7_378 ),
    inference(avatar_split_clause,[],[f2161,f2157,f632,f214,f3889])).

fof(f3889,plain,
    ( spl7_624
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_624])])).

fof(f632,plain,
    ( spl7_106
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f2157,plain,
    ( spl7_378
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_378])])).

fof(f2161,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_106
    | ~ spl7_378 ),
    inference(subsumption_resolution,[],[f2160,f633])).

fof(f633,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK6)))))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f632])).

fof(f2160,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK6)))))
    | ~ spl7_18
    | ~ spl7_378 ),
    inference(resolution,[],[f2158,f1454])).

fof(f2158,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_378 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f3884,plain,
    ( spl7_622
    | ~ spl7_18
    | ~ spl7_44
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f1490,f967,f336,f214,f3882])).

fof(f3882,plain,
    ( spl7_622
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_622])])).

fof(f336,plain,
    ( spl7_44
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f967,plain,
    ( spl7_170
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f1490,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_44
    | ~ spl7_170 ),
    inference(subsumption_resolution,[],[f1471,f337])).

fof(f337,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f336])).

fof(f1471,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl7_18
    | ~ spl7_170 ),
    inference(resolution,[],[f1454,f968])).

fof(f968,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_170 ),
    inference(avatar_component_clause,[],[f967])).

fof(f3877,plain,
    ( spl7_620
    | spl7_615 ),
    inference(avatar_split_clause,[],[f3868,f3839,f3875])).

fof(f3875,plain,
    ( spl7_620
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) = sK4(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_620])])).

fof(f3868,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK3(sK1)))),sK4(k3_struct_0(sK3(sK3(sK1))))) = sK4(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_615 ),
    inference(resolution,[],[f3840,f858])).

fof(f3867,plain,
    ( spl7_618
    | ~ spl7_20
    | ~ spl7_614 ),
    inference(avatar_split_clause,[],[f3855,f3842,f223,f3865])).

fof(f3865,plain,
    ( spl7_618
  <=> k3_struct_0(sK3(sK3(sK1))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_618])])).

fof(f3842,plain,
    ( spl7_614
  <=> v1_xboole_0(k3_struct_0(sK3(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_614])])).

fof(f3855,plain,
    ( k3_struct_0(sK3(sK3(sK1))) = o_0_0_xboole_0
    | ~ spl7_20
    | ~ spl7_614 ),
    inference(forward_demodulation,[],[f3848,f224])).

fof(f3848,plain,
    ( k3_struct_0(sK3(sK3(sK1))) = k1_xboole_0
    | ~ spl7_614 ),
    inference(resolution,[],[f3843,f117])).

fof(f3843,plain,
    ( v1_xboole_0(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_614 ),
    inference(avatar_component_clause,[],[f3842])).

fof(f3847,plain,
    ( spl7_614
    | spl7_616
    | ~ spl7_218 ),
    inference(avatar_split_clause,[],[f1268,f1261,f3845,f3842])).

fof(f3845,plain,
    ( spl7_616
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1)))))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK3(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_616])])).

fof(f1268,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1)))))
        | v1_xboole_0(k3_struct_0(sK3(sK3(sK1))))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK3(sK1)))) )
    | ~ spl7_218 ),
    inference(resolution,[],[f1262,f640])).

fof(f3835,plain,
    ( spl7_610
    | spl7_612
    | ~ spl7_216 ),
    inference(avatar_split_clause,[],[f1253,f1250,f3833,f3830])).

fof(f3830,plain,
    ( spl7_610
  <=> v1_xboole_0(k3_struct_0(sK3(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_610])])).

fof(f3833,plain,
    ( spl7_612
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0)))))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK3(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_612])])).

fof(f1253,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0)))))
        | v1_xboole_0(k3_struct_0(sK3(sK3(sK0))))
        | ~ m1_subset_1(X0,k3_struct_0(sK3(sK3(sK0)))) )
    | ~ spl7_216 ),
    inference(resolution,[],[f1251,f640])).

fof(f3822,plain,
    ( spl7_608
    | spl7_448
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f1665,f1660,f2700,f3820])).

fof(f3820,plain,
    ( spl7_608
  <=> k4_tmap_1(sK0,sK1) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_608])])).

fof(f2700,plain,
    ( spl7_448
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_448])])).

fof(f1665,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k4_tmap_1(sK0,sK1) = k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),k4_tmap_1(sK0,sK1))
    | ~ spl7_292 ),
    inference(resolution,[],[f1661,f601])).

fof(f3812,plain,
    ( spl7_606
    | ~ spl7_430 ),
    inference(avatar_split_clause,[],[f3805,f2544,f3810])).

fof(f2544,plain,
    ( spl7_430
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_430])])).

fof(f3805,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))
    | ~ spl7_430 ),
    inference(subsumption_resolution,[],[f3804,f2545])).

fof(f2545,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))
    | ~ spl7_430 ),
    inference(avatar_component_clause,[],[f2544])).

fof(f3804,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))
    | ~ spl7_430 ),
    inference(resolution,[],[f2549,f116])).

fof(f2549,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_430 ),
    inference(resolution,[],[f2545,f115])).

fof(f3801,plain,
    ( spl7_604
    | ~ spl7_602 ),
    inference(avatar_split_clause,[],[f3790,f3786,f3799])).

fof(f3786,plain,
    ( spl7_602
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_602])])).

fof(f3790,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_602 ),
    inference(superposition,[],[f145,f3787])).

fof(f3787,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_602 ),
    inference(avatar_component_clause,[],[f3786])).

fof(f3788,plain,
    ( spl7_602
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f801,f798,f3786])).

fof(f801,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_140 ),
    inference(resolution,[],[f799,f362])).

fof(f3693,plain,
    ( spl7_600
    | ~ spl7_574 ),
    inference(avatar_split_clause,[],[f3686,f3572,f3691])).

fof(f3572,plain,
    ( spl7_574
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_574])])).

fof(f3686,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))
    | ~ spl7_574 ),
    inference(subsumption_resolution,[],[f3685,f3573])).

fof(f3573,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))
    | ~ spl7_574 ),
    inference(avatar_component_clause,[],[f3572])).

fof(f3685,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))
    | ~ spl7_574 ),
    inference(resolution,[],[f3577,f116])).

fof(f3577,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_574 ),
    inference(resolution,[],[f3573,f115])).

fof(f3681,plain,
    ( spl7_598
    | ~ spl7_572 ),
    inference(avatar_split_clause,[],[f3674,f3557,f3679])).

fof(f3557,plain,
    ( spl7_572
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_572])])).

fof(f3674,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))
    | ~ spl7_572 ),
    inference(subsumption_resolution,[],[f3673,f3558])).

fof(f3558,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))
    | ~ spl7_572 ),
    inference(avatar_component_clause,[],[f3557])).

fof(f3673,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))
    | ~ spl7_572 ),
    inference(resolution,[],[f3565,f116])).

fof(f3565,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_572 ),
    inference(resolution,[],[f3558,f115])).

fof(f3666,plain,
    ( spl7_596
    | ~ spl7_172 ),
    inference(avatar_split_clause,[],[f977,f974,f3664])).

fof(f3664,plain,
    ( spl7_596
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK1))))),u1_struct_0(sK3(sK3(sK3(sK3(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_596])])).

fof(f974,plain,
    ( spl7_172
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK1))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f977,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK1))))),u1_struct_0(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_172 ),
    inference(superposition,[],[f108,f975])).

fof(f975,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK1))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_172 ),
    inference(avatar_component_clause,[],[f974])).

fof(f3655,plain,
    ( spl7_594
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f961,f958,f3653])).

fof(f3653,plain,
    ( spl7_594
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK0))))),u1_struct_0(sK3(sK3(sK3(sK3(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_594])])).

fof(f958,plain,
    ( spl7_168
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK0))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f961,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK3(sK0))))),u1_struct_0(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_168 ),
    inference(superposition,[],[f108,f959])).

fof(f959,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK0))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_168 ),
    inference(avatar_component_clause,[],[f958])).

fof(f3648,plain,
    ( spl7_482
    | ~ spl7_486 ),
    inference(avatar_split_clause,[],[f3354,f2900,f2878])).

fof(f2878,plain,
    ( spl7_482
  <=> m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_482])])).

fof(f2900,plain,
    ( spl7_486
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,sK4(o_0_0_xboole_0))
        | m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_486])])).

fof(f3354,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_486 ),
    inference(resolution,[],[f2901,f121])).

fof(f2901,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,sK4(o_0_0_xboole_0))
        | m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) )
    | ~ spl7_486 ),
    inference(avatar_component_clause,[],[f2900])).

fof(f3646,plain,
    ( spl7_478
    | spl7_592
    | ~ spl7_18
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3021,f2808,f214,f3644,f2865])).

fof(f2865,plain,
    ( spl7_478
  <=> m1_subset_1(sK2,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_478])])).

fof(f3021,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(u1_struct_0(sK1),X14)
        | m1_subset_1(sK2,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(X14),sK4(X14)) = sK4(X14) )
    | ~ spl7_18
    | ~ spl7_472 ),
    inference(superposition,[],[f639,f2811])).

fof(f2811,plain,
    ( ! [X0] :
        ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) = X0
        | k1_funct_1(k6_partfun1(X0),sK4(X0)) = sK4(X0) )
    | ~ spl7_472 ),
    inference(resolution,[],[f2809,f890])).

fof(f2809,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_472 ),
    inference(avatar_component_clause,[],[f2808])).

fof(f3642,plain,
    ( spl7_588
    | spl7_590
    | ~ spl7_36
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f2067,f566,f296,f3640,f3634])).

fof(f3634,plain,
    ( spl7_588
  <=> v2_struct_0(sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_588])])).

fof(f2067,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK4(u1_struct_0(sK3(sK3(sK1))))) = sK4(u1_struct_0(sK3(sK3(sK1))))
    | v2_struct_0(sK3(sK3(sK1)))
    | ~ spl7_36
    | ~ spl7_92 ),
    inference(forward_demodulation,[],[f2025,f567])).

fof(f2025,plain,
    ( v2_struct_0(sK3(sK3(sK1)))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK3(sK1)))),sK4(u1_struct_0(sK3(sK3(sK1))))) = sK4(u1_struct_0(sK3(sK3(sK1))))
    | ~ spl7_36 ),
    inference(resolution,[],[f1931,f297])).

fof(f3629,plain,
    ( spl7_584
    | spl7_586
    | ~ spl7_34
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f2066,f547,f286,f3627,f3621])).

fof(f3621,plain,
    ( spl7_584
  <=> v2_struct_0(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_584])])).

fof(f2066,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK4(u1_struct_0(sK3(sK3(sK0))))) = sK4(u1_struct_0(sK3(sK3(sK0))))
    | v2_struct_0(sK3(sK3(sK0)))
    | ~ spl7_34
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2024,f548])).

fof(f2024,plain,
    ( v2_struct_0(sK3(sK3(sK0)))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK3(sK0)))),sK4(u1_struct_0(sK3(sK3(sK0))))) = sK4(u1_struct_0(sK3(sK3(sK0))))
    | ~ spl7_34 ),
    inference(resolution,[],[f1931,f287])).

fof(f3613,plain,
    ( spl7_582
    | ~ spl7_8
    | ~ spl7_578 ),
    inference(avatar_split_clause,[],[f3600,f3589,f179,f3611])).

fof(f3589,plain,
    ( spl7_578
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_578])])).

fof(f3600,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))
    | ~ spl7_8
    | ~ spl7_578 ),
    inference(resolution,[],[f3590,f350])).

fof(f3590,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_578 ),
    inference(avatar_component_clause,[],[f3589])).

fof(f3597,plain,
    ( spl7_578
    | spl7_580
    | ~ spl7_384 ),
    inference(avatar_split_clause,[],[f3358,f2181,f3595,f3589])).

fof(f2181,plain,
    ( spl7_384
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_384])])).

fof(f3358,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0))))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(k4_tmap_1(sK0,sK3(sK0)))))
    | ~ spl7_384 ),
    inference(resolution,[],[f2182,f1209])).

fof(f2182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k4_tmap_1(sK0,sK3(sK0)))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) )
    | ~ spl7_384 ),
    inference(avatar_component_clause,[],[f2181])).

fof(f3584,plain,
    ( ~ spl7_577
    | spl7_448
    | spl7_304
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f1666,f1660,f1708,f2700,f3582])).

fof(f3582,plain,
    ( spl7_577
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_577])])).

fof(f1708,plain,
    ( spl7_304
  <=> v1_xboole_0(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_304])])).

fof(f1666,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),k4_tmap_1(sK0,sK1))
    | ~ spl7_292 ),
    inference(resolution,[],[f1661,f531])).

fof(f3574,plain,
    ( spl7_574
    | ~ spl7_420 ),
    inference(avatar_split_clause,[],[f3567,f2407,f3572])).

fof(f2407,plain,
    ( spl7_420
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_420])])).

fof(f3567,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))
    | ~ spl7_420 ),
    inference(subsumption_resolution,[],[f3566,f2408])).

fof(f2408,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))
    | ~ spl7_420 ),
    inference(avatar_component_clause,[],[f2407])).

fof(f3566,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))
    | ~ spl7_420 ),
    inference(resolution,[],[f2412,f116])).

fof(f2412,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_420 ),
    inference(resolution,[],[f2408,f115])).

fof(f3559,plain,
    ( spl7_572
    | ~ spl7_418 ),
    inference(avatar_split_clause,[],[f3552,f2395,f3557])).

fof(f2395,plain,
    ( spl7_418
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_418])])).

fof(f3552,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))
    | ~ spl7_418 ),
    inference(subsumption_resolution,[],[f3551,f2396])).

fof(f2396,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))
    | ~ spl7_418 ),
    inference(avatar_component_clause,[],[f2395])).

fof(f3551,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))
    | ~ spl7_418 ),
    inference(resolution,[],[f2400,f116])).

fof(f2400,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_418 ),
    inference(resolution,[],[f2396,f115])).

fof(f3547,plain,
    ( spl7_570
    | ~ spl7_568 ),
    inference(avatar_split_clause,[],[f3534,f3530,f3545])).

fof(f3545,plain,
    ( spl7_570
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_570])])).

fof(f3530,plain,
    ( spl7_568
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_568])])).

fof(f3534,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_568 ),
    inference(superposition,[],[f145,f3531])).

fof(f3531,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_568 ),
    inference(avatar_component_clause,[],[f3530])).

fof(f3532,plain,
    ( spl7_568
    | ~ spl7_110 ),
    inference(avatar_split_clause,[],[f659,f656,f3530])).

fof(f656,plain,
    ( spl7_110
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f659,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_110 ),
    inference(resolution,[],[f657,f362])).

fof(f657,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f656])).

fof(f3522,plain,
    ( spl7_566
    | ~ spl7_564 ),
    inference(avatar_split_clause,[],[f3509,f3505,f3520])).

fof(f3520,plain,
    ( spl7_566
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_566])])).

fof(f3505,plain,
    ( spl7_564
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_564])])).

fof(f3509,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_564 ),
    inference(superposition,[],[f145,f3506])).

fof(f3506,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_564 ),
    inference(avatar_component_clause,[],[f3505])).

fof(f3507,plain,
    ( spl7_564
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f648,f645,f3505])).

fof(f645,plain,
    ( spl7_108
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f648,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_108 ),
    inference(resolution,[],[f646,f362])).

fof(f646,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f645])).

fof(f3500,plain,
    ( spl7_562
    | ~ spl7_18
    | ~ spl7_42
    | ~ spl7_138 ),
    inference(avatar_split_clause,[],[f1489,f789,f326,f214,f3498])).

fof(f3498,plain,
    ( spl7_562
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_562])])).

fof(f1489,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_42
    | ~ spl7_138 ),
    inference(subsumption_resolution,[],[f1470,f327])).

fof(f1470,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK1)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl7_18
    | ~ spl7_138 ),
    inference(resolution,[],[f1454,f790])).

fof(f3493,plain,
    ( spl7_560
    | ~ spl7_104
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3078,f2808,f2232,f1061,f623,f3491])).

fof(f3491,plain,
    ( spl7_560
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK6)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK6))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_560])])).

fof(f623,plain,
    ( spl7_104
  <=> v1_relat_1(k3_struct_0(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f3078,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK6)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK6))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK6))))
    | ~ spl7_104
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f624])).

fof(f624,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK6)))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f623])).

fof(f3060,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(X7)
        | k1_funct_1(k6_partfun1(k1_zfmisc_1(X7)),sK4(k1_zfmisc_1(X7))) = sK4(k1_zfmisc_1(X7)) )
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(subsumption_resolution,[],[f3053,f1062])).

fof(f3053,plain,
    ( ! [X7] :
        ( k1_funct_1(k6_partfun1(k1_zfmisc_1(X7)),sK4(k1_zfmisc_1(X7))) = sK4(k1_zfmisc_1(X7))
        | v1_relat_1(o_0_0_xboole_0)
        | ~ v1_relat_1(X7) )
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3015,f113])).

fof(f3015,plain,
    ( ! [X4] :
        ( m1_subset_1(o_0_0_xboole_0,X4)
        | k1_funct_1(k6_partfun1(X4),sK4(X4)) = sK4(X4) )
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(superposition,[],[f2233,f2811])).

fof(f3486,plain,
    ( spl7_558
    | ~ spl7_76
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3064,f2808,f2232,f1061,f495,f3484])).

fof(f3484,plain,
    ( spl7_558
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK1)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK1))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_558])])).

fof(f3064,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK1)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK1))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK1))))
    | ~ spl7_76
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f496])).

fof(f3479,plain,
    ( spl7_556
    | ~ spl7_72
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3063,f2808,f2232,f1061,f479,f3477])).

fof(f3477,plain,
    ( spl7_556
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK0))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_556])])).

fof(f3063,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK3(sK0)))),sK4(k1_zfmisc_1(k3_struct_0(sK3(sK0))))) = sK4(k1_zfmisc_1(k3_struct_0(sK3(sK0))))
    | ~ spl7_72
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f480])).

fof(f3472,plain,
    ( spl7_554
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_234 ),
    inference(avatar_split_clause,[],[f1494,f1349,f538,f214,f3470])).

fof(f3470,plain,
    ( spl7_554
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK6)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK6)))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_554])])).

fof(f538,plain,
    ( spl7_86
  <=> l1_pre_topc(sK3(sK3(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f1349,plain,
    ( spl7_234
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f1494,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK6)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK6)))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_234 ),
    inference(subsumption_resolution,[],[f1475,f539])).

fof(f539,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK6))))
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f538])).

fof(f1475,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK6)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK6)))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK6))))
    | ~ spl7_18
    | ~ spl7_234 ),
    inference(resolution,[],[f1454,f1350])).

fof(f1350,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK6)))))
    | ~ spl7_234 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f3465,plain,
    ( spl7_552
    | ~ spl7_18
    | ~ spl7_40
    | ~ spl7_134 ),
    inference(avatar_split_clause,[],[f1488,f773,f316,f214,f3463])).

fof(f3463,plain,
    ( spl7_552
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_552])])).

fof(f1488,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_40
    | ~ spl7_134 ),
    inference(subsumption_resolution,[],[f1469,f317])).

fof(f1469,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK3(sK0)))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl7_18
    | ~ spl7_134 ),
    inference(resolution,[],[f1454,f774])).

fof(f3458,plain,
    ( spl7_550
    | spl7_415 ),
    inference(avatar_split_clause,[],[f3282,f2377,f3456])).

fof(f3456,plain,
    ( spl7_550
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_550])])).

fof(f3282,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_415 ),
    inference(resolution,[],[f2378,f858])).

fof(f3449,plain,
    ( spl7_548
    | spl7_532
    | ~ spl7_8
    | ~ spl7_230 ),
    inference(avatar_split_clause,[],[f3301,f1326,f179,f3392,f3447])).

fof(f3392,plain,
    ( spl7_532
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_532])])).

fof(f3301,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_230 ),
    inference(superposition,[],[f889,f1327])).

fof(f3442,plain,
    ( spl7_416
    | spl7_546
    | ~ spl7_474
    | ~ spl7_514 ),
    inference(avatar_split_clause,[],[f3248,f3245,f2824,f3440,f2386])).

fof(f3440,plain,
    ( spl7_546
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,sK4(k3_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_546])])).

fof(f2824,plain,
    ( spl7_474
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_474])])).

fof(f3245,plain,
    ( spl7_514
  <=> m1_subset_1(sK4(k3_struct_0(sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_514])])).

fof(f3248,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | v1_xboole_0(sK4(k3_struct_0(sK1)))
        | ~ m1_subset_1(X0,sK4(k3_struct_0(sK1))) )
    | ~ spl7_474
    | ~ spl7_514 ),
    inference(resolution,[],[f3246,f2836])).

fof(f2836,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,o_0_0_xboole_0)
        | m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,X5) )
    | ~ spl7_474 ),
    inference(superposition,[],[f640,f2825])).

fof(f2825,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl7_474 ),
    inference(avatar_component_clause,[],[f2824])).

fof(f3246,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl7_514 ),
    inference(avatar_component_clause,[],[f3245])).

fof(f3436,plain,
    ( spl7_542
    | spl7_544
    | ~ spl7_486 ),
    inference(avatar_split_clause,[],[f3355,f2900,f3434,f3428])).

fof(f3355,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0)))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl7_486 ),
    inference(resolution,[],[f2901,f1209])).

fof(f3423,plain,
    ( spl7_540
    | spl7_383 ),
    inference(avatar_split_clause,[],[f3281,f2175,f3421])).

fof(f3421,plain,
    ( spl7_540
  <=> k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) = sK4(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_540])])).

fof(f3281,plain,
    ( k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK3(sK0))),sK4(k4_tmap_1(sK0,sK3(sK0)))) = sK4(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_383 ),
    inference(resolution,[],[f2176,f858])).

fof(f3416,plain,
    ( spl7_538
    | spl7_416
    | ~ spl7_518 ),
    inference(avatar_split_clause,[],[f3408,f3259,f2386,f3414])).

fof(f3414,plain,
    ( spl7_538
  <=> k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_538])])).

fof(f3408,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK1))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_518 ),
    inference(resolution,[],[f3260,f601])).

fof(f3407,plain,
    ( spl7_536
    | ~ spl7_390
    | ~ spl7_472
    | spl7_519 ),
    inference(avatar_split_clause,[],[f3265,f3262,f2808,f2232,f3405])).

fof(f3262,plain,
    ( spl7_519
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_519])])).

fof(f3265,plain,
    ( k1_funct_1(k6_partfun1(sK4(k3_struct_0(sK1))),sK4(sK4(k3_struct_0(sK1)))) = sK4(sK4(k3_struct_0(sK1)))
    | ~ spl7_390
    | ~ spl7_472
    | ~ spl7_519 ),
    inference(resolution,[],[f3263,f3015])).

fof(f3263,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK1)))
    | ~ spl7_519 ),
    inference(avatar_component_clause,[],[f3262])).

fof(f3400,plain,
    ( spl7_532
    | spl7_534
    | ~ spl7_524 ),
    inference(avatar_split_clause,[],[f3324,f3319,f3398,f3392])).

fof(f3324,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_524 ),
    inference(resolution,[],[f3320,f601])).

fof(f3387,plain,
    ( spl7_484
    | spl7_486
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2981,f2824,f2900,f2884])).

fof(f2884,plain,
    ( spl7_484
  <=> v1_xboole_0(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_484])])).

fof(f2981,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | v1_xboole_0(sK4(o_0_0_xboole_0))
        | ~ m1_subset_1(X6,sK4(o_0_0_xboole_0)) )
    | ~ spl7_474 ),
    inference(resolution,[],[f2836,f121])).

fof(f3365,plain,
    ( spl7_530
    | ~ spl7_384 ),
    inference(avatar_split_clause,[],[f3357,f2181,f3363])).

fof(f3357,plain,
    ( m1_subset_1(sK4(k4_tmap_1(sK0,sK3(sK0))),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_384 ),
    inference(resolution,[],[f2182,f121])).

fof(f3352,plain,
    ( spl7_528
    | spl7_485 ),
    inference(avatar_split_clause,[],[f3275,f2881,f3350])).

fof(f3350,plain,
    ( spl7_528
  <=> k1_funct_1(k6_partfun1(sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_528])])).

fof(f3275,plain,
    ( k1_funct_1(k6_partfun1(sK4(o_0_0_xboole_0)),sK4(sK4(o_0_0_xboole_0))) = sK4(sK4(o_0_0_xboole_0))
    | ~ spl7_485 ),
    inference(resolution,[],[f2882,f858])).

fof(f3335,plain,
    ( spl7_526
    | ~ spl7_230
    | ~ spl7_288 ),
    inference(avatar_split_clause,[],[f3294,f1635,f1326,f3333])).

fof(f1635,plain,
    ( spl7_288
  <=> k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_288])])).

fof(f3294,plain,
    ( k1_funct_1(k6_partfun1(o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_230
    | ~ spl7_288 ),
    inference(superposition,[],[f1636,f1327])).

fof(f1636,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_288 ),
    inference(avatar_component_clause,[],[f1635])).

fof(f3321,plain,
    ( spl7_524
    | ~ spl7_230 ),
    inference(avatar_split_clause,[],[f3299,f1326,f3319])).

fof(f3299,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_230 ),
    inference(superposition,[],[f121,f1327])).

fof(f3314,plain,
    ( ~ spl7_523
    | spl7_189
    | ~ spl7_230 ),
    inference(avatar_split_clause,[],[f3305,f1326,f1061,f3312])).

fof(f3312,plain,
    ( spl7_523
  <=> ~ v1_relat_1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_523])])).

fof(f3305,plain,
    ( ~ v1_relat_1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_189
    | ~ spl7_230 ),
    inference(subsumption_resolution,[],[f3298,f1062])).

fof(f3298,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_relat_1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_230 ),
    inference(superposition,[],[f400,f1327])).

fof(f3289,plain,
    ( spl7_520
    | ~ spl7_298
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2830,f2824,f1684,f3287])).

fof(f3287,plain,
    ( spl7_520
  <=> m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_520])])).

fof(f2830,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),o_0_0_xboole_0)
    | ~ spl7_298
    | ~ spl7_474 ),
    inference(superposition,[],[f1685,f2825])).

fof(f3280,plain,
    ( ~ spl7_8
    | spl7_195
    | ~ spl7_512 ),
    inference(avatar_contradiction_clause,[],[f3278])).

fof(f3278,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_195
    | ~ spl7_512 ),
    inference(resolution,[],[f3271,f121])).

fof(f3271,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_195
    | ~ spl7_512 ),
    inference(subsumption_resolution,[],[f3240,f1103])).

fof(f3240,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_struct_0(sK1))
        | ~ m1_subset_1(X0,k3_struct_0(sK1)) )
    | ~ spl7_8
    | ~ spl7_512 ),
    inference(resolution,[],[f3234,f126])).

fof(f3234,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_512 ),
    inference(resolution,[],[f3229,f559])).

fof(f3229,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_512 ),
    inference(avatar_component_clause,[],[f3228])).

fof(f3228,plain,
    ( spl7_512
  <=> m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_512])])).

fof(f3270,plain,
    ( spl7_195
    | ~ spl7_282
    | ~ spl7_284
    | ~ spl7_512 ),
    inference(avatar_contradiction_clause,[],[f3268])).

fof(f3268,plain,
    ( $false
    | ~ spl7_195
    | ~ spl7_282
    | ~ spl7_284
    | ~ spl7_512 ),
    inference(resolution,[],[f3239,f121])).

fof(f3239,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k3_struct_0(sK1))
    | ~ spl7_195
    | ~ spl7_282
    | ~ spl7_284
    | ~ spl7_512 ),
    inference(subsumption_resolution,[],[f3233,f1103])).

fof(f3233,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_struct_0(sK1))
        | ~ m1_subset_1(X0,k3_struct_0(sK1)) )
    | ~ spl7_282
    | ~ spl7_284
    | ~ spl7_512 ),
    inference(resolution,[],[f3229,f1641])).

fof(f1641,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl7_282
    | ~ spl7_284 ),
    inference(forward_demodulation,[],[f1639,f1611])).

fof(f1611,plain,
    ( o_0_0_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_284 ),
    inference(avatar_component_clause,[],[f1610])).

fof(f1610,plain,
    ( spl7_284
  <=> o_0_0_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_284])])).

fof(f1639,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl7_282 ),
    inference(resolution,[],[f1596,f126])).

fof(f1596,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))) )
    | ~ spl7_282 ),
    inference(resolution,[],[f1590,f134])).

fof(f1590,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl7_282 ),
    inference(avatar_component_clause,[],[f1589])).

fof(f1589,plain,
    ( spl7_282
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f3264,plain,
    ( ~ spl7_519
    | spl7_413
    | ~ spl7_510 ),
    inference(avatar_split_clause,[],[f3201,f3194,f2374,f3262])).

fof(f2374,plain,
    ( spl7_413
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK4(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_413])])).

fof(f3194,plain,
    ( spl7_510
  <=> k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_510])])).

fof(f3201,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(k3_struct_0(sK1)))
    | ~ spl7_413
    | ~ spl7_510 ),
    inference(superposition,[],[f2375,f3195])).

fof(f3195,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl7_510 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f2375,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_413 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f3257,plain,
    ( ~ spl7_517
    | spl7_401
    | ~ spl7_510 ),
    inference(avatar_split_clause,[],[f3200,f3194,f2333,f3255])).

fof(f3255,plain,
    ( spl7_517
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_517])])).

fof(f2333,plain,
    ( spl7_401
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_401])])).

fof(f3200,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k3_struct_0(sK1))
    | ~ spl7_401
    | ~ spl7_510 ),
    inference(superposition,[],[f2334,f3195])).

fof(f2334,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k3_struct_0(sK1))
    | ~ spl7_401 ),
    inference(avatar_component_clause,[],[f2333])).

fof(f3247,plain,
    ( spl7_514
    | ~ spl7_200
    | ~ spl7_510 ),
    inference(avatar_split_clause,[],[f3198,f3194,f1132,f3245])).

fof(f3198,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK1)),o_0_0_xboole_0)
    | ~ spl7_200
    | ~ spl7_510 ),
    inference(superposition,[],[f1133,f3195])).

fof(f3230,plain,
    ( spl7_512
    | ~ spl7_84
    | ~ spl7_510 ),
    inference(avatar_split_clause,[],[f3197,f3194,f526,f3228])).

fof(f3197,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_84
    | ~ spl7_510 ),
    inference(superposition,[],[f527,f3195])).

fof(f3196,plain,
    ( spl7_510
    | ~ spl7_8
    | ~ spl7_414 ),
    inference(avatar_split_clause,[],[f3183,f2380,f179,f3194])).

fof(f3183,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_414 ),
    inference(resolution,[],[f2381,f350])).

fof(f2381,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_414 ),
    inference(avatar_component_clause,[],[f2380])).

fof(f3180,plain,
    ( spl7_508
    | spl7_414
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f1164,f1132,f2380,f3178])).

fof(f3178,plain,
    ( spl7_508
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) = sK4(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_508])])).

fof(f1164,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK4(k3_struct_0(sK1))) = sK4(k3_struct_0(sK1))
    | ~ spl7_200 ),
    inference(resolution,[],[f1133,f601])).

fof(f3173,plain,
    ( spl7_504
    | spl7_506
    | ~ spl7_490 ),
    inference(avatar_split_clause,[],[f2938,f2935,f3171,f3165])).

fof(f2938,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_490 ),
    inference(resolution,[],[f2936,f601])).

fof(f3160,plain,
    ( spl7_502
    | ~ spl7_80
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3080,f2808,f2232,f1061,f511,f3158])).

fof(f3158,plain,
    ( spl7_502
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK6))),sK4(k1_zfmisc_1(k3_struct_0(sK6)))) = sK4(k1_zfmisc_1(k3_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_502])])).

fof(f3080,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK6))),sK4(k1_zfmisc_1(k3_struct_0(sK6)))) = sK4(k1_zfmisc_1(k3_struct_0(sK6)))
    | ~ spl7_80
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f512])).

fof(f3153,plain,
    ( spl7_500
    | ~ spl7_52
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3079,f2808,f2232,f1061,f377,f3151])).

fof(f3151,plain,
    ( spl7_500
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK5))),sK4(k1_zfmisc_1(k3_struct_0(sK5)))) = sK4(k1_zfmisc_1(k3_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_500])])).

fof(f3079,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK5))),sK4(k1_zfmisc_1(k3_struct_0(sK5)))) = sK4(k1_zfmisc_1(k3_struct_0(sK5)))
    | ~ spl7_52
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f378])).

fof(f3146,plain,
    ( spl7_498
    | ~ spl7_68
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3062,f2808,f2232,f1061,f463,f3144])).

fof(f3144,plain,
    ( spl7_498
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK1))),sK4(k1_zfmisc_1(k3_struct_0(sK1)))) = sK4(k1_zfmisc_1(k3_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_498])])).

fof(f3062,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK1))),sK4(k1_zfmisc_1(k3_struct_0(sK1)))) = sK4(k1_zfmisc_1(k3_struct_0(sK1)))
    | ~ spl7_68
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f464])).

fof(f3139,plain,
    ( spl7_496
    | ~ spl7_64
    | spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f3061,f2808,f2232,f1061,f447,f3137])).

fof(f3137,plain,
    ( spl7_496
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK0))),sK4(k1_zfmisc_1(k3_struct_0(sK0)))) = sK4(k1_zfmisc_1(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_496])])).

fof(f3061,plain,
    ( k1_funct_1(k6_partfun1(k1_zfmisc_1(k3_struct_0(sK0))),sK4(k1_zfmisc_1(k3_struct_0(sK0)))) = sK4(k1_zfmisc_1(k3_struct_0(sK0)))
    | ~ spl7_64
    | ~ spl7_189
    | ~ spl7_390
    | ~ spl7_472 ),
    inference(resolution,[],[f3060,f448])).

fof(f3132,plain,
    ( spl7_492
    | ~ spl7_495
    | ~ spl7_10
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f3121,f2824,f186,f3130,f3124])).

fof(f3124,plain,
    ( spl7_492
  <=> ! [X0] : m1_subset_1(k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k3_struct_0(sK5),X0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_492])])).

fof(f3121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_struct_0(sK5),o_0_0_xboole_0)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k3_struct_0(sK5),X0),o_0_0_xboole_0) )
    | ~ spl7_10
    | ~ spl7_474 ),
    inference(resolution,[],[f2890,f187])).

fof(f2890,plain,
    ( ! [X4,X3] :
        ( ~ l1_struct_0(X3)
        | ~ m1_subset_1(k3_struct_0(X3),o_0_0_xboole_0)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),k3_struct_0(X3),X4),o_0_0_xboole_0) )
    | ~ spl7_474 ),
    inference(resolution,[],[f2842,f110])).

fof(f2842,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | m1_subset_1(k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),X2,X3),o_0_0_xboole_0)
        | ~ m1_subset_1(X2,o_0_0_xboole_0) )
    | ~ spl7_474 ),
    inference(forward_demodulation,[],[f2832,f2825])).

fof(f2832,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0),X2,X3),o_0_0_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X2) )
    | ~ spl7_474 ),
    inference(superposition,[],[f142,f2825])).

fof(f2937,plain,
    ( spl7_490
    | ~ spl7_482
    | ~ spl7_488 ),
    inference(avatar_split_clause,[],[f2926,f2916,f2878,f2935])).

fof(f2916,plain,
    ( spl7_488
  <=> o_0_0_xboole_0 = sK4(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_488])])).

fof(f2926,plain,
    ( m1_subset_1(o_0_0_xboole_0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_482
    | ~ spl7_488 ),
    inference(forward_demodulation,[],[f2920,f2917])).

fof(f2917,plain,
    ( o_0_0_xboole_0 = sK4(o_0_0_xboole_0)
    | ~ spl7_488 ),
    inference(avatar_component_clause,[],[f2916])).

fof(f2920,plain,
    ( m1_subset_1(sK4(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_482
    | ~ spl7_488 ),
    inference(superposition,[],[f2879,f2917])).

fof(f2879,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_482 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f2918,plain,
    ( spl7_488
    | ~ spl7_8
    | ~ spl7_484 ),
    inference(avatar_split_clause,[],[f2905,f2884,f179,f2916])).

fof(f2905,plain,
    ( o_0_0_xboole_0 = sK4(o_0_0_xboole_0)
    | ~ spl7_8
    | ~ spl7_484 ),
    inference(resolution,[],[f2885,f350])).

fof(f2885,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl7_484 ),
    inference(avatar_component_clause,[],[f2884])).

fof(f2902,plain,
    ( spl7_486
    | spl7_484
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2843,f2824,f2884,f2900])).

fof(f2843,plain,
    ( ! [X7] :
        ( v1_xboole_0(sK4(o_0_0_xboole_0))
        | ~ m1_subset_1(X7,sK4(o_0_0_xboole_0))
        | m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) )
    | ~ spl7_474 ),
    inference(forward_demodulation,[],[f2837,f2825])).

fof(f2837,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,sK4(o_0_0_xboole_0))
        | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))))
        | m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) )
    | ~ spl7_474 ),
    inference(superposition,[],[f1017,f2825])).

fof(f2886,plain,
    ( spl7_482
    | spl7_484
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2844,f2824,f2884,f2878])).

fof(f2844,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_474 ),
    inference(forward_demodulation,[],[f2838,f2825])).

fof(f2838,plain,
    ( m1_subset_1(sK4(sK4(o_0_0_xboole_0)),k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))))
    | ~ spl7_474 ),
    inference(superposition,[],[f1209,f2825])).

fof(f2873,plain,
    ( spl7_478
    | ~ spl7_481
    | ~ spl7_18
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2835,f2824,f214,f2871,f2865])).

fof(f2871,plain,
    ( spl7_481
  <=> ~ m1_subset_1(u1_struct_0(sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_481])])).

fof(f2835,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),o_0_0_xboole_0)
    | m1_subset_1(sK2,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_18
    | ~ spl7_474 ),
    inference(superposition,[],[f639,f2825])).

fof(f2851,plain,
    ( spl7_476
    | ~ spl7_390
    | ~ spl7_474 ),
    inference(avatar_split_clause,[],[f2829,f2824,f2232,f2849])).

fof(f2849,plain,
    ( spl7_476
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_476])])).

fof(f2829,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl7_390
    | ~ spl7_474 ),
    inference(superposition,[],[f2233,f2825])).

fof(f2826,plain,
    ( spl7_474
    | ~ spl7_8
    | ~ spl7_472 ),
    inference(avatar_split_clause,[],[f2813,f2808,f179,f2824])).

fof(f2813,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_472 ),
    inference(resolution,[],[f2809,f350])).

fof(f2810,plain,
    ( spl7_470
    | spl7_472
    | ~ spl7_390 ),
    inference(avatar_split_clause,[],[f2237,f2232,f2808,f2802])).

fof(f2237,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_390 ),
    inference(resolution,[],[f2233,f601])).

fof(f2797,plain,
    ( spl7_468
    | spl7_406
    | ~ spl7_186 ),
    inference(avatar_split_clause,[],[f1070,f1049,f2352,f2795])).

fof(f2795,plain,
    ( spl7_468
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k3_struct_0(sK0))) = sK4(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_468])])).

fof(f1049,plain,
    ( spl7_186
  <=> m1_subset_1(sK4(k3_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f1070,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),sK4(k3_struct_0(sK0))) = sK4(k3_struct_0(sK0))
    | ~ spl7_186 ),
    inference(resolution,[],[f1050,f601])).

fof(f1050,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_186 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f2790,plain,
    ( spl7_466
    | spl7_435 ),
    inference(avatar_split_clause,[],[f2592,f2558,f2788])).

fof(f2788,plain,
    ( spl7_466
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_466])])).

fof(f2592,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = sK4(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl7_435 ),
    inference(resolution,[],[f2559,f858])).

fof(f2783,plain,
    ( spl7_464
    | spl7_402
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f849,f526,f2339,f2781])).

fof(f2781,plain,
    ( spl7_464
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),k3_struct_0(sK1)) = k3_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_464])])).

fof(f849,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),k3_struct_0(sK1)) = k3_struct_0(sK1)
    | ~ spl7_84 ),
    inference(resolution,[],[f601,f527])).

fof(f2776,plain,
    ( spl7_462
    | ~ spl7_306
    | spl7_435 ),
    inference(avatar_split_clause,[],[f2768,f2558,f1711,f2774])).

fof(f2774,plain,
    ( spl7_462
  <=> k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) = sK4(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_462])])).

fof(f2768,plain,
    ( k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK4(k4_tmap_1(sK0,sK1))) = sK4(k4_tmap_1(sK0,sK1))
    | ~ spl7_306
    | ~ spl7_435 ),
    inference(resolution,[],[f2745,f121])).

fof(f2745,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k4_tmap_1(sK0,sK1))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_306
    | ~ spl7_435 ),
    inference(subsumption_resolution,[],[f2743,f2559])).

fof(f2743,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k4_tmap_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | k1_funct_1(k6_partfun1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),X0) = X0 )
    | ~ spl7_306 ),
    inference(resolution,[],[f1712,f601])).

fof(f2767,plain,
    ( spl7_458
    | ~ spl7_461
    | ~ spl7_436 ),
    inference(avatar_split_clause,[],[f2746,f2564,f2765,f2759])).

fof(f2759,plain,
    ( spl7_458
  <=> v1_xboole_0(sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_458])])).

fof(f2765,plain,
    ( spl7_461
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_461])])).

fof(f2746,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK4(k4_tmap_1(sK0,sK1)))
    | v1_xboole_0(sK4(k4_tmap_1(sK0,sK1)))
    | ~ spl7_436 ),
    inference(resolution,[],[f2565,f121])).

fof(f2754,plain,
    ( spl7_456
    | spl7_305 ),
    inference(avatar_split_clause,[],[f2742,f1705,f2752])).

fof(f2752,plain,
    ( spl7_456
  <=> k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) = sK4(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_456])])).

fof(f2742,plain,
    ( k1_funct_1(k6_partfun1(k4_tmap_1(sK0,sK1)),sK4(k4_tmap_1(sK0,sK1))) = sK4(k4_tmap_1(sK0,sK1))
    | ~ spl7_305 ),
    inference(resolution,[],[f1706,f858])).

fof(f2741,plain,
    ( spl7_454
    | ~ spl7_26
    | ~ spl7_452 ),
    inference(avatar_split_clause,[],[f2732,f2715,f246,f2739])).

fof(f2739,plain,
    ( spl7_454
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_454])])).

fof(f2715,plain,
    ( spl7_452
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_452])])).

fof(f2732,plain,
    ( m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,sK2),u1_struct_0(sK0))
    | ~ spl7_26
    | ~ spl7_452 ),
    inference(resolution,[],[f2716,f247])).

fof(f2716,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0)) )
    | ~ spl7_452 ),
    inference(avatar_component_clause,[],[f2715])).

fof(f2729,plain,
    ( ~ spl7_203
    | spl7_7
    | ~ spl7_450 ),
    inference(avatar_split_clause,[],[f2725,f2712,f172,f1147])).

fof(f172,plain,
    ( spl7_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2712,plain,
    ( spl7_450
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_450])])).

fof(f2725,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_7
    | ~ spl7_450 ),
    inference(subsumption_resolution,[],[f2718,f173])).

fof(f173,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f2718,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_450 ),
    inference(resolution,[],[f2713,f120])).

fof(f2713,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_450 ),
    inference(avatar_component_clause,[],[f2712])).

fof(f2717,plain,
    ( spl7_450
    | spl7_452
    | ~ spl7_192
    | ~ spl7_442
    | ~ spl7_444 ),
    inference(avatar_split_clause,[],[f2638,f2630,f2618,f1093,f2715,f2712])).

fof(f1093,plain,
    ( spl7_192
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f2618,plain,
    ( spl7_442
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_442])])).

fof(f2630,plain,
    ( spl7_444
  <=> v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_444])])).

fof(f2638,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_192
    | ~ spl7_442
    | ~ spl7_444 ),
    inference(subsumption_resolution,[],[f2637,f1094])).

fof(f1094,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl7_192 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f2637,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0))
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_442
    | ~ spl7_444 ),
    inference(subsumption_resolution,[],[f2634,f2619])).

fof(f2619,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_442 ),
    inference(avatar_component_clause,[],[f2618])).

fof(f2634,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | m1_subset_1(k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),o_0_0_xboole_0,X1),u1_struct_0(sK0))
        | ~ v1_funct_1(o_0_0_xboole_0)
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl7_444 ),
    inference(resolution,[],[f2631,f135])).

fof(f2631,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_444 ),
    inference(avatar_component_clause,[],[f2630])).

fof(f2702,plain,
    ( spl7_446
    | spl7_448
    | ~ spl7_442 ),
    inference(avatar_split_clause,[],[f2624,f2618,f2700,f2694])).

fof(f2694,plain,
    ( spl7_446
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_446])])).

fof(f2624,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_442 ),
    inference(resolution,[],[f2619,f601])).

fof(f2632,plain,
    ( spl7_444
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_440 ),
    inference(avatar_split_clause,[],[f2608,f2597,f200,f165,f158,f151,f2630])).

fof(f2597,plain,
    ( spl7_440
  <=> k4_tmap_1(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_440])])).

fof(f2608,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_440 ),
    inference(subsumption_resolution,[],[f2607,f152])).

fof(f2607,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_440 ),
    inference(subsumption_resolution,[],[f2606,f159])).

fof(f2606,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_440 ),
    inference(subsumption_resolution,[],[f2605,f166])).

fof(f2605,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_14
    | ~ spl7_440 ),
    inference(subsumption_resolution,[],[f2603,f201])).

fof(f2603,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_440 ),
    inference(superposition,[],[f128,f2598])).

fof(f2598,plain,
    ( k4_tmap_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl7_440 ),
    inference(avatar_component_clause,[],[f2597])).

fof(f2620,plain,
    ( spl7_442
    | ~ spl7_292
    | ~ spl7_440 ),
    inference(avatar_split_clause,[],[f2601,f2597,f1660,f2618])).

fof(f2601,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_292
    | ~ spl7_440 ),
    inference(superposition,[],[f1661,f2598])).

fof(f2609,plain,
    ( ~ spl7_205
    | spl7_23
    | ~ spl7_440 ),
    inference(avatar_split_clause,[],[f2602,f2597,f230,f1157])).

fof(f1157,plain,
    ( spl7_205
  <=> k1_funct_1(o_0_0_xboole_0,sK2) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_205])])).

fof(f230,plain,
    ( spl7_23
  <=> k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f2602,plain,
    ( k1_funct_1(o_0_0_xboole_0,sK2) != sK2
    | ~ spl7_23
    | ~ spl7_440 ),
    inference(superposition,[],[f231,f2598])).

fof(f231,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f2599,plain,
    ( spl7_440
    | ~ spl7_8
    | ~ spl7_304 ),
    inference(avatar_split_clause,[],[f2585,f1708,f179,f2597])).

fof(f2585,plain,
    ( k4_tmap_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_304 ),
    inference(resolution,[],[f1709,f350])).

fof(f1709,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK1))
    | ~ spl7_304 ),
    inference(avatar_component_clause,[],[f1708])).

fof(f2582,plain,
    ( spl7_438
    | ~ spl7_8
    | ~ spl7_434 ),
    inference(avatar_split_clause,[],[f2569,f2561,f179,f2580])).

fof(f2580,plain,
    ( spl7_438
  <=> k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_438])])).

fof(f2561,plain,
    ( spl7_434
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_434])])).

fof(f2569,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_434 ),
    inference(resolution,[],[f2562,f350])).

fof(f2562,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl7_434 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2566,plain,
    ( spl7_434
    | spl7_436
    | ~ spl7_306 ),
    inference(avatar_split_clause,[],[f1715,f1711,f2564,f2561])).

fof(f1715,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k4_tmap_1(sK0,sK1))
        | v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1) )
    | ~ spl7_306 ),
    inference(resolution,[],[f1712,f531])).

fof(f2556,plain,
    ( spl7_432
    | spl7_396
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f848,f518,f2319,f2554])).

fof(f848,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),k3_struct_0(sK0)) = k3_struct_0(sK0)
    | ~ spl7_82 ),
    inference(resolution,[],[f601,f519])).

fof(f2546,plain,
    ( spl7_430
    | ~ spl7_380 ),
    inference(avatar_split_clause,[],[f2536,f2168,f2544])).

fof(f2168,plain,
    ( spl7_380
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_380])])).

fof(f2536,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))
    | ~ spl7_380 ),
    inference(subsumption_resolution,[],[f2535,f2169])).

fof(f2169,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))
    | ~ spl7_380 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f2535,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))
    | ~ spl7_380 ),
    inference(resolution,[],[f2173,f116])).

fof(f2173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_380 ),
    inference(resolution,[],[f2169,f115])).

fof(f2462,plain,
    ( spl7_428
    | ~ spl7_158 ),
    inference(avatar_split_clause,[],[f921,f918,f2460])).

fof(f2460,plain,
    ( spl7_428
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK6))),u1_struct_0(sK3(sK3(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_428])])).

fof(f918,plain,
    ( spl7_158
  <=> k3_struct_0(sK3(sK3(sK6))) = k6_partfun1(u1_struct_0(sK3(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f921,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK6))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK6))),u1_struct_0(sK3(sK3(sK6))))))
    | ~ spl7_158 ),
    inference(superposition,[],[f108,f919])).

fof(f919,plain,
    ( k3_struct_0(sK3(sK3(sK6))) = k6_partfun1(u1_struct_0(sK3(sK3(sK6))))
    | ~ spl7_158 ),
    inference(avatar_component_clause,[],[f918])).

fof(f2455,plain,
    ( spl7_426
    | spl7_374
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f1233,f502,f179,f2138,f2453])).

fof(f2453,plain,
    ( spl7_426
  <=> u1_struct_0(sK6) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_426])])).

fof(f2138,plain,
    ( spl7_374
  <=> k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK6))) = sK4(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_374])])).

fof(f1233,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK6))) = sK4(u1_struct_0(sK6))
    | u1_struct_0(sK6) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_78 ),
    inference(superposition,[],[f889,f503])).

fof(f2448,plain,
    ( spl7_424
    | ~ spl7_50
    | ~ spl7_422 ),
    inference(avatar_split_clause,[],[f2433,f2428,f368,f2446])).

fof(f2433,plain,
    ( k3_struct_0(sK5) = k6_partfun1(o_0_0_xboole_0)
    | ~ spl7_50
    | ~ spl7_422 ),
    inference(superposition,[],[f369,f2429])).

fof(f2430,plain,
    ( spl7_422
    | spl7_346
    | ~ spl7_8
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f1232,f368,f179,f1943,f2428])).

fof(f1232,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | u1_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_50 ),
    inference(superposition,[],[f889,f369])).

fof(f2409,plain,
    ( spl7_420
    | ~ spl7_342 ),
    inference(avatar_split_clause,[],[f2402,f1885,f2407])).

fof(f1885,plain,
    ( spl7_342
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_342])])).

fof(f2402,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))
    | ~ spl7_342 ),
    inference(subsumption_resolution,[],[f2401,f1886])).

fof(f1886,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))
    | ~ spl7_342 ),
    inference(avatar_component_clause,[],[f1885])).

fof(f2401,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))
    | ~ spl7_342 ),
    inference(resolution,[],[f1889,f116])).

fof(f1889,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_342 ),
    inference(resolution,[],[f1886,f115])).

fof(f2397,plain,
    ( spl7_418
    | ~ spl7_340 ),
    inference(avatar_split_clause,[],[f2390,f1874,f2395])).

fof(f1874,plain,
    ( spl7_340
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_340])])).

fof(f2390,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))
    | ~ spl7_340 ),
    inference(subsumption_resolution,[],[f2389,f1875])).

fof(f1875,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))
    | ~ spl7_340 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f2389,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))
    | ~ spl7_340 ),
    inference(resolution,[],[f1878,f116])).

fof(f1878,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_340 ),
    inference(resolution,[],[f1875,f115])).

fof(f2388,plain,
    ( ~ spl7_413
    | spl7_414
    | spl7_416
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f1165,f1132,f2386,f2380,f2374])).

fof(f1165,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK1)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK4(k3_struct_0(sK1)))
    | ~ spl7_200 ),
    inference(resolution,[],[f1133,f531])).

fof(f2367,plain,
    ( spl7_410
    | spl7_370
    | ~ spl7_8
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f1223,f486,f179,f2125,f2365])).

fof(f2365,plain,
    ( spl7_410
  <=> u1_struct_0(sK3(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_410])])).

fof(f2125,plain,
    ( spl7_370
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK3(sK1)))) = sK4(u1_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_370])])).

fof(f486,plain,
    ( spl7_74
  <=> k3_struct_0(sK3(sK1)) = k6_partfun1(u1_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f1223,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK3(sK1)))) = sK4(u1_struct_0(sK3(sK1)))
    | u1_struct_0(sK3(sK1)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_74 ),
    inference(superposition,[],[f889,f487])).

fof(f487,plain,
    ( k3_struct_0(sK3(sK1)) = k6_partfun1(u1_struct_0(sK3(sK1)))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f486])).

fof(f2360,plain,
    ( ~ spl7_405
    | spl7_406
    | spl7_408
    | ~ spl7_186 ),
    inference(avatar_split_clause,[],[f1071,f1049,f2358,f2352,f2346])).

fof(f2346,plain,
    ( spl7_405
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_405])])).

fof(f2358,plain,
    ( spl7_408
  <=> v1_xboole_0(sK4(k3_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_408])])).

fof(f1071,plain,
    ( v1_xboole_0(sK4(k3_struct_0(sK0)))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK4(k3_struct_0(sK0)))
    | ~ spl7_186 ),
    inference(resolution,[],[f1050,f531])).

fof(f2341,plain,
    ( ~ spl7_401
    | spl7_402
    | spl7_194
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f669,f526,f1105,f2339,f2333])).

fof(f1105,plain,
    ( spl7_194
  <=> v1_xboole_0(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f669,plain,
    ( v1_xboole_0(k3_struct_0(sK1))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k3_struct_0(sK1))
    | ~ spl7_84 ),
    inference(resolution,[],[f531,f527])).

fof(f2328,plain,
    ( spl7_398
    | spl7_366
    | ~ spl7_8
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1222,f470,f179,f2112,f2326])).

fof(f1222,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
    | u1_struct_0(sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_70 ),
    inference(superposition,[],[f889,f471])).

fof(f2321,plain,
    ( ~ spl7_395
    | spl7_396
    | spl7_180
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f668,f518,f1022,f2319,f2313])).

fof(f1022,plain,
    ( spl7_180
  <=> v1_xboole_0(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f668,plain,
    ( v1_xboole_0(k3_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),k3_struct_0(sK0))
    | ~ spl7_82 ),
    inference(resolution,[],[f531,f519])).

fof(f2285,plain,
    ( ~ spl7_389
    | spl7_392
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(avatar_split_clause,[],[f2206,f2197,f165,f158,f151,f2283,f2214])).

fof(f2197,plain,
    ( spl7_386
  <=> k4_tmap_1(sK0,sK3(sK0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_386])])).

fof(f2206,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2205,f152])).

fof(f2205,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2204,f159])).

fof(f2204,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2202,f166])).

fof(f2202,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK3(sK0)),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_386 ),
    inference(superposition,[],[f128,f2198])).

fof(f2198,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_386 ),
    inference(avatar_component_clause,[],[f2197])).

fof(f2234,plain,
    ( spl7_390
    | ~ spl7_298
    | ~ spl7_386 ),
    inference(avatar_split_clause,[],[f2201,f2197,f1684,f2232])).

fof(f2201,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_298
    | ~ spl7_386 ),
    inference(superposition,[],[f1685,f2198])).

fof(f2221,plain,
    ( ~ spl7_4
    | spl7_389 ),
    inference(avatar_contradiction_clause,[],[f2220])).

fof(f2220,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_389 ),
    inference(subsumption_resolution,[],[f2219,f166])).

fof(f2219,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_389 ),
    inference(resolution,[],[f2215,f116])).

fof(f2215,plain,
    ( ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_389 ),
    inference(avatar_component_clause,[],[f2214])).

fof(f2216,plain,
    ( ~ spl7_389
    | spl7_192
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(avatar_split_clause,[],[f2209,f2197,f165,f158,f151,f1093,f2214])).

fof(f2209,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2208,f152])).

fof(f2208,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2207,f159])).

fof(f2207,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_386 ),
    inference(subsumption_resolution,[],[f2203,f166])).

fof(f2203,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ m1_pre_topc(sK3(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_386 ),
    inference(superposition,[],[f127,f2198])).

fof(f2199,plain,
    ( spl7_386
    | ~ spl7_8
    | ~ spl7_382 ),
    inference(avatar_split_clause,[],[f2186,f2178,f179,f2197])).

fof(f2186,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_382 ),
    inference(resolution,[],[f2179,f350])).

fof(f2179,plain,
    ( v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
    | ~ spl7_382 ),
    inference(avatar_component_clause,[],[f2178])).

fof(f2183,plain,
    ( spl7_382
    | spl7_384
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f1687,f1684,f2181,f2178])).

fof(f1687,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
        | v1_xboole_0(k4_tmap_1(sK0,sK3(sK0)))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK3(sK0))) )
    | ~ spl7_298 ),
    inference(resolution,[],[f1685,f640])).

fof(f2170,plain,
    ( spl7_380
    | ~ spl7_308 ),
    inference(avatar_split_clause,[],[f2163,f1722,f2168])).

fof(f1722,plain,
    ( spl7_308
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_308])])).

fof(f2163,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))
    | ~ spl7_308 ),
    inference(subsumption_resolution,[],[f2162,f1723])).

fof(f1723,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))
    | ~ spl7_308 ),
    inference(avatar_component_clause,[],[f1722])).

fof(f2162,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))
    | ~ spl7_308 ),
    inference(resolution,[],[f1726,f116])).

fof(f1726,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_308 ),
    inference(resolution,[],[f1723,f115])).

fof(f2159,plain,
    ( spl7_378
    | ~ spl7_376 ),
    inference(avatar_split_clause,[],[f2151,f2145,f2157])).

fof(f2145,plain,
    ( spl7_376
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK6))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_376])])).

fof(f2151,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_376 ),
    inference(superposition,[],[f145,f2146])).

fof(f2146,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK6))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_376 ),
    inference(avatar_component_clause,[],[f2145])).

fof(f2147,plain,
    ( spl7_376
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f635,f632,f2145])).

fof(f635,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK6))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_106 ),
    inference(resolution,[],[f633,f362])).

fof(f2140,plain,
    ( spl7_372
    | spl7_374
    | ~ spl7_12
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f2101,f502,f193,f2138,f2132])).

fof(f2132,plain,
    ( spl7_372
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_372])])).

fof(f2101,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK4(u1_struct_0(sK6))) = sK4(u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ spl7_12
    | ~ spl7_78 ),
    inference(forward_demodulation,[],[f2059,f503])).

fof(f2059,plain,
    ( v2_struct_0(sK6)
    | k1_funct_1(k6_partfun1(u1_struct_0(sK6)),sK4(u1_struct_0(sK6))) = sK4(u1_struct_0(sK6))
    | ~ spl7_12 ),
    inference(resolution,[],[f1931,f194])).

fof(f2127,plain,
    ( spl7_368
    | spl7_370
    | ~ spl7_32
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f2065,f486,f276,f2125,f2119])).

fof(f2119,plain,
    ( spl7_368
  <=> v2_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_368])])).

fof(f2065,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK4(u1_struct_0(sK3(sK1)))) = sK4(u1_struct_0(sK3(sK1)))
    | v2_struct_0(sK3(sK1))
    | ~ spl7_32
    | ~ spl7_74 ),
    inference(forward_demodulation,[],[f2023,f487])).

fof(f2023,plain,
    ( v2_struct_0(sK3(sK1))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK1))),sK4(u1_struct_0(sK3(sK1)))) = sK4(u1_struct_0(sK3(sK1)))
    | ~ spl7_32 ),
    inference(resolution,[],[f1931,f277])).

fof(f2114,plain,
    ( spl7_364
    | spl7_366
    | ~ spl7_30
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f2064,f470,f266,f2112,f2106])).

fof(f2106,plain,
    ( spl7_364
  <=> v2_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_364])])).

fof(f2064,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
    | v2_struct_0(sK3(sK0))
    | ~ spl7_30
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f2022,f471])).

fof(f2022,plain,
    ( v2_struct_0(sK3(sK0))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK3(sK0))),sK4(u1_struct_0(sK3(sK0)))) = sK4(u1_struct_0(sK3(sK0)))
    | ~ spl7_30 ),
    inference(resolution,[],[f1931,f267])).

fof(f2019,plain,
    ( spl7_362
    | spl7_357 ),
    inference(avatar_split_clause,[],[f2010,f1983,f2017])).

fof(f2017,plain,
    ( spl7_362
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) = sK4(k3_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_362])])).

fof(f2010,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK6)),sK4(k3_struct_0(sK6))) = sK4(k3_struct_0(sK6))
    | ~ spl7_357 ),
    inference(resolution,[],[f1984,f858])).

fof(f2009,plain,
    ( spl7_360
    | ~ spl7_8
    | ~ spl7_356 ),
    inference(avatar_split_clause,[],[f1994,f1986,f179,f2007])).

fof(f2007,plain,
    ( spl7_360
  <=> k3_struct_0(sK6) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_360])])).

fof(f1994,plain,
    ( k3_struct_0(sK6) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_356 ),
    inference(resolution,[],[f1987,f350])).

fof(f1987,plain,
    ( v1_xboole_0(k3_struct_0(sK6))
    | ~ spl7_356 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f1991,plain,
    ( spl7_356
    | spl7_358
    | ~ spl7_118 ),
    inference(avatar_split_clause,[],[f1014,f693,f1989,f1986])).

fof(f1014,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)))
        | v1_xboole_0(k3_struct_0(sK6))
        | ~ m1_subset_1(X7,k3_struct_0(sK6)) )
    | ~ spl7_118 ),
    inference(resolution,[],[f640,f694])).

fof(f1981,plain,
    ( spl7_354
    | spl7_349 ),
    inference(avatar_split_clause,[],[f1972,f1947,f1979])).

fof(f1979,plain,
    ( spl7_354
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) = sK4(k3_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_354])])).

fof(f1972,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK5)),sK4(k3_struct_0(sK5))) = sK4(k3_struct_0(sK5))
    | ~ spl7_349 ),
    inference(resolution,[],[f1948,f858])).

fof(f1971,plain,
    ( spl7_352
    | ~ spl7_8
    | ~ spl7_348 ),
    inference(avatar_split_clause,[],[f1958,f1950,f179,f1969])).

fof(f1969,plain,
    ( spl7_352
  <=> k3_struct_0(sK5) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_352])])).

fof(f1958,plain,
    ( k3_struct_0(sK5) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_348 ),
    inference(resolution,[],[f1951,f350])).

fof(f1951,plain,
    ( v1_xboole_0(k3_struct_0(sK5))
    | ~ spl7_348 ),
    inference(avatar_component_clause,[],[f1950])).

fof(f1955,plain,
    ( spl7_348
    | spl7_350
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1013,f665,f1953,f1950])).

fof(f1013,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5)))
        | v1_xboole_0(k3_struct_0(sK5))
        | ~ m1_subset_1(X6,k3_struct_0(sK5)) )
    | ~ spl7_112 ),
    inference(resolution,[],[f640,f666])).

fof(f1945,plain,
    ( spl7_344
    | spl7_346
    | ~ spl7_10
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f1932,f368,f186,f1943,f1937])).

fof(f1937,plain,
    ( spl7_344
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_344])])).

fof(f1932,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ spl7_10
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f1930,f369])).

fof(f1930,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK5)),sK4(u1_struct_0(sK5))) = sK4(u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ spl7_10 ),
    inference(resolution,[],[f893,f187])).

fof(f1887,plain,
    ( spl7_342
    | ~ spl7_278 ),
    inference(avatar_split_clause,[],[f1880,f1577,f1885])).

fof(f1577,plain,
    ( spl7_278
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f1880,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))
    | ~ spl7_278 ),
    inference(subsumption_resolution,[],[f1879,f1578])).

fof(f1578,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))
    | ~ spl7_278 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f1879,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))
    | ~ spl7_278 ),
    inference(resolution,[],[f1581,f116])).

fof(f1581,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_278 ),
    inference(resolution,[],[f1578,f115])).

fof(f1876,plain,
    ( spl7_340
    | ~ spl7_276 ),
    inference(avatar_split_clause,[],[f1869,f1566,f1874])).

fof(f1566,plain,
    ( spl7_276
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f1869,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))
    | ~ spl7_276 ),
    inference(subsumption_resolution,[],[f1868,f1567])).

fof(f1567,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))
    | ~ spl7_276 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f1868,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))
    | ~ spl7_276 ),
    inference(resolution,[],[f1570,f116])).

fof(f1570,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_276 ),
    inference(resolution,[],[f1567,f115])).

fof(f1865,plain,
    ( spl7_338
    | ~ spl7_336 ),
    inference(avatar_split_clause,[],[f1858,f1847,f1863])).

fof(f1863,plain,
    ( spl7_338
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_338])])).

fof(f1847,plain,
    ( spl7_336
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_336])])).

fof(f1858,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_336 ),
    inference(superposition,[],[f145,f1848])).

fof(f1848,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_336 ),
    inference(avatar_component_clause,[],[f1847])).

fof(f1849,plain,
    ( spl7_336
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f598,f595,f1847])).

fof(f595,plain,
    ( spl7_98
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f598,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_98 ),
    inference(resolution,[],[f596,f362])).

fof(f596,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f595])).

fof(f1840,plain,
    ( spl7_334
    | ~ spl7_332 ),
    inference(avatar_split_clause,[],[f1833,f1828,f1838])).

fof(f1838,plain,
    ( spl7_334
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_334])])).

fof(f1828,plain,
    ( spl7_332
  <=> k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_332])])).

fof(f1833,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_332 ),
    inference(superposition,[],[f145,f1829])).

fof(f1829,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_332 ),
    inference(avatar_component_clause,[],[f1828])).

fof(f1830,plain,
    ( spl7_332
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f587,f584,f1828])).

fof(f584,plain,
    ( spl7_96
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f587,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_96 ),
    inference(resolution,[],[f585,f362])).

fof(f585,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f584])).

fof(f1819,plain,
    ( spl7_330
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f783,f780,f1817])).

fof(f1817,plain,
    ( spl7_330
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK3(sK3(sK3(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_330])])).

fof(f780,plain,
    ( spl7_136
  <=> k3_struct_0(sK3(sK3(sK3(sK1)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f783,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK1)))),u1_struct_0(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_136 ),
    inference(superposition,[],[f108,f781])).

fof(f781,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK1)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK1)))))
    | ~ spl7_136 ),
    inference(avatar_component_clause,[],[f780])).

fof(f1812,plain,
    ( spl7_328
    | ~ spl7_18
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(avatar_split_clause,[],[f1487,f575,f296,f214,f1810])).

fof(f1810,plain,
    ( spl7_328
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_328])])).

fof(f1487,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_36
    | ~ spl7_94 ),
    inference(subsumption_resolution,[],[f1468,f297])).

fof(f1468,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK1))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK1))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl7_18
    | ~ spl7_94 ),
    inference(resolution,[],[f1454,f576])).

fof(f1801,plain,
    ( spl7_326
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f767,f764,f1799])).

fof(f1799,plain,
    ( spl7_326
  <=> m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK3(sK3(sK3(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_326])])).

fof(f764,plain,
    ( spl7_132
  <=> k3_struct_0(sK3(sK3(sK3(sK0)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f767,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK3(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK3(sK0)))),u1_struct_0(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_132 ),
    inference(superposition,[],[f108,f765])).

fof(f765,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK0)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK0)))))
    | ~ spl7_132 ),
    inference(avatar_component_clause,[],[f764])).

fof(f1794,plain,
    ( spl7_324
    | ~ spl7_18
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(avatar_split_clause,[],[f1495,f927,f358,f214,f1792])).

fof(f1792,plain,
    ( spl7_324
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK6))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK6))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_324])])).

fof(f358,plain,
    ( spl7_48
  <=> l1_pre_topc(sK3(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f927,plain,
    ( spl7_160
  <=> v1_relat_1(k3_struct_0(sK3(sK3(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f1495,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK6))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK6))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(subsumption_resolution,[],[f1476,f359])).

fof(f359,plain,
    ( l1_pre_topc(sK3(sK3(sK6)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f358])).

fof(f1476,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK6))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK6))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK6)))
    | ~ spl7_18
    | ~ spl7_160 ),
    inference(resolution,[],[f1454,f928])).

fof(f928,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK6))))
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f927])).

fof(f1787,plain,
    ( spl7_322
    | ~ spl7_18
    | ~ spl7_34
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f1486,f556,f286,f214,f1785])).

fof(f1785,plain,
    ( spl7_322
  <=> k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_322])])).

fof(f1486,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_34
    | ~ spl7_90 ),
    inference(subsumption_resolution,[],[f1467,f287])).

fof(f1467,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK3(sK0))),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK3(sK0))),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_18
    | ~ spl7_90 ),
    inference(resolution,[],[f1454,f557])).

fof(f1778,plain,
    ( spl7_318
    | spl7_320
    | ~ spl7_130 ),
    inference(avatar_split_clause,[],[f1012,f755,f1776,f1773])).

fof(f1773,plain,
    ( spl7_318
  <=> v1_xboole_0(k3_struct_0(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_318])])).

fof(f1012,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1))))
        | v1_xboole_0(k3_struct_0(sK3(sK1)))
        | ~ m1_subset_1(X5,k3_struct_0(sK3(sK1))) )
    | ~ spl7_130 ),
    inference(resolution,[],[f640,f756])).

fof(f1768,plain,
    ( spl7_316
    | spl7_311 ),
    inference(avatar_split_clause,[],[f1759,f1734,f1766])).

fof(f1766,plain,
    ( spl7_316
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) = sK4(k3_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_316])])).

fof(f1759,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK3(sK0))),sK4(k3_struct_0(sK3(sK0)))) = sK4(k3_struct_0(sK3(sK0)))
    | ~ spl7_311 ),
    inference(resolution,[],[f1735,f858])).

fof(f1758,plain,
    ( spl7_314
    | ~ spl7_8
    | ~ spl7_310 ),
    inference(avatar_split_clause,[],[f1745,f1737,f179,f1756])).

fof(f1756,plain,
    ( spl7_314
  <=> k3_struct_0(sK3(sK0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_314])])).

fof(f1745,plain,
    ( k3_struct_0(sK3(sK0)) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_310 ),
    inference(resolution,[],[f1738,f350])).

fof(f1738,plain,
    ( v1_xboole_0(k3_struct_0(sK3(sK0)))
    | ~ spl7_310 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f1742,plain,
    ( spl7_310
    | spl7_312
    | ~ spl7_128 ),
    inference(avatar_split_clause,[],[f1011,f744,f1740,f1737])).

fof(f1011,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0))))
        | v1_xboole_0(k3_struct_0(sK3(sK0)))
        | ~ m1_subset_1(X4,k3_struct_0(sK3(sK0))) )
    | ~ spl7_128 ),
    inference(resolution,[],[f640,f745])).

fof(f1724,plain,
    ( spl7_308
    | ~ spl7_236 ),
    inference(avatar_split_clause,[],[f1717,f1358,f1722])).

fof(f1358,plain,
    ( spl7_236
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f1717,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f1716,f1359])).

fof(f1359,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))
    | ~ spl7_236 ),
    inference(avatar_component_clause,[],[f1358])).

fof(f1716,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))
    | ~ spl7_236 ),
    inference(resolution,[],[f1362,f116])).

fof(f1362,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_236 ),
    inference(resolution,[],[f1359,f115])).

fof(f1713,plain,
    ( spl7_304
    | spl7_306
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f1663,f1660,f1711,f1708])).

fof(f1663,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | v1_xboole_0(k4_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k4_tmap_1(sK0,sK1)) )
    | ~ spl7_292 ),
    inference(resolution,[],[f1661,f640])).

fof(f1703,plain,
    ( ~ spl7_301
    | spl7_302
    | ~ spl7_298 ),
    inference(avatar_split_clause,[],[f1688,f1684,f1701,f1695])).

fof(f1701,plain,
    ( spl7_302
  <=> v1_relat_1(k4_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_302])])).

fof(f1688,plain,
    ( v1_relat_1(k4_tmap_1(sK0,sK3(sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0)))
    | ~ spl7_298 ),
    inference(resolution,[],[f1685,f113])).

fof(f1686,plain,
    ( spl7_298
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1655,f165,f158,f151,f1684])).

fof(f1655,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1654,f166])).

fof(f1654,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f1605,f116])).

fof(f1605,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0)))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1604,f152])).

fof(f1604,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1603,f166])).

fof(f1603,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(k4_tmap_1(sK0,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f129,f159])).

fof(f1679,plain,
    ( ~ spl7_295
    | spl7_296
    | ~ spl7_292 ),
    inference(avatar_split_clause,[],[f1664,f1660,f1677,f1671])).

fof(f1671,plain,
    ( spl7_295
  <=> ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_295])])).

fof(f1677,plain,
    ( spl7_296
  <=> v1_relat_1(k4_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_296])])).

fof(f1664,plain,
    ( v1_relat_1(k4_tmap_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl7_292 ),
    inference(resolution,[],[f1661,f113])).

fof(f1662,plain,
    ( spl7_292
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1653,f200,f165,f158,f151,f1660])).

fof(f1653,plain,
    ( m1_subset_1(k4_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f1605,f201])).

fof(f1648,plain,
    ( ~ spl7_291
    | ~ spl7_18
    | ~ spl7_282
    | ~ spl7_284 ),
    inference(avatar_split_clause,[],[f1640,f1610,f1589,f214,f1646])).

fof(f1646,plain,
    ( spl7_291
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_291])])).

fof(f1640,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_18
    | ~ spl7_282
    | ~ spl7_284 ),
    inference(forward_demodulation,[],[f1638,f1611])).

fof(f1638,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | ~ spl7_18
    | ~ spl7_282 ),
    inference(resolution,[],[f1596,f215])).

fof(f1637,plain,
    ( spl7_288
    | spl7_229
    | ~ spl7_286 ),
    inference(avatar_split_clause,[],[f1630,f1624,f1307,f1635])).

fof(f1307,plain,
    ( spl7_229
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_229])])).

fof(f1624,plain,
    ( spl7_286
  <=> m1_subset_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_286])])).

fof(f1630,plain,
    ( k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_229
    | ~ spl7_286 ),
    inference(subsumption_resolution,[],[f1628,f1308])).

fof(f1308,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_229 ),
    inference(avatar_component_clause,[],[f1307])).

fof(f1628,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | k1_funct_1(k6_partfun1(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_286 ),
    inference(resolution,[],[f1625,f601])).

fof(f1625,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_286 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f1626,plain,
    ( spl7_286
    | ~ spl7_284 ),
    inference(avatar_split_clause,[],[f1619,f1610,f1624])).

fof(f1619,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_284 ),
    inference(superposition,[],[f121,f1611])).

fof(f1612,plain,
    ( spl7_284
    | ~ spl7_8
    | ~ spl7_282 ),
    inference(avatar_split_clause,[],[f1597,f1589,f179,f1610])).

fof(f1597,plain,
    ( o_0_0_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_8
    | ~ spl7_282 ),
    inference(resolution,[],[f1590,f350])).

fof(f1594,plain,(
    ~ spl7_280 ),
    inference(avatar_contradiction_clause,[],[f1592])).

fof(f1592,plain,
    ( $false
    | ~ spl7_280 ),
    inference(resolution,[],[f1584,f121])).

fof(f1584,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl7_280 ),
    inference(avatar_component_clause,[],[f1583])).

fof(f1583,plain,
    ( spl7_280
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_280])])).

fof(f1591,plain,
    ( spl7_280
    | spl7_282
    | ~ spl7_226 ),
    inference(avatar_split_clause,[],[f1330,f1304,f1589,f1583])).

fof(f1304,plain,
    ( spl7_226
  <=> ! [X5] : ~ r2_hidden(X5,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f1330,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
        | ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl7_226 ),
    inference(resolution,[],[f1305,f126])).

fof(f1305,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl7_226 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f1579,plain,
    ( spl7_278
    | ~ spl7_256 ),
    inference(avatar_split_clause,[],[f1572,f1448,f1577])).

fof(f1448,plain,
    ( spl7_256
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f1572,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))
    | ~ spl7_256 ),
    inference(subsumption_resolution,[],[f1571,f1449])).

fof(f1449,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))
    | ~ spl7_256 ),
    inference(avatar_component_clause,[],[f1448])).

fof(f1571,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))
    | ~ spl7_256 ),
    inference(resolution,[],[f1452,f116])).

fof(f1452,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_256 ),
    inference(resolution,[],[f1449,f115])).

fof(f1568,plain,
    ( spl7_276
    | ~ spl7_254 ),
    inference(avatar_split_clause,[],[f1561,f1437,f1566])).

fof(f1437,plain,
    ( spl7_254
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f1561,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))
    | ~ spl7_254 ),
    inference(subsumption_resolution,[],[f1560,f1438])).

fof(f1438,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))
    | ~ spl7_254 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f1560,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))
    | ~ spl7_254 ),
    inference(resolution,[],[f1441,f116])).

fof(f1441,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_254 ),
    inference(resolution,[],[f1438,f115])).

fof(f1559,plain,
    ( spl7_274
    | ~ spl7_18
    | ~ spl7_32
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f1485,f495,f276,f214,f1557])).

fof(f1557,plain,
    ( spl7_274
  <=> k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).

fof(f1485,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_32
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f1466,f277])).

fof(f1466,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK1)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK1)),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK1))
    | ~ spl7_18
    | ~ spl7_76 ),
    inference(resolution,[],[f1454,f496])).

fof(f1552,plain,
    ( spl7_272
    | ~ spl7_18
    | ~ spl7_38
    | ~ spl7_104 ),
    inference(avatar_split_clause,[],[f1496,f623,f306,f214,f1550])).

fof(f1550,plain,
    ( spl7_272
  <=> k1_funct_1(k3_struct_0(sK3(sK6)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).

fof(f1496,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK6)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_38
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f1477,f307])).

fof(f1477,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK6)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK6)),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK6))
    | ~ spl7_18
    | ~ spl7_104 ),
    inference(resolution,[],[f1454,f624])).

fof(f1545,plain,
    ( spl7_270
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f1484,f479,f266,f214,f1543])).

fof(f1543,plain,
    ( spl7_270
  <=> k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_270])])).

fof(f1484,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f1465,f267])).

fof(f1465,plain,
    ( k1_funct_1(k3_struct_0(sK3(sK0)),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK3(sK0)),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK3(sK0))
    | ~ spl7_18
    | ~ spl7_72 ),
    inference(resolution,[],[f1454,f480])).

fof(f1538,plain,
    ( spl7_268
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1524,f165,f158,f151,f1536])).

fof(f1536,plain,
    ( spl7_268
  <=> k4_tmap_1(sK0,sK3(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f1524,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK3(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1523,f166])).

fof(f1523,plain,
    ( k4_tmap_1(sK0,sK3(sK0)) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK3(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f1507,f116])).

fof(f1507,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1506,f152])).

fof(f1506,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1505,f166])).

fof(f1505,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k4_tmap_1(sK0,X0) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f118,f159])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',d7_tmap_1)).

fof(f1531,plain,
    ( spl7_266
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1522,f200,f165,f158,f151,f1529])).

fof(f1522,plain,
    ( k4_tmap_1(sK0,sK1) = k2_tmap_1(sK0,sK0,k3_struct_0(sK0),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f1507,f201])).

fof(f1521,plain,
    ( spl7_264
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f1497,f511,f214,f193,f1519])).

fof(f1519,plain,
    ( spl7_264
  <=> k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_264])])).

fof(f1497,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK1)),sK2)
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f1479,f194])).

fof(f1479,plain,
    ( k1_funct_1(k3_struct_0(sK6),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK6),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK6)
    | ~ spl7_18
    | ~ spl7_80 ),
    inference(resolution,[],[f1454,f512])).

fof(f1514,plain,
    ( spl7_262
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_68
    | ~ spl7_100 ),
    inference(avatar_split_clause,[],[f1483,f607,f463,f258,f214,f1512])).

fof(f1512,plain,
    ( spl7_262
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f1483,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK2) = sK2
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_68
    | ~ spl7_100 ),
    inference(forward_demodulation,[],[f1482,f608])).

fof(f1482,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f1464,f259])).

fof(f1464,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK1),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl7_18
    | ~ spl7_68 ),
    inference(resolution,[],[f1454,f464])).

fof(f1504,plain,
    ( spl7_260
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_64
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f1481,f865,f447,f214,f165,f1502])).

fof(f1502,plain,
    ( spl7_260
  <=> k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_260])])).

fof(f1481,plain,
    ( k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2) = sK2
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_64
    | ~ spl7_150 ),
    inference(forward_demodulation,[],[f1480,f866])).

fof(f1480,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ spl7_4
    | ~ spl7_18
    | ~ spl7_64 ),
    inference(subsumption_resolution,[],[f1463,f166])).

fof(f1463,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_18
    | ~ spl7_64 ),
    inference(resolution,[],[f1454,f448])).

fof(f1462,plain,
    ( spl7_258
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f1455,f377,f214,f186,f1460])).

fof(f1460,plain,
    ( spl7_258
  <=> k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f1455,plain,
    ( k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK1)),sK2)
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f1453,f378])).

fof(f1453,plain,
    ( ~ v1_relat_1(k3_struct_0(sK5))
    | k1_funct_1(k3_struct_0(sK5),sK2) = k1_funct_1(k7_relat_1(k3_struct_0(sK5),u1_struct_0(sK1)),sK2)
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f1098,f187])).

fof(f1450,plain,
    ( spl7_256
    | ~ spl7_222 ),
    inference(avatar_split_clause,[],[f1443,f1289,f1448])).

fof(f1289,plain,
    ( spl7_222
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).

fof(f1443,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))
    | ~ spl7_222 ),
    inference(subsumption_resolution,[],[f1442,f1290])).

fof(f1290,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))
    | ~ spl7_222 ),
    inference(avatar_component_clause,[],[f1289])).

fof(f1442,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))
    | ~ spl7_222 ),
    inference(resolution,[],[f1293,f116])).

fof(f1293,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_222 ),
    inference(resolution,[],[f1290,f115])).

fof(f1439,plain,
    ( spl7_254
    | ~ spl7_220 ),
    inference(avatar_split_clause,[],[f1432,f1278,f1437])).

fof(f1278,plain,
    ( spl7_220
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f1432,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))
    | ~ spl7_220 ),
    inference(subsumption_resolution,[],[f1431,f1279])).

fof(f1279,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))
    | ~ spl7_220 ),
    inference(avatar_component_clause,[],[f1278])).

fof(f1431,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))
    | ~ spl7_220 ),
    inference(resolution,[],[f1282,f116])).

fof(f1282,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_220 ),
    inference(resolution,[],[f1279,f115])).

fof(f1430,plain,
    ( spl7_252
    | ~ spl7_250 ),
    inference(avatar_split_clause,[],[f1423,f1418,f1428])).

fof(f1423,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_250 ),
    inference(superposition,[],[f145,f1419])).

fof(f1420,plain,
    ( spl7_250
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f430,f396,f1418])).

fof(f430,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_56 ),
    inference(resolution,[],[f362,f397])).

fof(f1413,plain,
    ( spl7_248
    | ~ spl7_246 ),
    inference(avatar_split_clause,[],[f1406,f1401,f1411])).

fof(f1406,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_246 ),
    inference(superposition,[],[f145,f1402])).

fof(f1403,plain,
    ( spl7_246
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f429,f386,f1401])).

fof(f429,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_54 ),
    inference(resolution,[],[f362,f387])).

fof(f1394,plain,
    ( spl7_242
    | spl7_244
    | ~ spl7_196 ),
    inference(avatar_split_clause,[],[f1214,f1108,f1392,f1386])).

fof(f1108,plain,
    ( spl7_196
  <=> ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | ~ m1_subset_1(X3,k3_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f1214,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK1))))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_196 ),
    inference(resolution,[],[f1209,f1109])).

fof(f1109,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k3_struct_0(sK1))
        | m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) )
    | ~ spl7_196 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1379,plain,
    ( spl7_238
    | spl7_240
    | ~ spl7_182 ),
    inference(avatar_split_clause,[],[f1213,f1025,f1377,f1371])).

fof(f1213,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k3_struct_0(sK0))))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(k3_struct_0(sK0)))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_182 ),
    inference(resolution,[],[f1209,f1026])).

fof(f1360,plain,
    ( spl7_236
    | ~ spl7_214 ),
    inference(avatar_split_clause,[],[f1353,f1241,f1358])).

fof(f1241,plain,
    ( spl7_214
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f1353,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))
    | ~ spl7_214 ),
    inference(subsumption_resolution,[],[f1352,f1242])).

fof(f1242,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_214 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1352,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_214 ),
    inference(resolution,[],[f1245,f116])).

fof(f1245,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_214 ),
    inference(resolution,[],[f1242,f115])).

fof(f1351,plain,
    ( spl7_234
    | ~ spl7_232 ),
    inference(avatar_split_clause,[],[f1344,f1339,f1349])).

fof(f1344,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK6)))))
    | ~ spl7_232 ),
    inference(superposition,[],[f145,f1340])).

fof(f1341,plain,
    ( spl7_232
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f541,f538,f1339])).

fof(f541,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK6)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK6)))))
    | ~ spl7_86 ),
    inference(resolution,[],[f539,f362])).

fof(f1328,plain,
    ( spl7_230
    | ~ spl7_8
    | ~ spl7_228 ),
    inference(avatar_split_clause,[],[f1315,f1310,f179,f1326])).

fof(f1310,plain,
    ( spl7_228
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_228])])).

fof(f1315,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_8
    | ~ spl7_228 ),
    inference(resolution,[],[f1311,f350])).

fof(f1311,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl7_228 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1312,plain,
    ( spl7_226
    | spl7_228
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1217,f179,f1310,f1304])).

fof(f1217,plain,
    ( ! [X5] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X5,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f1209,f559])).

fof(f1302,plain,
    ( spl7_224
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f617,f614,f1300])).

fof(f617,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK6)),u1_struct_0(sK3(sK6)))))
    | ~ spl7_102 ),
    inference(superposition,[],[f108,f615])).

fof(f1291,plain,
    ( spl7_222
    | ~ spl7_178 ),
    inference(avatar_split_clause,[],[f1284,f1003,f1289])).

fof(f1003,plain,
    ( spl7_178
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f1284,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))
    | ~ spl7_178 ),
    inference(subsumption_resolution,[],[f1283,f1004])).

fof(f1004,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_178 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f1283,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_178 ),
    inference(resolution,[],[f1007,f116])).

fof(f1007,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_178 ),
    inference(resolution,[],[f1004,f115])).

fof(f1280,plain,
    ( spl7_220
    | ~ spl7_176 ),
    inference(avatar_split_clause,[],[f1273,f992,f1278])).

fof(f992,plain,
    ( spl7_176
  <=> l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f1273,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))
    | ~ spl7_176 ),
    inference(subsumption_resolution,[],[f1272,f993])).

fof(f993,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_176 ),
    inference(avatar_component_clause,[],[f992])).

fof(f1272,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_176 ),
    inference(resolution,[],[f996,f116])).

fof(f996,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_176 ),
    inference(resolution,[],[f993,f115])).

fof(f1263,plain,
    ( spl7_218
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f569,f566,f1261])).

fof(f569,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK1))),u1_struct_0(sK3(sK3(sK1))))))
    | ~ spl7_92 ),
    inference(superposition,[],[f108,f567])).

fof(f1252,plain,
    ( spl7_216
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f550,f547,f1250])).

fof(f550,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK3(sK0))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK3(sK0))),u1_struct_0(sK3(sK3(sK0))))))
    | ~ spl7_88 ),
    inference(superposition,[],[f108,f548])).

fof(f1243,plain,
    ( spl7_214
    | ~ spl7_166 ),
    inference(avatar_split_clause,[],[f1236,f949,f1241])).

fof(f1236,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ spl7_166 ),
    inference(subsumption_resolution,[],[f1235,f950])).

fof(f1235,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK6))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_166 ),
    inference(resolution,[],[f953,f116])).

fof(f953,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))
        | l1_pre_topc(X0) )
    | ~ spl7_166 ),
    inference(resolution,[],[f950,f115])).

fof(f1206,plain,
    ( ~ spl7_189
    | spl7_212
    | ~ spl7_18
    | ~ spl7_192
    | ~ spl7_204 ),
    inference(avatar_split_clause,[],[f1199,f1160,f1093,f214,f1204,f1061])).

fof(f1204,plain,
    ( spl7_212
  <=> k1_funct_1(k7_relat_1(o_0_0_xboole_0,u1_struct_0(sK1)),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f1160,plain,
    ( spl7_204
  <=> k1_funct_1(o_0_0_xboole_0,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).

fof(f1199,plain,
    ( k1_funct_1(k7_relat_1(o_0_0_xboole_0,u1_struct_0(sK1)),sK2) = sK2
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl7_18
    | ~ spl7_192
    | ~ spl7_204 ),
    inference(forward_demodulation,[],[f1153,f1161])).

fof(f1161,plain,
    ( k1_funct_1(o_0_0_xboole_0,sK2) = sK2
    | ~ spl7_204 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1153,plain,
    ( k1_funct_1(o_0_0_xboole_0,sK2) = k1_funct_1(k7_relat_1(o_0_0_xboole_0,u1_struct_0(sK1)),sK2)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl7_18
    | ~ spl7_192 ),
    inference(resolution,[],[f1094,f1068])).

fof(f1198,plain,
    ( spl7_210
    | ~ spl7_18
    | ~ spl7_188
    | ~ spl7_192 ),
    inference(avatar_split_clause,[],[f1154,f1093,f1064,f214,f1196])).

fof(f1196,plain,
    ( spl7_210
  <=> k1_funct_1(o_0_0_xboole_0,sK2) = k1_funct_1(k7_relat_1(o_0_0_xboole_0,u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).

fof(f1064,plain,
    ( spl7_188
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).

fof(f1154,plain,
    ( k1_funct_1(o_0_0_xboole_0,sK2) = k1_funct_1(k7_relat_1(o_0_0_xboole_0,u1_struct_0(sK1)),sK2)
    | ~ spl7_18
    | ~ spl7_188
    | ~ spl7_192 ),
    inference(subsumption_resolution,[],[f1153,f1065])).

fof(f1065,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl7_188 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f1189,plain,
    ( ~ spl7_203
    | spl7_208
    | ~ spl7_198 ),
    inference(avatar_split_clause,[],[f1181,f1123,f1187,f1147])).

fof(f1187,plain,
    ( spl7_208
  <=> v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f1123,plain,
    ( spl7_198
  <=> k3_struct_0(sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).

fof(f1181,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl7_198 ),
    inference(superposition,[],[f111,f1124])).

fof(f1124,plain,
    ( k3_struct_0(sK1) = o_0_0_xboole_0
    | ~ spl7_198 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1173,plain,
    ( spl7_206
    | spl7_195 ),
    inference(avatar_split_clause,[],[f1163,f1102,f1171])).

fof(f1171,plain,
    ( spl7_206
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) = sK4(k3_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f1163,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK1)),sK4(k3_struct_0(sK1))) = sK4(k3_struct_0(sK1))
    | ~ spl7_195 ),
    inference(resolution,[],[f1103,f858])).

fof(f1162,plain,
    ( spl7_204
    | ~ spl7_100
    | ~ spl7_198 ),
    inference(avatar_split_clause,[],[f1137,f1123,f607,f1160])).

fof(f1137,plain,
    ( k1_funct_1(o_0_0_xboole_0,sK2) = sK2
    | ~ spl7_100
    | ~ spl7_198 ),
    inference(superposition,[],[f608,f1124])).

fof(f1152,plain,
    ( ~ spl7_28
    | spl7_203 ),
    inference(avatar_contradiction_clause,[],[f1151])).

fof(f1151,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_203 ),
    inference(subsumption_resolution,[],[f1150,f259])).

fof(f1150,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl7_203 ),
    inference(resolution,[],[f1148,f114])).

fof(f1148,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_203 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1149,plain,
    ( ~ spl7_203
    | spl7_192
    | ~ spl7_198 ),
    inference(avatar_split_clause,[],[f1142,f1123,f1093,f1147])).

fof(f1142,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ l1_struct_0(sK1)
    | ~ spl7_198 ),
    inference(superposition,[],[f110,f1124])).

fof(f1134,plain,
    ( spl7_200
    | ~ spl7_196 ),
    inference(avatar_split_clause,[],[f1127,f1108,f1132])).

fof(f1127,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_196 ),
    inference(resolution,[],[f1109,f121])).

fof(f1125,plain,
    ( spl7_198
    | ~ spl7_8
    | ~ spl7_194 ),
    inference(avatar_split_clause,[],[f1112,f1105,f179,f1123])).

fof(f1112,plain,
    ( k3_struct_0(sK1) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_194 ),
    inference(resolution,[],[f1106,f350])).

fof(f1106,plain,
    ( v1_xboole_0(k3_struct_0(sK1))
    | ~ spl7_194 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f1110,plain,
    ( spl7_194
    | spl7_196
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f1010,f526,f1108,f1105])).

fof(f1010,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | v1_xboole_0(k3_struct_0(sK1))
        | ~ m1_subset_1(X3,k3_struct_0(sK1)) )
    | ~ spl7_84 ),
    inference(resolution,[],[f640,f527])).

fof(f1095,plain,
    ( ~ spl7_153
    | spl7_192
    | ~ spl7_184 ),
    inference(avatar_split_clause,[],[f1059,f1040,f1093,f882])).

fof(f1040,plain,
    ( spl7_184
  <=> k3_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f1059,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ l1_struct_0(sK0)
    | ~ spl7_184 ),
    inference(superposition,[],[f110,f1041])).

fof(f1041,plain,
    ( k3_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl7_184 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1079,plain,
    ( spl7_190
    | spl7_181 ),
    inference(avatar_split_clause,[],[f1067,f1019,f1077])).

fof(f1077,plain,
    ( spl7_190
  <=> k1_funct_1(k6_partfun1(k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) = sK4(k3_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f1067,plain,
    ( k1_funct_1(k6_partfun1(k3_struct_0(sK0)),sK4(k3_struct_0(sK0))) = sK4(k3_struct_0(sK0))
    | ~ spl7_181 ),
    inference(resolution,[],[f1020,f858])).

fof(f1066,plain,
    ( spl7_188
    | ~ spl7_64
    | ~ spl7_184 ),
    inference(avatar_split_clause,[],[f1056,f1040,f447,f1064])).

fof(f1056,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl7_64
    | ~ spl7_184 ),
    inference(superposition,[],[f448,f1041])).

fof(f1051,plain,
    ( spl7_186
    | ~ spl7_182 ),
    inference(avatar_split_clause,[],[f1044,f1025,f1049])).

fof(f1044,plain,
    ( m1_subset_1(sK4(k3_struct_0(sK0)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl7_182 ),
    inference(resolution,[],[f1026,f121])).

fof(f1042,plain,
    ( spl7_184
    | ~ spl7_8
    | ~ spl7_180 ),
    inference(avatar_split_clause,[],[f1029,f1022,f179,f1040])).

fof(f1029,plain,
    ( k3_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl7_8
    | ~ spl7_180 ),
    inference(resolution,[],[f1023,f350])).

fof(f1023,plain,
    ( v1_xboole_0(k3_struct_0(sK0))
    | ~ spl7_180 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1027,plain,
    ( spl7_180
    | spl7_182
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f1009,f518,f1025,f1022])).

fof(f1009,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
        | v1_xboole_0(k3_struct_0(sK0))
        | ~ m1_subset_1(X2,k3_struct_0(sK0)) )
    | ~ spl7_82 ),
    inference(resolution,[],[f640,f519])).

fof(f1005,plain,
    ( spl7_178
    | ~ spl7_148 ),
    inference(avatar_split_clause,[],[f998,f842,f1003])).

fof(f998,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ spl7_148 ),
    inference(subsumption_resolution,[],[f997,f843])).

fof(f997,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_148 ),
    inference(resolution,[],[f846,f116])).

fof(f846,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_148 ),
    inference(resolution,[],[f843,f115])).

fof(f994,plain,
    ( spl7_176
    | ~ spl7_146 ),
    inference(avatar_split_clause,[],[f987,f831,f992])).

fof(f987,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ spl7_146 ),
    inference(subsumption_resolution,[],[f986,f832])).

fof(f986,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_146 ),
    inference(resolution,[],[f835,f116])).

fof(f835,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_146 ),
    inference(resolution,[],[f832,f115])).

fof(f985,plain,
    ( spl7_174
    | ~ spl7_172 ),
    inference(avatar_split_clause,[],[f978,f974,f983])).

fof(f978,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_172 ),
    inference(superposition,[],[f145,f975])).

fof(f976,plain,
    ( spl7_172
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f428,f346,f974])).

fof(f428,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK1))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_46 ),
    inference(resolution,[],[f362,f347])).

fof(f969,plain,
    ( spl7_170
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f962,f958,f967])).

fof(f962,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_168 ),
    inference(superposition,[],[f145,f959])).

fof(f960,plain,
    ( spl7_168
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f427,f336,f958])).

fof(f427,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK3(sK0))))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_44 ),
    inference(resolution,[],[f362,f337])).

fof(f951,plain,
    ( spl7_166
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f944,f798,f949])).

fof(f944,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ spl7_140 ),
    inference(subsumption_resolution,[],[f943,f799])).

fof(f943,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK6)))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_140 ),
    inference(resolution,[],[f802,f116])).

fof(f802,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK6))))))
        | l1_pre_topc(X0) )
    | ~ spl7_140 ),
    inference(resolution,[],[f799,f115])).

fof(f942,plain,
    ( spl7_162
    | spl7_164
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f855,f732,f940,f934])).

fof(f934,plain,
    ( spl7_162
  <=> k1_funct_1(k6_partfun1(k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f855,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | k1_funct_1(k6_partfun1(k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl7_126 ),
    inference(resolution,[],[f601,f733])).

fof(f929,plain,
    ( spl7_160
    | ~ spl7_158 ),
    inference(avatar_split_clause,[],[f922,f918,f927])).

fof(f922,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK6))))
    | ~ spl7_158 ),
    inference(superposition,[],[f145,f919])).

fof(f920,plain,
    ( spl7_158
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f431,f358,f918])).

fof(f431,plain,
    ( k3_struct_0(sK3(sK3(sK6))) = k6_partfun1(u1_struct_0(sK3(sK3(sK6))))
    | ~ spl7_48 ),
    inference(resolution,[],[f362,f359])).

fof(f913,plain,
    ( spl7_156
    | ~ spl7_18
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f906,f454,f214,f911])).

fof(f906,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1))
    | ~ spl7_18
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f904,f455])).

fof(f904,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK1)),sK4(u1_struct_0(sK1))) = sK4(u1_struct_0(sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f891,f215])).

fof(f891,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | k1_funct_1(k6_partfun1(X6),sK4(X6)) = sK4(X6) ) ),
    inference(resolution,[],[f858,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t7_boole)).

fof(f903,plain,
    ( spl7_154
    | ~ spl7_62
    | spl7_117 ),
    inference(avatar_split_clause,[],[f896,f681,f438,f901])).

fof(f896,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0))
    | ~ spl7_62
    | ~ spl7_117 ),
    inference(forward_demodulation,[],[f894,f439])).

fof(f894,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) = sK4(u1_struct_0(sK0))
    | ~ spl7_117 ),
    inference(resolution,[],[f858,f682])).

fof(f887,plain,
    ( ~ spl7_4
    | spl7_153 ),
    inference(avatar_contradiction_clause,[],[f886])).

fof(f886,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_153 ),
    inference(subsumption_resolution,[],[f885,f166])).

fof(f885,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_153 ),
    inference(resolution,[],[f883,f114])).

fof(f883,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_153 ),
    inference(avatar_component_clause,[],[f882])).

fof(f884,plain,
    ( ~ spl7_153
    | spl7_1
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f874,f684,f151,f882])).

fof(f684,plain,
    ( spl7_116
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f874,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_116 ),
    inference(subsumption_resolution,[],[f868,f152])).

fof(f868,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_116 ),
    inference(resolution,[],[f685,f120])).

fof(f685,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f684])).

fof(f867,plain,
    ( spl7_116
    | spl7_150
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f859,f438,f207,f865,f684])).

fof(f859,plain,
    ( k1_funct_1(k3_struct_0(sK0),sK2) = sK2
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_16
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f856,f439])).

fof(f856,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_funct_1(k6_partfun1(u1_struct_0(sK0)),sK2) = sK2
    | ~ spl7_16 ),
    inference(resolution,[],[f601,f208])).

fof(f844,plain,
    ( spl7_148
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f837,f820,f842])).

fof(f837,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ spl7_144 ),
    inference(subsumption_resolution,[],[f836,f821])).

fof(f836,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_144 ),
    inference(resolution,[],[f824,f116])).

fof(f824,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_144 ),
    inference(resolution,[],[f821,f115])).

fof(f833,plain,
    ( spl7_146
    | ~ spl7_142 ),
    inference(avatar_split_clause,[],[f826,f809,f831])).

fof(f826,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ spl7_142 ),
    inference(subsumption_resolution,[],[f825,f810])).

fof(f825,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_142 ),
    inference(resolution,[],[f813,f116])).

fof(f813,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_142 ),
    inference(resolution,[],[f810,f115])).

fof(f822,plain,
    ( spl7_144
    | ~ spl7_110 ),
    inference(avatar_split_clause,[],[f815,f656,f820])).

fof(f815,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ spl7_110 ),
    inference(subsumption_resolution,[],[f814,f657])).

fof(f814,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_110 ),
    inference(resolution,[],[f660,f116])).

fof(f660,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_110 ),
    inference(resolution,[],[f657,f115])).

fof(f811,plain,
    ( spl7_142
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f804,f645,f809])).

fof(f804,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ spl7_108 ),
    inference(subsumption_resolution,[],[f803,f646])).

fof(f803,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_108 ),
    inference(resolution,[],[f649,f116])).

fof(f649,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
        | l1_pre_topc(X0) )
    | ~ spl7_108 ),
    inference(resolution,[],[f646,f115])).

fof(f800,plain,
    ( spl7_140
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f793,f632,f798])).

fof(f793,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6))))))
    | ~ spl7_106 ),
    inference(subsumption_resolution,[],[f792,f633])).

fof(f792,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK6))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK6)))))
    | ~ spl7_106 ),
    inference(resolution,[],[f636,f116])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK6)))))
        | l1_pre_topc(X0) )
    | ~ spl7_106 ),
    inference(resolution,[],[f633,f115])).

fof(f791,plain,
    ( spl7_138
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f784,f780,f789])).

fof(f784,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK1)))))
    | ~ spl7_136 ),
    inference(superposition,[],[f145,f781])).

fof(f782,plain,
    ( spl7_136
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f426,f326,f780])).

fof(f426,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK1)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK1)))))
    | ~ spl7_42 ),
    inference(resolution,[],[f362,f327])).

fof(f775,plain,
    ( spl7_134
    | ~ spl7_132 ),
    inference(avatar_split_clause,[],[f768,f764,f773])).

fof(f768,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK3(sK0)))))
    | ~ spl7_132 ),
    inference(superposition,[],[f145,f765])).

fof(f766,plain,
    ( spl7_132
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f425,f316,f764])).

fof(f425,plain,
    ( k3_struct_0(sK3(sK3(sK3(sK0)))) = k6_partfun1(u1_struct_0(sK3(sK3(sK3(sK0)))))
    | ~ spl7_40 ),
    inference(resolution,[],[f362,f317])).

fof(f757,plain,
    ( spl7_130
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f489,f486,f755])).

fof(f489,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK1)),u1_struct_0(sK3(sK1)))))
    | ~ spl7_74 ),
    inference(superposition,[],[f108,f487])).

fof(f746,plain,
    ( spl7_128
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f473,f470,f744])).

fof(f473,plain,
    ( m1_subset_1(k3_struct_0(sK3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3(sK0)),u1_struct_0(sK3(sK0)))))
    | ~ spl7_70 ),
    inference(superposition,[],[f108,f471])).

fof(f734,plain,
    ( spl7_126
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f726,f717,f732])).

fof(f726,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_124 ),
    inference(superposition,[],[f121,f718])).

fof(f721,plain,(
    ~ spl7_120 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | ~ spl7_120 ),
    inference(resolution,[],[f698,f121])).

fof(f698,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl7_120
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f719,plain,
    ( spl7_124
    | ~ spl7_8
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f707,f703,f179,f717])).

fof(f703,plain,
    ( spl7_122
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f707,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_8
    | ~ spl7_122 ),
    inference(resolution,[],[f704,f350])).

fof(f704,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f703])).

fof(f705,plain,
    ( spl7_120
    | spl7_122
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f561,f179,f703,f697])).

fof(f561,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f560,f126])).

fof(f560,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl7_8 ),
    inference(resolution,[],[f559,f121])).

fof(f695,plain,
    ( spl7_118
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f505,f502,f693])).

fof(f505,plain,
    ( m1_subset_1(k3_struct_0(sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6))))
    | ~ spl7_78 ),
    inference(superposition,[],[f108,f503])).

fof(f686,plain,
    ( ~ spl7_115
    | spl7_116
    | spl7_60
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f671,f207,f416,f684,f678])).

fof(f678,plain,
    ( spl7_115
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f416,plain,
    ( spl7_60
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f671,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK2)
    | ~ spl7_16 ),
    inference(resolution,[],[f531,f208])).

fof(f667,plain,
    ( spl7_112
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f371,f368,f665])).

fof(f371,plain,
    ( m1_subset_1(k3_struct_0(sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK5))))
    | ~ spl7_50 ),
    inference(superposition,[],[f108,f369])).

fof(f658,plain,
    ( spl7_110
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f651,f595,f656])).

fof(f651,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f650,f596])).

fof(f650,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK1))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_98 ),
    inference(resolution,[],[f599,f116])).

fof(f599,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))
        | l1_pre_topc(X0) )
    | ~ spl7_98 ),
    inference(resolution,[],[f596,f115])).

fof(f647,plain,
    ( spl7_108
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f638,f584,f645])).

fof(f638,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ spl7_96 ),
    inference(subsumption_resolution,[],[f637,f585])).

fof(f637,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK3(sK0))))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_96 ),
    inference(resolution,[],[f588,f116])).

fof(f588,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))
        | l1_pre_topc(X0) )
    | ~ spl7_96 ),
    inference(resolution,[],[f585,f115])).

fof(f634,plain,
    ( spl7_106
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f627,f538,f632])).

fof(f627,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK6)))))
    | ~ spl7_86 ),
    inference(subsumption_resolution,[],[f626,f539])).

fof(f626,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK6)))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK6))))
    | ~ spl7_86 ),
    inference(resolution,[],[f542,f116])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK6))))
        | l1_pre_topc(X0) )
    | ~ spl7_86 ),
    inference(resolution,[],[f539,f115])).

fof(f625,plain,
    ( spl7_104
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f618,f614,f623])).

fof(f618,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK6)))
    | ~ spl7_102 ),
    inference(superposition,[],[f145,f615])).

fof(f616,plain,
    ( spl7_102
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f432,f306,f614])).

fof(f432,plain,
    ( k3_struct_0(sK3(sK6)) = k6_partfun1(u1_struct_0(sK3(sK6)))
    | ~ spl7_38 ),
    inference(resolution,[],[f362,f307])).

fof(f609,plain,
    ( spl7_100
    | ~ spl7_18
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f602,f454,f214,f607])).

fof(f602,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK2) = sK2
    | ~ spl7_18
    | ~ spl7_66 ),
    inference(forward_demodulation,[],[f600,f455])).

fof(f600,plain,
    ( k1_funct_1(k6_partfun1(u1_struct_0(sK1)),sK2) = sK2
    | ~ spl7_18 ),
    inference(resolution,[],[f146,f215])).

fof(f597,plain,
    ( spl7_98
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f590,f396,f595])).

fof(f590,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f589,f397])).

fof(f589,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK1)))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_56 ),
    inference(resolution,[],[f399,f116])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK1))))))
        | l1_pre_topc(X0) )
    | ~ spl7_56 ),
    inference(resolution,[],[f397,f115])).

fof(f586,plain,
    ( spl7_96
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f579,f386,f584])).

fof(f579,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ spl7_54 ),
    inference(subsumption_resolution,[],[f578,f387])).

fof(f578,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK3(sK0)))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_54 ),
    inference(resolution,[],[f389,f116])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK3(sK0))))))
        | l1_pre_topc(X0) )
    | ~ spl7_54 ),
    inference(resolution,[],[f387,f115])).

fof(f577,plain,
    ( spl7_94
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f570,f566,f575])).

fof(f570,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK1))))
    | ~ spl7_92 ),
    inference(superposition,[],[f145,f567])).

fof(f568,plain,
    ( spl7_92
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f424,f296,f566])).

fof(f424,plain,
    ( k3_struct_0(sK3(sK3(sK1))) = k6_partfun1(u1_struct_0(sK3(sK3(sK1))))
    | ~ spl7_36 ),
    inference(resolution,[],[f362,f297])).

fof(f558,plain,
    ( spl7_90
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f551,f547,f556])).

fof(f551,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK3(sK0))))
    | ~ spl7_88 ),
    inference(superposition,[],[f145,f548])).

fof(f549,plain,
    ( spl7_88
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f423,f286,f547])).

fof(f423,plain,
    ( k3_struct_0(sK3(sK3(sK0))) = k6_partfun1(u1_struct_0(sK3(sK3(sK0))))
    | ~ spl7_34 ),
    inference(resolution,[],[f362,f287])).

fof(f540,plain,
    ( spl7_86
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f533,f358,f538])).

fof(f533,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK6))))
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f532,f359])).

fof(f532,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK6))))
    | ~ l1_pre_topc(sK3(sK3(sK6)))
    | ~ spl7_48 ),
    inference(resolution,[],[f363,f116])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK6)))
        | l1_pre_topc(X0) )
    | ~ spl7_48 ),
    inference(resolution,[],[f359,f115])).

fof(f528,plain,
    ( spl7_84
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f457,f454,f526])).

fof(f457,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl7_66 ),
    inference(superposition,[],[f108,f455])).

fof(f520,plain,
    ( spl7_82
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f441,f438,f518])).

fof(f441,plain,
    ( m1_subset_1(k3_struct_0(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl7_62 ),
    inference(superposition,[],[f108,f439])).

fof(f513,plain,
    ( spl7_80
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f506,f502,f511])).

fof(f506,plain,
    ( v1_relat_1(k3_struct_0(sK6))
    | ~ spl7_78 ),
    inference(superposition,[],[f145,f503])).

fof(f504,plain,
    ( spl7_78
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f433,f193,f502])).

fof(f433,plain,
    ( k3_struct_0(sK6) = k6_partfun1(u1_struct_0(sK6))
    | ~ spl7_12 ),
    inference(resolution,[],[f362,f194])).

fof(f497,plain,
    ( spl7_76
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f490,f486,f495])).

fof(f490,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK1)))
    | ~ spl7_74 ),
    inference(superposition,[],[f145,f487])).

fof(f488,plain,
    ( spl7_74
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f422,f276,f486])).

fof(f422,plain,
    ( k3_struct_0(sK3(sK1)) = k6_partfun1(u1_struct_0(sK3(sK1)))
    | ~ spl7_32 ),
    inference(resolution,[],[f362,f277])).

fof(f481,plain,
    ( spl7_72
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f474,f470,f479])).

fof(f474,plain,
    ( v1_relat_1(k3_struct_0(sK3(sK0)))
    | ~ spl7_70 ),
    inference(superposition,[],[f145,f471])).

fof(f472,plain,
    ( spl7_70
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f421,f266,f470])).

fof(f421,plain,
    ( k3_struct_0(sK3(sK0)) = k6_partfun1(u1_struct_0(sK3(sK0)))
    | ~ spl7_30 ),
    inference(resolution,[],[f362,f267])).

fof(f465,plain,
    ( spl7_68
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f458,f454,f463])).

fof(f458,plain,
    ( v1_relat_1(k3_struct_0(sK1))
    | ~ spl7_66 ),
    inference(superposition,[],[f145,f455])).

fof(f456,plain,
    ( spl7_66
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f420,f258,f454])).

fof(f420,plain,
    ( k3_struct_0(sK1) = k6_partfun1(u1_struct_0(sK1))
    | ~ spl7_28 ),
    inference(resolution,[],[f362,f259])).

fof(f449,plain,
    ( spl7_64
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f442,f438,f447])).

fof(f442,plain,
    ( v1_relat_1(k3_struct_0(sK0))
    | ~ spl7_62 ),
    inference(superposition,[],[f145,f439])).

fof(f440,plain,
    ( spl7_62
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f419,f165,f438])).

fof(f419,plain,
    ( k3_struct_0(sK0) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f362,f166])).

fof(f418,plain,
    ( ~ spl7_59
    | spl7_60
    | spl7_25 ),
    inference(avatar_split_clause,[],[f405,f238,f416,f410])).

fof(f410,plain,
    ( spl7_59
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f238,plain,
    ( spl7_25
  <=> ~ r2_hidden(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f405,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(u1_struct_0(sK1),sK2)
    | ~ spl7_25 ),
    inference(resolution,[],[f126,f239])).

fof(f239,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK2)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f238])).

fof(f398,plain,
    ( spl7_56
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f391,f346,f396])).

fof(f391,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ spl7_46 ),
    inference(subsumption_resolution,[],[f390,f347])).

fof(f390,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK1))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl7_46 ),
    inference(resolution,[],[f349,f116])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK1)))))
        | l1_pre_topc(X0) )
    | ~ spl7_46 ),
    inference(resolution,[],[f347,f115])).

fof(f388,plain,
    ( spl7_54
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f381,f336,f386])).

fof(f381,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f380,f337])).

fof(f380,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK3(sK0))))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl7_44 ),
    inference(resolution,[],[f339,f116])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK3(sK0)))))
        | l1_pre_topc(X0) )
    | ~ spl7_44 ),
    inference(resolution,[],[f337,f115])).

fof(f379,plain,
    ( spl7_52
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f372,f368,f377])).

fof(f372,plain,
    ( v1_relat_1(k3_struct_0(sK5))
    | ~ spl7_50 ),
    inference(superposition,[],[f145,f369])).

fof(f370,plain,
    ( spl7_50
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f361,f186,f368])).

fof(f361,plain,
    ( k3_struct_0(sK5) = k6_partfun1(u1_struct_0(sK5))
    | ~ spl7_10 ),
    inference(resolution,[],[f109,f187])).

fof(f360,plain,
    ( spl7_48
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f353,f306,f358])).

fof(f353,plain,
    ( l1_pre_topc(sK3(sK3(sK6)))
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f352,f307])).

fof(f352,plain,
    ( l1_pre_topc(sK3(sK3(sK6)))
    | ~ l1_pre_topc(sK3(sK6))
    | ~ spl7_38 ),
    inference(resolution,[],[f309,f116])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK6))
        | l1_pre_topc(X0) )
    | ~ spl7_38 ),
    inference(resolution,[],[f307,f115])).

fof(f348,plain,
    ( spl7_46
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f341,f326,f346])).

fof(f341,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f340,f327])).

fof(f340,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK1)))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl7_42 ),
    inference(resolution,[],[f329,f116])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK1))))
        | l1_pre_topc(X0) )
    | ~ spl7_42 ),
    inference(resolution,[],[f327,f115])).

fof(f338,plain,
    ( spl7_44
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f331,f316,f336])).

fof(f331,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f330,f317])).

fof(f330,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK3(sK0)))))
    | ~ l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl7_40 ),
    inference(resolution,[],[f319,f116])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK3(sK0))))
        | l1_pre_topc(X0) )
    | ~ spl7_40 ),
    inference(resolution,[],[f317,f115])).

fof(f328,plain,
    ( spl7_42
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f321,f296,f326])).

fof(f321,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f320,f297])).

fof(f320,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK1))))
    | ~ l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl7_36 ),
    inference(resolution,[],[f299,f116])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK1)))
        | l1_pre_topc(X0) )
    | ~ spl7_36 ),
    inference(resolution,[],[f297,f115])).

fof(f318,plain,
    ( spl7_40
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f311,f286,f316])).

fof(f311,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f310,f287])).

fof(f310,plain,
    ( l1_pre_topc(sK3(sK3(sK3(sK0))))
    | ~ l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_34 ),
    inference(resolution,[],[f289,f116])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK3(sK0)))
        | l1_pre_topc(X0) )
    | ~ spl7_34 ),
    inference(resolution,[],[f287,f115])).

fof(f308,plain,
    ( spl7_38
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f301,f193,f306])).

fof(f301,plain,
    ( l1_pre_topc(sK3(sK6))
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f300,f194])).

fof(f300,plain,
    ( l1_pre_topc(sK3(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ spl7_12 ),
    inference(resolution,[],[f250,f116])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK6)
        | l1_pre_topc(X1) )
    | ~ spl7_12 ),
    inference(resolution,[],[f115,f194])).

fof(f298,plain,
    ( spl7_36
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f291,f276,f296])).

fof(f291,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f290,f277])).

fof(f290,plain,
    ( l1_pre_topc(sK3(sK3(sK1)))
    | ~ l1_pre_topc(sK3(sK1))
    | ~ spl7_32 ),
    inference(resolution,[],[f279,f116])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK1))
        | l1_pre_topc(X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f277,f115])).

fof(f288,plain,
    ( spl7_34
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f281,f266,f286])).

fof(f281,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f280,f267])).

fof(f280,plain,
    ( l1_pre_topc(sK3(sK3(sK0)))
    | ~ l1_pre_topc(sK3(sK0))
    | ~ spl7_30 ),
    inference(resolution,[],[f269,f116])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3(sK0))
        | l1_pre_topc(X0) )
    | ~ spl7_30 ),
    inference(resolution,[],[f267,f115])).

fof(f278,plain,
    ( spl7_32
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f271,f258,f276])).

fof(f271,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f270,f259])).

fof(f270,plain,
    ( l1_pre_topc(sK3(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl7_28 ),
    inference(resolution,[],[f261,f116])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | l1_pre_topc(X0) )
    | ~ spl7_28 ),
    inference(resolution,[],[f259,f115])).

fof(f268,plain,
    ( spl7_30
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f253,f165,f266])).

fof(f253,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f252,f166])).

fof(f252,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f249,f116])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f115,f166])).

fof(f260,plain,
    ( spl7_28
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f251,f200,f165,f258])).

fof(f251,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(resolution,[],[f249,f201])).

fof(f248,plain,
    ( spl7_26
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f241,f214,f246])).

fof(f241,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f124,f215])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t1_subset)).

fof(f240,plain,
    ( ~ spl7_25
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f233,f214,f238])).

fof(f233,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK2)
    | ~ spl7_18 ),
    inference(resolution,[],[f123,f215])).

fof(f232,plain,(
    ~ spl7_23 ),
    inference(avatar_split_clause,[],[f104,f230])).

fof(f104,plain,(
    k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,
    ( k1_funct_1(k4_tmap_1(sK0,sK1),sK2) != sK2
    & r2_hidden(sK2,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f87,f86,f85])).

fof(f85,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
                & r2_hidden(X2,u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(sK0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( k1_funct_1(k4_tmap_1(X0,sK1),X2) != X2
            & r2_hidden(X2,u1_struct_0(sK1))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
          & r2_hidden(X2,u1_struct_0(X1))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_funct_1(k4_tmap_1(X0,X1),sK2) != sK2
        & r2_hidden(sK2,u1_struct_0(X1))
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) != X2
              & r2_hidden(X2,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,u1_struct_0(X1))
                 => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',t95_tmap_1)).

fof(f225,plain,
    ( spl7_20
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f217,f179,f223])).

fof(f217,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl7_8 ),
    inference(resolution,[],[f117,f180])).

fof(f216,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f103,f214])).

fof(f103,plain,(
    r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

fof(f209,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f102,f207])).

fof(f102,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f88])).

fof(f202,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f101,f200])).

fof(f101,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f195,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f144,f193])).

fof(f144,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f95])).

fof(f95,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',existence_l1_pre_topc)).

fof(f188,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f143,f186])).

fof(f143,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f93])).

fof(f93,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',existence_l1_struct_0)).

fof(f181,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f105,f179])).

fof(f105,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t95_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f174,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f100,f172])).

fof(f100,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f167,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f99,f165])).

fof(f99,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f160,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f98,f158])).

fof(f98,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f153,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f97,f151])).

fof(f97,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).
%------------------------------------------------------------------------------

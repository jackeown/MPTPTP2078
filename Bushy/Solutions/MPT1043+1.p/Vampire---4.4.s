%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t159_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:33 EDT 2019

% Result     : Theorem 27.15s
% Output     : Refutation 27.15s
% Verified   : 
% Statistics : Number of formulae       : 3720 (17109 expanded)
%              Number of leaves         :  794 (7831 expanded)
%              Depth                    :   15
%              Number of atoms          : 11455 (45569 expanded)
%              Number of equality atoms :  306 (3732 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f94,f101,f108,f117,f130,f137,f138,f155,f166,f184,f193,f200,f228,f265,f279,f286,f301,f302,f309,f311,f322,f329,f339,f349,f356,f373,f374,f381,f388,f395,f397,f415,f428,f435,f444,f466,f473,f480,f481,f488,f495,f502,f503,f504,f505,f506,f507,f525,f541,f548,f565,f572,f579,f580,f581,f600,f607,f614,f618,f638,f645,f652,f665,f678,f722,f729,f736,f765,f784,f788,f795,f796,f797,f798,f799,f800,f801,f802,f821,f828,f832,f847,f854,f861,f907,f919,f923,f924,f925,f926,f927,f928,f955,f962,f963,f970,f977,f984,f986,f1010,f1030,f1037,f1041,f1067,f1128,f1155,f1162,f1169,f1176,f1183,f1184,f1191,f1198,f1205,f1212,f1219,f1221,f1234,f1242,f1265,f1272,f1279,f1286,f1293,f1300,f1307,f1308,f1309,f1316,f1317,f1318,f1319,f1320,f1321,f1327,f1328,f1329,f1330,f1331,f1332,f1374,f1383,f1390,f1391,f1398,f1405,f1413,f1415,f1417,f1419,f1476,f1483,f1490,f1497,f1498,f1511,f1539,f1546,f1554,f1561,f1568,f1576,f1583,f1584,f1591,f1598,f1606,f1613,f1615,f1616,f1617,f1618,f1633,f1636,f1637,f1638,f1646,f1655,f1657,f1661,f1663,f1669,f1672,f1683,f1684,f1685,f1686,f1698,f1706,f1714,f1722,f1730,f1738,f1747,f1755,f1763,f1771,f1779,f1787,f1808,f1810,f1812,f1813,f1814,f1815,f1816,f1817,f1818,f1819,f1820,f1827,f1828,f1829,f1830,f1831,f1832,f1833,f1834,f1835,f1865,f1866,f1873,f1880,f1918,f1925,f1932,f1961,f1968,f1975,f1982,f1989,f1990,f1997,f2004,f2011,f2018,f2025,f2027,f2070,f2071,f2078,f2108,f2115,f2122,f2129,f2136,f2143,f2150,f2151,f2158,f2165,f2172,f2179,f2186,f2193,f2195,f2211,f2218,f2225,f2256,f2263,f2270,f2277,f2284,f2291,f2292,f2293,f2294,f2295,f2302,f2309,f2316,f2317,f2324,f2326,f2342,f2349,f2356,f2374,f2387,f2403,f2404,f2417,f2418,f2450,f2457,f2464,f2471,f2478,f2485,f2492,f2493,f2500,f2507,f2514,f2521,f2528,f2535,f2542,f2549,f2551,f2570,f2578,f2601,f2609,f2610,f2617,f2655,f2662,f2669,f2676,f2683,f2690,f2698,f2699,f2701,f2702,f2709,f2716,f2723,f2730,f2737,f2744,f2751,f2753,f2774,f2781,f2788,f2795,f2802,f2809,f2829,f2836,f2843,f2850,f2857,f2858,f2865,f2872,f2879,f2886,f2892,f2900,f2908,f2916,f2923,f2930,f2937,f2939,f2941,f2971,f2979,f2980,f2987,f3006,f3014,f3015,f3022,f3059,f3066,f3073,f3080,f3087,f3094,f3102,f3103,f3105,f3106,f3113,f3120,f3127,f3134,f3141,f3148,f3155,f3162,f3169,f3176,f3183,f3185,f3234,f3241,f3248,f3255,f3262,f3269,f3277,f3279,f3280,f3282,f3284,f3285,f3292,f3299,f3306,f3313,f3320,f3327,f3334,f3336,f3338,f3340,f3388,f3395,f3402,f3409,f3416,f3423,f3431,f3433,f3434,f3436,f3438,f3439,f3446,f3453,f3460,f3467,f3474,f3481,f3488,f3495,f3497,f3499,f3547,f3554,f3561,f3568,f3575,f3582,f3590,f3592,f3593,f3595,f3597,f3598,f3605,f3612,f3619,f3626,f3633,f3640,f3647,f3654,f3661,f3663,f3665,f3716,f3723,f3730,f3737,f3744,f3751,f3759,f3761,f3762,f3764,f3766,f3767,f3774,f3781,f3788,f3795,f3802,f3809,f3816,f3823,f3830,f3837,f3839,f3853,f3861,f3863,f3864,f3871,f3910,f3917,f3924,f3931,f3938,f3945,f3953,f3955,f3956,f3958,f3960,f3961,f3968,f3975,f3982,f3989,f3996,f4003,f4010,f4017,f4024,f4031,f4038,f4040,f4054,f4062,f4064,f4065,f4072,f4086,f4093,f4094,f4095,f4096,f4107,f4120,f4153,f4155,f4156,f4163,f4171,f4173,f4174,f4181,f4182,f4195,f4216,f4223,f4230,f4249,f4256,f4263,f4270,f4277,f4284,f4291,f4320,f4333,f4351,f4358,f4365,f4372,f4379,f4386,f4393,f4394,f4401,f4402,f4445,f4452,f4459,f4466,f4467,f4474,f4481,f4488,f4495,f4503,f4505,f4506,f4508,f4510,f4511,f4518,f4525,f4532,f4539,f4546,f4553,f4560,f4567,f4574,f4581,f4588,f4595,f4597,f4611,f4619,f4621,f4622,f4629,f4643,f4651,f4653,f4654,f4661,f4678,f4686,f4688,f4689,f4696,f4715,f4722,f4723,f4724,f4725,f4732,f4739,f4740,f4747,f4760,f4768,f4770,f4771,f4778,f4825,f4832,f4839,f4848,f4861,f4862,f4891,f4898,f4905,f4938,f4945,f4952,f4959,f4966,f4973,f4980,f4981,f4982,f4983,f4993,f4997,f5005,f5006,f5017,f5030,f5047,f5066,f5073,f5080,f5087,f5094,f5101,f5102,f5103,f5110,f5111,f5115,f5116,f5117,f5118,f5119,f5132,f5133,f5134,f5135,f5136,f5137,f5138,f5139,f5140,f5142,f5144,f5146,f5148,f5150,f5152,f5154,f5156,f5158,f5160,f5162,f5164,f5166,f5168,f5170,f5172,f5180,f5183,f5185,f5187,f5189,f5191,f5193,f5195,f5197,f5206,f5212,f5221,f5223,f5232,f5241,f5286,f5288,f5290,f5300,f5310,f5316,f5319,f5323,f5327,f5330,f5334,f5337,f5341,f5344,f5347,f5351,f5355,f5357,f5360,f5363,f5366,f5369,f5371,f5373,f5382,f5385,f5388,f5392,f5394,f5400,f5469,f5478,f5489,f5498,f5507,f5518,f5527,f5536,f5544,f5553,f5562,f5571,f5580,f5589,f5592,f5601,f5612,f5622,f5631,f5640,f5649,f5658,f5667,f5676,f5685,f5694,f5701,f5711,f5720,f5725,f5734,f5745,f5756,f5769,f5771,f5773,f5781,f5789,f5797,f5799,f5912,f5973,f6007,f6082,f6089,f6096,f6104,f6148,f6162,f6167,f6184,f6189,f6203,f6207,f6212,f6216,f6227,f6237,f6248,f6252,f6257,f6261,f6265,f6269,f6274,f6278,f6288,f6293,f6298,f6316,f6339,f6347,f6354,f6361,f6372,f6379,f6387,f6396,f6404,f6413,f6421,f6429,f6436,f6443,f6451,f6458,f6465,f6472,f6480,f6488,f6490,f6498,f6506,f6514,f6522,f6529,f6536,f6543,f6548,f6549,f6551,f6554,f6556,f6559,f6561,f6568,f6570,f6571,f6572,f6574,f6575,f6576,f6577,f6584,f6586,f6588,f6590,f6592,f6594,f6596,f6598,f6599,f6600,f6608,f6615,f6623,f6630,f6637,f6644,f6651,f6652,f6654,f6662,f6679,f6690,f6693,f6702,f6711,f6714,f6717,f6720,f6729,f6738,f6744,f6747,f6749,f6753,f6755,f6757,f6759,f6762,f6764,f6775,f6787,f6796,f6807,f6810,f6818,f6827,f6836,f6837,f6838,f6839,f6840,f6847,f6862,f6871,f6879,f6887,f6896,f6905,f6914,f6917,f6920,f6923,f6932,f6941,f6950,f6959,f6962,f6978,f6980,f6983,f6991,f6994,f7002,f7011,f7014,f7017,f7020,f7023,f7026,f7029,f7032,f7037,f7039,f7051,f7056,f7058,f7060,f7063,f7071,f7074,f7079,f7082,f7085,f7089,f7098,f7101,f7104,f7107,f7108,f7127,f7130,f7133,f7136,f7138,f7140,f7142,f7144,f7146,f7149,f7153,f7156,f7159,f7163,f7166,f7170,f7173,f7180,f7187,f7196,f7205,f7207,f7216,f7225,f7228,f7237,f7240,f7243,f7246,f7250,f7254,f7257,f7259,f7262,f7265,f7268,f7272,f7275,f7278,f7281,f7284,f7295,f7298,f7307,f7310,f7313,f7316,f7319,f7328,f7332,f7335,f7338,f7347,f7351,f7354,f7357,f7360,f7366,f7369,f7373,f7378,f7385,f7388,f7392,f7395,f7396,f7397,f7433,f7436,f7438,f7441,f7452,f7456,f7464,f7473,f7479,f7488,f7497,f7506,f7509,f7518,f7527,f7530,f7533,f7536,f7539,f7548,f7551,f7554,f7565,f7568,f7581,f7584,f7593,f7599,f7601,f7700,f7707,f7708,f7709,f7710,f7717,f7718,f7759,f7766,f7773,f7774,f7775,f7776,f7777,f7778,f7812,f7819,f7826,f7833,f7840,f7884,f7887,f7890,f7899,f7902,f7910,f7911,f7913,f7914,f7921,f7929,f7938,f7947,f7950,f7953,f7956,f7957,f7966,f7973,f7980,f7983,f7990,f7992,f8021,f8029,f8049,f8064,f8071,f8078,f8079,f8086,f8087,f8101])).

fof(f8101,plain,
    ( ~ spl5_1075
    | ~ spl5_1133
    | ~ spl5_1073
    | ~ spl5_8
    | spl5_1109 ),
    inference(avatar_split_clause,[],[f8097,f6613,f115,f6431,f6724,f6438])).

fof(f6438,plain,
    ( spl5_1075
  <=> ~ v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1075])])).

fof(f6724,plain,
    ( spl5_1133
  <=> ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1133])])).

fof(f6431,plain,
    ( spl5_1073
  <=> ~ v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1073])])).

fof(f115,plain,
    ( spl5_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f6613,plain,
    ( spl5_1109
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1109])])).

fof(f8097,plain,
    ( ~ v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_8
    | ~ spl5_1109 ),
    inference(resolution,[],[f6614,f237])).

fof(f237,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k1_funct_2(o_0_0_xboole_0,X2))
        | ~ v1_funct_2(X1,o_0_0_xboole_0,X2)
        | ~ r1_tarski(X1,k2_zfmisc_1(o_0_0_xboole_0,X2))
        | ~ v1_funct_1(X1) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f236,f116])).

fof(f116,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f236,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(X1,o_0_0_xboole_0,X2)
        | r2_hidden(X1,k1_funct_2(o_0_0_xboole_0,X2))
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f235,f116])).

fof(f235,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k1_funct_2(o_0_0_xboole_0,X2))
        | ~ v1_funct_2(X1,k1_xboole_0,X2)
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f230,f116])).

fof(f230,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t3_subset)).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | r2_hidden(X2,k1_funct_2(k1_xboole_0,X1))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => r2_hidden(X2,k1_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t11_funct_2)).

fof(f6614,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1109 ),
    inference(avatar_component_clause,[],[f6613])).

fof(f8087,plain,
    ( ~ spl5_1005
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8061,f5281,f5718])).

fof(f5718,plain,
    ( spl5_1005
  <=> ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1005])])).

fof(f5281,plain,
    ( spl5_943
  <=> ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_943])])).

fof(f8061,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_943 ),
    inference(resolution,[],[f5282,f148])).

fof(f148,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f66,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t7_boole)).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',d3_tarski)).

fof(f5282,plain,
    ( ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl5_943 ),
    inference(avatar_component_clause,[],[f5281])).

fof(f8086,plain,
    ( spl5_1276
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8051,f5281,f8084])).

fof(f8084,plain,
    ( spl5_1276
  <=> r2_hidden(sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1276])])).

fof(f8051,plain,
    ( r2_hidden(sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_943 ),
    inference(unit_resulting_resolution,[],[f5282,f66])).

fof(f8079,plain,
    ( ~ spl5_1033
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8053,f5281,f6099])).

fof(f6099,plain,
    ( spl5_1033
  <=> ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1033])])).

fof(f8053,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_943 ),
    inference(unit_resulting_resolution,[],[f5282,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8078,plain,
    ( spl5_1274
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8054,f5281,f8076])).

fof(f8076,plain,
    ( spl5_1274
  <=> m1_subset_1(sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1274])])).

fof(f8054,plain,
    ( m1_subset_1(sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_943 ),
    inference(unit_resulting_resolution,[],[f5282,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t1_subset)).

fof(f8071,plain,
    ( ~ spl5_1273
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8055,f5281,f8069])).

fof(f8069,plain,
    ( spl5_1273
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1273])])).

fof(f8055,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_943 ),
    inference(unit_resulting_resolution,[],[f5282,f147])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK4(X2,X3))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f66,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',antisymmetry_r2_hidden)).

fof(f8064,plain,
    ( ~ spl5_1005
    | spl5_943 ),
    inference(avatar_split_clause,[],[f8056,f5281,f5718])).

fof(f8056,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_943 ),
    inference(unit_resulting_resolution,[],[f5282,f148])).

fof(f8049,plain,
    ( ~ spl5_1271
    | spl5_1187 ),
    inference(avatar_split_clause,[],[f8041,f7096,f8047])).

fof(f8047,plain,
    ( spl5_1271
  <=> ~ r2_hidden(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1271])])).

fof(f7096,plain,
    ( spl5_1187
  <=> ~ v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1187])])).

fof(f8041,plain,
    ( ~ r2_hidden(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_1187 ),
    inference(unit_resulting_resolution,[],[f60,f7097,f143])).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f63,f61])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t2_subset)).

fof(f7097,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1187 ),
    inference(avatar_component_clause,[],[f7096])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',existence_m1_subset_1)).

fof(f8029,plain,
    ( spl5_1268
    | spl5_1051 ),
    inference(avatar_split_clause,[],[f8011,f6342,f8027])).

fof(f8027,plain,
    ( spl5_1268
  <=> r2_hidden(sK3(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1268])])).

fof(f6342,plain,
    ( spl5_1051
  <=> ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1051])])).

fof(f8011,plain,
    ( r2_hidden(sK3(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1051 ),
    inference(unit_resulting_resolution,[],[f60,f6343,f63])).

fof(f6343,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1051 ),
    inference(avatar_component_clause,[],[f6342])).

fof(f8021,plain,
    ( ~ spl5_1267
    | spl5_1051 ),
    inference(avatar_split_clause,[],[f8014,f6342,f8019])).

fof(f8019,plain,
    ( spl5_1267
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1267])])).

fof(f8014,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_1051 ),
    inference(unit_resulting_resolution,[],[f60,f6343,f143])).

fof(f7992,plain,
    ( spl5_1248
    | ~ spl5_8
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7991,f6345,f115,f7908])).

fof(f7908,plain,
    ( spl5_1248
  <=> o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1248])])).

fof(f6345,plain,
    ( spl5_1050
  <=> v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1050])])).

fof(f7991,plain,
    ( o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_8
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7845,f116])).

fof(f7845,plain,
    ( k1_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f6346,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t6_boole)).

fof(f6346,plain,
    ( v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1050 ),
    inference(avatar_component_clause,[],[f6345])).

fof(f7990,plain,
    ( spl5_1264
    | ~ spl5_1050
    | spl5_1125 ),
    inference(avatar_split_clause,[],[f7846,f6674,f6345,f7988])).

fof(f7988,plain,
    ( spl5_1264
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1264])])).

fof(f6674,plain,
    ( spl5_1125
  <=> ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1125])])).

fof(f7846,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_1050
    | ~ spl5_1125 ),
    inference(unit_resulting_resolution,[],[f6675,f6346,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',fc3_funct_2)).

fof(f6675,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1125 ),
    inference(avatar_component_clause,[],[f6674])).

fof(f7983,plain,
    ( spl5_1260
    | spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7982,f6345,f299,f263,f223,f7971])).

fof(f7971,plain,
    ( spl5_1260
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1260])])).

fof(f223,plain,
    ( spl5_31
  <=> ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f263,plain,
    ( spl5_36
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f299,plain,
    ( spl5_42
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f7982,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7981,f300])).

fof(f300,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f299])).

fof(f7981,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7847,f264])).

fof(f264,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f263])).

fof(f7847,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_31
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f224,f6346,f64])).

fof(f224,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f223])).

fof(f7980,plain,
    ( spl5_1262
    | spl5_961
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7848,f6345,f5516,f7978])).

fof(f7978,plain,
    ( spl5_1262
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1262])])).

fof(f5516,plain,
    ( spl5_961
  <=> ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_961])])).

fof(f7848,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_961
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f5517,f6346,f64])).

fof(f5517,plain,
    ( ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_961 ),
    inference(avatar_component_clause,[],[f5516])).

fof(f7973,plain,
    ( spl5_1260
    | ~ spl5_1050
    | spl5_1107 ),
    inference(avatar_split_clause,[],[f7849,f6606,f6345,f7971])).

fof(f6606,plain,
    ( spl5_1107
  <=> ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1107])])).

fof(f7849,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_1050
    | ~ spl5_1107 ),
    inference(unit_resulting_resolution,[],[f6607,f6346,f64])).

fof(f6607,plain,
    ( ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_1107 ),
    inference(avatar_component_clause,[],[f6606])).

fof(f7966,plain,
    ( spl5_1258
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7959,f6345,f390,f299,f263,f7964])).

fof(f7964,plain,
    ( spl5_1258
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1258])])).

fof(f390,plain,
    ( spl5_63
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f7959,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7958,f300])).

fof(f7958,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k5_partfun1(sK0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_63
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7850,f264])).

fof(f7850,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_63
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f391,f6346,f64])).

fof(f391,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f390])).

fof(f7957,plain,
    ( spl5_1252
    | spl5_201
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7851,f6345,f1240,f7927])).

fof(f7927,plain,
    ( spl5_1252
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1252])])).

fof(f1240,plain,
    ( spl5_201
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f7851,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_201
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f1241,f6346,f64])).

fof(f1241,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_201 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f7956,plain,
    ( spl5_1252
    | ~ spl5_36
    | ~ spl5_42
    | spl5_67
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7955,f6345,f410,f299,f263,f7927])).

fof(f410,plain,
    ( spl5_67
  <=> ~ v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f7955,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_67
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7954,f300])).

fof(f7954,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_67
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7852,f264])).

fof(f7852,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_67
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f411,f6346,f64])).

fof(f411,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f410])).

fof(f7953,plain,
    ( spl5_1256
    | ~ spl5_36
    | ~ spl5_42
    | spl5_225
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7952,f6345,f1400,f299,f263,f7945])).

fof(f7945,plain,
    ( spl5_1256
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1256])])).

fof(f1400,plain,
    ( spl5_225
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).

fof(f7952,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_225
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7951,f300])).

fof(f7951,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_225
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7853,f264])).

fof(f7853,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_225
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f1401,f6346,f64])).

fof(f1401,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_225 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f7950,plain,
    ( spl5_1254
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7949,f6345,f383,f299,f263,f7936])).

fof(f7936,plain,
    ( spl5_1254
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1254])])).

fof(f383,plain,
    ( spl5_61
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f7949,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7948,f300])).

fof(f7948,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_61
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7854,f264])).

fof(f7854,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_61
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f384,f6346,f64])).

fof(f384,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f383])).

fof(f7947,plain,
    ( spl5_1256
    | ~ spl5_36
    | ~ spl5_42
    | spl5_223
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7940,f6345,f1393,f299,f263,f7945])).

fof(f1393,plain,
    ( spl5_223
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f7940,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_223
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7939,f300])).

fof(f7939,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_223
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7855,f264])).

fof(f7855,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_223
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f1394,f6346,f64])).

fof(f1394,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_223 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f7938,plain,
    ( spl5_1254
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7931,f6345,f376,f299,f263,f7936])).

fof(f376,plain,
    ( spl5_59
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f7931,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7930,f300])).

fof(f7930,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_59
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7856,f264])).

fof(f7856,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_59
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f377,f6346,f64])).

fof(f377,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f376])).

fof(f7929,plain,
    ( spl5_1252
    | ~ spl5_36
    | spl5_49
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7922,f6345,f324,f263,f7927])).

fof(f324,plain,
    ( spl5_49
  <=> ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f7922,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_49
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7857,f264])).

fof(f7857,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_49
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f325,f6346,f64])).

fof(f325,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f324])).

fof(f7921,plain,
    ( spl5_1250
    | spl5_137
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7858,f6345,f816,f7919])).

fof(f7919,plain,
    ( spl5_1250
  <=> v1_xboole_0(k1_funct_2(sK2,sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1250])])).

fof(f816,plain,
    ( spl5_137
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f7858,plain,
    ( v1_xboole_0(k1_funct_2(sK2,sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_137
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f817,f6346,f64])).

fof(f817,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f816])).

fof(f7914,plain,
    ( spl5_1248
    | ~ spl5_6
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7859,f6345,f106,f7908])).

fof(f106,plain,
    ( spl5_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f7859,plain,
    ( o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f107,f6346,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t8_boole)).

fof(f107,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f7913,plain,
    ( spl5_1248
    | ~ spl5_54
    | ~ spl5_530
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7912,f6345,f3100,f354,f7908])).

fof(f354,plain,
    ( spl5_54
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f3100,plain,
    ( spl5_530
  <=> k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_530])])).

fof(f7912,plain,
    ( o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_530
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7860,f3101])).

fof(f3101,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_530 ),
    inference(avatar_component_clause,[],[f3100])).

fof(f7860,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f355,f6346,f70])).

fof(f355,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f354])).

fof(f7911,plain,
    ( spl5_1248
    | ~ spl5_6
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7862,f6345,f106,f7908])).

fof(f7862,plain,
    ( o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f107,f6346,f70])).

fof(f7910,plain,
    ( spl5_1248
    | ~ spl5_54
    | ~ spl5_530
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7903,f6345,f3100,f354,f7908])).

fof(f7903,plain,
    ( o_0_0_xboole_0 = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_530
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7863,f3101])).

fof(f7863,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f355,f6346,f70])).

fof(f7902,plain,
    ( ~ spl5_1247
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7901,f6345,f299,f263,f153,f7897])).

fof(f7897,plain,
    ( spl5_1247
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1247])])).

fof(f153,plain,
    ( spl5_14
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f7901,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7900,f300])).

fof(f7900,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7866,f264])).

fof(f7866,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_14
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f154,f6346,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t5_subset)).

fof(f154,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f7899,plain,
    ( ~ spl5_1247
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7892,f6345,f347,f299,f263,f7897])).

fof(f347,plain,
    ( spl5_52
  <=> r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f7892,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7891,f300])).

fof(f7891,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7867,f264])).

fof(f7867,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f348,f6346,f79])).

fof(f348,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f347])).

fof(f7890,plain,
    ( ~ spl5_1245
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7889,f6345,f299,f263,f153,f7882])).

fof(f7882,plain,
    ( spl5_1245
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1245])])).

fof(f7889,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7888,f300])).

fof(f7888,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7870,f264])).

fof(f7870,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f154,f6346,f169])).

fof(f169,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r1_tarski(X7,X8)
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f65,f71])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7887,plain,
    ( ~ spl5_1245
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7886,f6345,f347,f299,f263,f7882])).

fof(f7886,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7885,f300])).

fof(f7885,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7871,f264])).

fof(f7871,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_52
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f348,f6346,f169])).

fof(f7884,plain,
    ( ~ spl5_1245
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(avatar_split_clause,[],[f7877,f6345,f299,f263,f153,f7882])).

fof(f7877,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7876,f300])).

fof(f7876,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_1050 ),
    inference(forward_demodulation,[],[f7875,f264])).

fof(f7875,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_1050 ),
    inference(unit_resulting_resolution,[],[f6346,f703])).

fof(f703,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),X10)
        | ~ v1_xboole_0(X10) )
    | ~ spl5_14 ),
    inference(resolution,[],[f169,f154])).

fof(f7840,plain,
    ( spl5_1242
    | ~ spl5_4
    | ~ spl5_1116
    | spl5_1119 ),
    inference(avatar_split_clause,[],[f7792,f6649,f6642,f99,f7838])).

fof(f7838,plain,
    ( spl5_1242
  <=> m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1242])])).

fof(f99,plain,
    ( spl5_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f6642,plain,
    ( spl5_1116
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1116])])).

fof(f6649,plain,
    ( spl5_1119
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1119])])).

fof(f7792,plain,
    ( m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_4
    | ~ spl5_1116
    | ~ spl5_1119 ),
    inference(unit_resulting_resolution,[],[f100,f6643,f6650,f270])).

fof(f270,plain,(
    ! [X12,X10,X11,X9] :
      ( m1_subset_1(sK4(k5_partfun1(X9,X10,X11),X12),k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11)
      | r1_tarski(k5_partfun1(X9,X10,X11),X12) ) ),
    inference(resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t158_funct_2)).

fof(f6650,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1119 ),
    inference(avatar_component_clause,[],[f6649])).

fof(f6643,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1116 ),
    inference(avatar_component_clause,[],[f6642])).

fof(f100,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f7833,plain,
    ( spl5_1240
    | spl5_1119 ),
    inference(avatar_split_clause,[],[f7798,f6649,f7831])).

fof(f7831,plain,
    ( spl5_1240
  <=> m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1240])])).

fof(f7798,plain,
    ( m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_1119 ),
    inference(unit_resulting_resolution,[],[f6650,f146])).

fof(f7826,plain,
    ( ~ spl5_1239
    | spl5_1119 ),
    inference(avatar_split_clause,[],[f7799,f6649,f7824])).

fof(f7824,plain,
    ( spl5_1239
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1239])])).

fof(f7799,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_1119 ),
    inference(unit_resulting_resolution,[],[f6650,f147])).

fof(f7819,plain,
    ( ~ spl5_1237
    | ~ spl5_950
    | spl5_1119 ),
    inference(avatar_split_clause,[],[f7803,f6649,f5464,f7817])).

fof(f7817,plain,
    ( spl5_1237
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1237])])).

fof(f5464,plain,
    ( spl5_950
  <=> r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_950])])).

fof(f7803,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_950
    | ~ spl5_1119 ),
    inference(unit_resulting_resolution,[],[f5465,f6650,f170])).

fof(f170,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK4(X9,X10),X11)
      | ~ r1_tarski(X11,X10)
      | r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f65,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5465,plain,
    ( r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_950 ),
    inference(avatar_component_clause,[],[f5464])).

fof(f7812,plain,
    ( ~ spl5_1235
    | spl5_1119 ),
    inference(avatar_split_clause,[],[f7804,f6649,f7810])).

fof(f7810,plain,
    ( spl5_1235
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1235])])).

fof(f7804,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_1119 ),
    inference(unit_resulting_resolution,[],[f121,f6650,f170])).

fof(f121,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f60,f68])).

fof(f7778,plain,
    ( ~ spl5_1233
    | ~ spl5_4
    | spl5_263
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7733,f6642,f1625,f99,f7771])).

fof(f7771,plain,
    ( spl5_1233
  <=> ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1233])])).

fof(f1625,plain,
    ( spl5_263
  <=> ~ v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_263])])).

fof(f7733,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_263
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f1626,f100,f6643,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1626,plain,
    ( ~ v1_funct_1(o_0_0_xboole_0)
    | ~ spl5_263 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f7777,plain,
    ( ~ spl5_1233
    | ~ spl5_4
    | spl5_963
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7734,f6642,f5525,f99,f7771])).

fof(f5525,plain,
    ( spl5_963
  <=> ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_963])])).

fof(f7734,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_963
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f100,f5526,f6643,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5526,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_963 ),
    inference(avatar_component_clause,[],[f5525])).

fof(f7776,plain,
    ( ~ spl5_1233
    | ~ spl5_4
    | spl5_263
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7735,f6642,f1625,f99,f7771])).

fof(f7735,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_263
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f1626,f100,f159,f6643,f204])).

fof(f204,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k5_partfun1(X2,X3,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,X4)
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f75,f65])).

fof(f159,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f67,f66])).

fof(f7775,plain,
    ( ~ spl5_1231
    | ~ spl5_4
    | spl5_263
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7736,f6642,f1625,f99,f7764])).

fof(f7764,plain,
    ( spl5_1231
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1231])])).

fof(f7736,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))))
    | ~ spl5_4
    | ~ spl5_263
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f1626,f100,f121,f6643,f204])).

fof(f7774,plain,
    ( ~ spl5_1229
    | ~ spl5_4
    | spl5_263
    | spl5_1107
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7737,f6642,f6606,f1625,f99,f7757])).

fof(f7757,plain,
    ( spl5_1229
  <=> ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1229])])).

fof(f7737,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_263
    | ~ spl5_1107
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f1626,f100,f6607,f6643,f205])).

fof(f205,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_funct_1(X5)
      | ~ v1_funct_1(X6)
      | v1_xboole_0(k5_partfun1(X7,X8,X6))
      | ~ m1_subset_1(X5,k5_partfun1(X7,X8,X6)) ) ),
    inference(resolution,[],[f75,f63])).

fof(f7773,plain,
    ( ~ spl5_1233
    | ~ spl5_4
    | spl5_963
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7739,f6642,f5525,f99,f7771])).

fof(f7739,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_963
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f100,f5526,f159,f6643,f240])).

fof(f240,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k5_partfun1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X0,X4)
      | v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f76,f65])).

fof(f7766,plain,
    ( ~ spl5_1231
    | ~ spl5_4
    | spl5_963
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7740,f6642,f5525,f99,f7764])).

fof(f7740,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))))
    | ~ spl5_4
    | ~ spl5_963
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f100,f5526,f121,f6643,f240])).

fof(f7759,plain,
    ( ~ spl5_1229
    | ~ spl5_4
    | spl5_963
    | spl5_1107
    | ~ spl5_1116 ),
    inference(avatar_split_clause,[],[f7741,f6642,f6606,f5525,f99,f7757])).

fof(f7741,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_4
    | ~ spl5_963
    | ~ spl5_1107
    | ~ spl5_1116 ),
    inference(unit_resulting_resolution,[],[f100,f5526,f6607,f6643,f241])).

fof(f241,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_funct_2(X5,X6,X7)
      | ~ v1_funct_1(X8)
      | v1_xboole_0(k5_partfun1(X6,X7,X8))
      | ~ m1_subset_1(X5,k5_partfun1(X6,X7,X8)) ) ),
    inference(resolution,[],[f76,f63])).

fof(f7718,plain,
    ( ~ spl5_1227
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7693,f5473,f7715])).

fof(f7715,plain,
    ( spl5_1227
  <=> ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1227])])).

fof(f5473,plain,
    ( spl5_953
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_953])])).

fof(f7693,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_953 ),
    inference(resolution,[],[f5474,f69])).

fof(f5474,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_953 ),
    inference(avatar_component_clause,[],[f5473])).

fof(f7717,plain,
    ( ~ spl5_1227
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7686,f5473,f7715])).

fof(f7686,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f5474,f69])).

fof(f7710,plain,
    ( ~ spl5_1223
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7687,f5473,f7698])).

fof(f7698,plain,
    ( spl5_1223
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1223])])).

fof(f7687,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f159,f5474,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(X0,X2) ) ),
    inference(resolution,[],[f65,f62])).

fof(f7709,plain,
    ( ~ spl5_1225
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7688,f5473,f7705])).

fof(f7705,plain,
    ( spl5_1225
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1225])])).

fof(f7688,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f121,f5474,f167])).

fof(f7708,plain,
    ( ~ spl5_1225
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7689,f5473,f7705])).

fof(f7689,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f5474,f202])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK3(k1_zfmisc_1(X2)))
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t4_subset)).

fof(f7707,plain,
    ( ~ spl5_1225
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7690,f5473,f7705])).

fof(f7690,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f60,f5474,f78])).

fof(f7700,plain,
    ( ~ spl5_1223
    | spl5_953 ),
    inference(avatar_split_clause,[],[f7691,f5473,f7698])).

fof(f7691,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_953 ),
    inference(unit_resulting_resolution,[],[f5474,f62])).

fof(f7601,plain,
    ( spl5_1154
    | ~ spl5_1170
    | ~ spl5_1188 ),
    inference(avatar_split_clause,[],[f7600,f7194,f6948,f6869])).

fof(f6869,plain,
    ( spl5_1154
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1154])])).

fof(f6948,plain,
    ( spl5_1170
  <=> k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1170])])).

fof(f7194,plain,
    ( spl5_1188
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1188])])).

fof(f7600,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_1170
    | ~ spl5_1188 ),
    inference(forward_demodulation,[],[f7195,f6949])).

fof(f6949,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_1170 ),
    inference(avatar_component_clause,[],[f6948])).

fof(f7195,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_1188 ),
    inference(avatar_component_clause,[],[f7194])).

fof(f7599,plain,
    ( ~ spl5_1203
    | ~ spl5_42
    | spl5_93 ),
    inference(avatar_split_clause,[],[f7598,f563,f299,f7431])).

fof(f7431,plain,
    ( spl5_1203
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1203])])).

fof(f563,plain,
    ( spl5_93
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f7598,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_93 ),
    inference(forward_demodulation,[],[f564,f300])).

fof(f564,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f563])).

fof(f7593,plain,
    ( ~ spl5_1221
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7592,f1411,f299,f263,f153,f7579])).

fof(f7579,plain,
    ( spl5_1221
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1221])])).

fof(f1411,plain,
    ( spl5_226
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_226])])).

fof(f7592,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7591,f300])).

fof(f7591,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6134,f264])).

fof(f6134,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f1412,f703])).

fof(f1412,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_226 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f7584,plain,
    ( ~ spl5_1221
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7583,f1411,f347,f299,f263,f7579])).

fof(f7583,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7582,f300])).

fof(f7582,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6130,f264])).

fof(f6130,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f348,f1412,f169])).

fof(f7581,plain,
    ( ~ spl5_1221
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7574,f1411,f299,f263,f153,f7579])).

fof(f7574,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7573,f300])).

fof(f7573,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6129,f264])).

fof(f6129,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f154,f1412,f169])).

fof(f7568,plain,
    ( ~ spl5_1219
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7567,f1411,f347,f299,f263,f7563])).

fof(f7563,plain,
    ( spl5_1219
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1219])])).

fof(f7567,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7566,f300])).

fof(f7566,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6126,f264])).

fof(f6126,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_52
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f348,f1412,f79])).

fof(f7565,plain,
    ( ~ spl5_1219
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7558,f1411,f299,f263,f153,f7563])).

fof(f7558,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7557,f300])).

fof(f7557,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6125,f264])).

fof(f6125,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_14
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f154,f1412,f79])).

fof(f7554,plain,
    ( spl5_1216
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7553,f1411,f354,f299,f263,f7546])).

fof(f7546,plain,
    ( spl5_1216
  <=> k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1216])])).

fof(f7553,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7552,f300])).

fof(f7552,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6122,f264])).

fof(f6122,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f355,f1412,f70])).

fof(f7551,plain,
    ( spl5_1204
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7550,f1411,f299,f263,f106,f7471])).

fof(f7471,plain,
    ( spl5_1204
  <=> k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1204])])).

fof(f7550,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7549,f300])).

fof(f7549,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6121,f264])).

fof(f6121,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f107,f1412,f70])).

fof(f7548,plain,
    ( spl5_1216
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7541,f1411,f354,f299,f263,f7546])).

fof(f7541,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7540,f300])).

fof(f7540,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6119,f264])).

fof(f6119,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_54
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f355,f1412,f70])).

fof(f7539,plain,
    ( spl5_1204
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7538,f1411,f299,f263,f106,f7471])).

fof(f7538,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7537,f300])).

fof(f7537,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6118,f264])).

fof(f6118,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f107,f1412,f70])).

fof(f7536,plain,
    ( spl5_1210
    | ~ spl5_36
    | ~ spl5_42
    | spl5_49
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7535,f1411,f324,f299,f263,f7504])).

fof(f7504,plain,
    ( spl5_1210
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1210])])).

fof(f7535,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_49
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7534,f300])).

fof(f7534,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_49
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6116,f264])).

fof(f6116,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_49
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f325,f1412,f64])).

fof(f7533,plain,
    ( spl5_1214
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7532,f1411,f376,f299,f263,f7525])).

fof(f7525,plain,
    ( spl5_1214
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1214])])).

fof(f7532,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7531,f300])).

fof(f7531,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_59
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6115,f264])).

fof(f6115,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_59
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f377,f1412,f64])).

fof(f7530,plain,
    ( spl5_1212
    | ~ spl5_36
    | ~ spl5_42
    | spl5_223
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7529,f1411,f1393,f299,f263,f7516])).

fof(f7516,plain,
    ( spl5_1212
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1212])])).

fof(f7529,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7528,f300])).

fof(f7528,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6114,f264])).

fof(f6114,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f1394,f1412,f64])).

fof(f7527,plain,
    ( spl5_1214
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7520,f1411,f383,f299,f263,f7525])).

fof(f7520,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7519,f300])).

fof(f7519,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_61
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6113,f264])).

fof(f6113,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_61
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f384,f1412,f64])).

fof(f7518,plain,
    ( spl5_1212
    | ~ spl5_36
    | ~ spl5_42
    | spl5_225
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7511,f1411,f1400,f299,f263,f7516])).

fof(f7511,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7510,f300])).

fof(f7510,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6112,f264])).

fof(f6112,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f1401,f1412,f64])).

fof(f7509,plain,
    ( spl5_1210
    | ~ spl5_36
    | ~ spl5_42
    | spl5_67
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7508,f1411,f410,f299,f263,f7504])).

fof(f7508,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_67
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7507,f300])).

fof(f7507,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_67
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6111,f264])).

fof(f6111,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_67
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f411,f1412,f64])).

fof(f7506,plain,
    ( spl5_1210
    | ~ spl5_36
    | ~ spl5_42
    | spl5_201
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7499,f1411,f1240,f299,f263,f7504])).

fof(f7499,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_201
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7498,f300])).

fof(f7498,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_201
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6110,f264])).

fof(f6110,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_201
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f1241,f1412,f64])).

fof(f7497,plain,
    ( spl5_1208
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7490,f1411,f390,f299,f263,f7495])).

fof(f7495,plain,
    ( spl5_1208
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1208])])).

fof(f7490,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7489,f300])).

fof(f7489,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_63
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6109,f264])).

fof(f6109,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_63
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f391,f1412,f64])).

fof(f7488,plain,
    ( spl5_1206
    | spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7481,f1411,f299,f263,f223,f7486])).

fof(f7486,plain,
    ( spl5_1206
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1206])])).

fof(f7481,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7480,f300])).

fof(f7480,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6106,f264])).

fof(f6106,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_31
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f224,f1412,f64])).

fof(f7479,plain,
    ( spl5_1204
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7478,f1411,f299,f263,f115,f7471])).

fof(f7478,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7477,f300])).

fof(f7477,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7476,f264])).

fof(f7476,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6105,f116])).

fof(f6105,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) = k1_xboole_0
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f1412,f59])).

fof(f7473,plain,
    ( spl5_1204
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f7466,f1411,f299,f263,f115,f7471])).

fof(f7466,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f7465,f300])).

fof(f7465,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6294,f264])).

fof(f6294,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6105,f116])).

fof(f7464,plain,
    ( ~ spl5_1203
    | ~ spl5_36
    | spl5_233 ),
    inference(avatar_split_clause,[],[f7463,f1488,f263,f7431])).

fof(f1488,plain,
    ( spl5_233
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_233])])).

fof(f7463,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_233 ),
    inference(forward_demodulation,[],[f1489,f264])).

fof(f1489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_233 ),
    inference(avatar_component_clause,[],[f1488])).

fof(f7456,plain,
    ( ~ spl5_1203
    | ~ spl5_42
    | spl5_403
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7455,f2490,f2469,f299,f7431])).

fof(f2469,plain,
    ( spl5_403
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_403])])).

fof(f2490,plain,
    ( spl5_408
  <=> k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_408])])).

fof(f7455,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_403
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2554,f300])).

fof(f2554,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_403
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2470,f2491])).

fof(f2491,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_408 ),
    inference(avatar_component_clause,[],[f2490])).

fof(f2470,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_403 ),
    inference(avatar_component_clause,[],[f2469])).

fof(f7452,plain,
    ( ~ spl5_1203
    | ~ spl5_36
    | spl5_405
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7451,f2490,f2476,f263,f7431])).

fof(f2476,plain,
    ( spl5_405
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_405])])).

fof(f7451,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_405
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2553,f264])).

fof(f2553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_405
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2477,f2491])).

fof(f2477,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_405 ),
    inference(avatar_component_clause,[],[f2476])).

fof(f7441,plain,
    ( ~ spl5_1203
    | ~ spl5_42
    | spl5_525
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7440,f3100,f3078,f299,f7431])).

fof(f3078,plain,
    ( spl5_525
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_525])])).

fof(f7440,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_525
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7439,f300])).

fof(f7439,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_525
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3079,f3101])).

fof(f3079,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_525 ),
    inference(avatar_component_clause,[],[f3078])).

fof(f7438,plain,
    ( ~ spl5_1203
    | ~ spl5_42
    | spl5_525
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7437,f3100,f3078,f299,f7431])).

fof(f7437,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_525
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3188,f300])).

fof(f3188,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_525
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3079,f3101])).

fof(f7436,plain,
    ( ~ spl5_1203
    | ~ spl5_36
    | spl5_527
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7435,f3100,f3085,f263,f7431])).

fof(f3085,plain,
    ( spl5_527
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_527])])).

fof(f7435,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_527
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7434,f264])).

fof(f7434,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_527
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3086,f3101])).

fof(f3086,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_527 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f7433,plain,
    ( ~ spl5_1203
    | ~ spl5_36
    | spl5_527
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7426,f3100,f3085,f263,f7431])).

fof(f7426,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_527
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3187,f264])).

fof(f3187,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_527
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3086,f3101])).

fof(f7397,plain,
    ( ~ spl5_951
    | spl5_955 ),
    inference(avatar_split_clause,[],[f6320,f5487,f5467])).

fof(f5467,plain,
    ( spl5_951
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_951])])).

fof(f5487,plain,
    ( spl5_955
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_955])])).

fof(f6320,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_955 ),
    inference(unit_resulting_resolution,[],[f5488,f69])).

fof(f5488,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_955 ),
    inference(avatar_component_clause,[],[f5487])).

fof(f7396,plain,
    ( ~ spl5_951
    | spl5_955 ),
    inference(avatar_split_clause,[],[f6326,f5487,f5467])).

fof(f6326,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_955 ),
    inference(resolution,[],[f5488,f69])).

fof(f7395,plain,
    ( ~ spl5_1015
    | ~ spl5_36
    | ~ spl5_42
    | spl5_219 ),
    inference(avatar_split_clause,[],[f7394,f1381,f299,f263,f5779])).

fof(f5779,plain,
    ( spl5_1015
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1015])])).

fof(f1381,plain,
    ( spl5_219
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_219])])).

fof(f7394,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f7393,f300])).

fof(f7393,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f4701,f264])).

fof(f4701,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f69])).

fof(f1382,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_219 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f7392,plain,
    ( ~ spl5_1015
    | ~ spl5_36
    | ~ spl5_42
    | spl5_219 ),
    inference(avatar_split_clause,[],[f7391,f1381,f299,f263,f5779])).

fof(f7391,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f7390,f300])).

fof(f7390,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f4708,f264])).

fof(f4708,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_219 ),
    inference(resolution,[],[f1382,f69])).

fof(f7388,plain,
    ( ~ spl5_1125
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7387,f299,f263,f182,f6674])).

fof(f182,plain,
    ( spl5_21
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f7387,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7386,f300])).

fof(f7386,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f183,f264])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f7385,plain,
    ( spl5_1182
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7384,f299,f263,f182,f7049])).

fof(f7049,plain,
    ( spl5_1182
  <=> r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1182])])).

fof(f7384,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7383,f300])).

fof(f7383,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,o_0_0_xboole_0)),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f186,f264])).

fof(f186,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f60,f183,f63])).

fof(f7378,plain,
    ( spl5_1182
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7377,f299,f263,f182,f7049])).

fof(f7377,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7376,f300])).

fof(f7376,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,o_0_0_xboole_0)),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f835,f264])).

fof(f835,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f60,f183,f63])).

fof(f7373,plain,
    ( ~ spl5_1125
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7372,f299,f263,f182,f6674])).

fof(f7372,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1254,f264])).

fof(f1254,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_21
    | ~ spl5_42 ),
    inference(superposition,[],[f183,f300])).

fof(f7369,plain,
    ( spl5_1182
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7368,f299,f263,f182,f7049])).

fof(f7368,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7367,f300])).

fof(f7367,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,o_0_0_xboole_0)),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_21
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f1423,f264])).

fof(f1423,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f60,f183,f63])).

fof(f7366,plain,
    ( spl5_1166
    | spl5_21
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7365,f299,f263,f198,f182,f6930])).

fof(f6930,plain,
    ( spl5_1166
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1166])])).

fof(f198,plain,
    ( spl5_24
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f7365,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7364,f300])).

fof(f7364,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2420,f264])).

fof(f2420,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f183,f199,f64])).

fof(f199,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f198])).

fof(f7360,plain,
    ( spl5_1166
    | spl5_21
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f7359,f307,f299,f263,f182,f6930])).

fof(f307,plain,
    ( spl5_44
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f7359,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7358,f264])).

fof(f7358,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3201,f300])).

fof(f3201,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_21
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f183,f308,f64])).

fof(f308,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f307])).

fof(f7357,plain,
    ( spl5_1182
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7356,f299,f263,f191,f7049])).

fof(f191,plain,
    ( spl5_22
  <=> r2_hidden(sK3(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f7356,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7355,f300])).

fof(f7355,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,o_0_0_xboole_0)),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f192,f264])).

fof(f192,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f7354,plain,
    ( ~ spl5_1125
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7353,f299,f263,f191,f6674])).

fof(f7353,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7352,f300])).

fof(f7352,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4138,f264])).

fof(f4138,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f159,f192,f169])).

fof(f7351,plain,
    ( ~ spl5_1163
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7350,f3100,f354,f299,f263,f191,f6903])).

fof(f6903,plain,
    ( spl5_1163
  <=> ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1163])])).

fof(f7350,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7349,f300])).

fof(f7349,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7348,f264])).

fof(f7348,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4137,f3101])).

fof(f4137,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f355,f192,f169])).

fof(f7347,plain,
    ( ~ spl5_1201
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7340,f299,f263,f198,f191,f7345])).

fof(f7345,plain,
    ( spl5_1201
  <=> ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1201])])).

fof(f7340,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7339,f300])).

fof(f7339,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4136,f264])).

fof(f4136,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f199,f192,f169])).

fof(f7338,plain,
    ( ~ spl5_1163
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7337,f299,f263,f191,f106,f6903])).

fof(f7337,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7336,f300])).

fof(f7336,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4135,f264])).

fof(f4135,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f107,f192,f169])).

fof(f7335,plain,
    ( ~ spl5_1161
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7334,f3100,f354,f299,f263,f191,f6894])).

fof(f6894,plain,
    ( spl5_1161
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1161])])).

fof(f7334,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7333,f300])).

fof(f7333,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4164,f264])).

fof(f4164,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4130,f3101])).

fof(f4130,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_22
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f355,f192,f79])).

fof(f7332,plain,
    ( ~ spl5_1161
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7331,f3100,f354,f299,f263,f191,f6894])).

fof(f7331,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7330,f300])).

fof(f7330,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7329,f264])).

fof(f7329,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4130,f3101])).

fof(f7328,plain,
    ( ~ spl5_1199
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7321,f299,f263,f198,f191,f7326])).

fof(f7326,plain,
    ( spl5_1199
  <=> ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1199])])).

fof(f7321,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7320,f300])).

fof(f7320,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4129,f264])).

fof(f4129,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_22
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f199,f192,f79])).

fof(f7319,plain,
    ( ~ spl5_1161
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7318,f299,f263,f191,f106,f6894])).

fof(f7318,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7317,f300])).

fof(f7317,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4128,f264])).

fof(f4128,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f107,f192,f79])).

fof(f7316,plain,
    ( ~ spl5_1125
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7315,f299,f263,f191,f6674])).

fof(f7315,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7314,f300])).

fof(f7314,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4127,f264])).

fof(f4127,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f192,f71])).

fof(f7313,plain,
    ( ~ spl5_1163
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7312,f299,f263,f191,f106,f6903])).

fof(f7312,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7311,f300])).

fof(f7311,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4125,f264])).

fof(f4125,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f118,f192,f65])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f107,f71])).

fof(f7310,plain,
    ( ~ spl5_1161
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7309,f2490,f299,f263,f198,f191,f6894])).

fof(f7309,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7308,f300])).

fof(f7308,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4172,f264])).

fof(f4172,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4129,f2491])).

fof(f7307,plain,
    ( ~ spl5_1125
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7306,f299,f263,f191,f6674])).

fof(f7306,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7305,f300])).

fof(f7305,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f4141,f264])).

fof(f4141,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f192,f71])).

fof(f7298,plain,
    ( ~ spl5_1163
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7297,f3100,f354,f299,f263,f191,f6903])).

fof(f7297,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7296,f300])).

fof(f7296,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4146,f264])).

fof(f4146,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4137,f3101])).

fof(f7295,plain,
    ( ~ spl5_1163
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7294,f2490,f299,f263,f198,f191,f6903])).

fof(f7294,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7293,f300])).

fof(f7293,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4154,f264])).

fof(f4154,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4136,f2491])).

fof(f7284,plain,
    ( spl5_1170
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7283,f299,f263,f198,f106,f6948])).

fof(f7283,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7282,f300])).

fof(f7282,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2430,f264])).

fof(f2430,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f107,f199,f70])).

fof(f7281,plain,
    ( spl5_1170
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7280,f299,f263,f198,f106,f6948])).

fof(f7280,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7279,f300])).

fof(f7279,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2428,f264])).

fof(f2428,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f107,f199,f70])).

fof(f7278,plain,
    ( spl5_1168
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_137 ),
    inference(avatar_split_clause,[],[f7277,f816,f299,f263,f198,f6939])).

fof(f6939,plain,
    ( spl5_1168
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1168])])).

fof(f7277,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_137 ),
    inference(forward_demodulation,[],[f7276,f300])).

fof(f7276,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_137 ),
    inference(forward_demodulation,[],[f2427,f264])).

fof(f2427,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f199,f64])).

fof(f7275,plain,
    ( spl5_1166
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_129 ),
    inference(avatar_split_clause,[],[f7274,f776,f299,f263,f198,f6930])).

fof(f776,plain,
    ( spl5_129
  <=> ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f7274,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f7273,f300])).

fof(f7273,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f2421,f264])).

fof(f2421,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f777,f199,f64])).

fof(f777,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_129 ),
    inference(avatar_component_clause,[],[f776])).

fof(f7272,plain,
    ( spl5_1170
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7271,f299,f263,f198,f115,f6948])).

fof(f7271,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7270,f300])).

fof(f7270,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f7269,f264])).

fof(f7269,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f2419,f116])).

fof(f2419,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_xboole_0
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f199,f59])).

fof(f7268,plain,
    ( spl5_1170
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f7267,f299,f263,f198,f115,f6948])).

fof(f7267,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f7266,f300])).

fof(f7266,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2550,f264])).

fof(f2550,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f2419,f116])).

fof(f7265,plain,
    ( spl5_1196
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_223 ),
    inference(avatar_split_clause,[],[f7264,f1393,f299,f263,f198,f7235])).

fof(f7235,plain,
    ( spl5_1196
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1196])])).

fof(f7264,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_223 ),
    inference(forward_demodulation,[],[f7263,f300])).

fof(f7263,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_223 ),
    inference(forward_demodulation,[],[f2962,f264])).

fof(f2962,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f199,f1394,f64])).

fof(f7262,plain,
    ( spl5_1192
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7261,f667,f299,f263,f198,f7214])).

fof(f7214,plain,
    ( spl5_1192
  <=> v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1192])])).

fof(f667,plain,
    ( spl5_117
  <=> ~ v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f7261,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f7260,f300])).

fof(f7260,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f2990,f264])).

fof(f2990,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f199,f668,f64])).

fof(f668,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | ~ spl5_117 ),
    inference(avatar_component_clause,[],[f667])).

fof(f7259,plain,
    ( spl5_1158
    | ~ spl5_24
    | ~ spl5_42
    | spl5_117
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7258,f2490,f667,f299,f198,f6885])).

fof(f6885,plain,
    ( spl5_1158
  <=> v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1158])])).

fof(f7258,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_42
    | ~ spl5_117
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2993,f300])).

fof(f2993,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_117
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2990,f2491])).

fof(f7257,plain,
    ( spl5_1196
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_225 ),
    inference(avatar_split_clause,[],[f7256,f1400,f299,f263,f198,f7235])).

fof(f7256,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_225 ),
    inference(forward_demodulation,[],[f7255,f300])).

fof(f7255,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_225 ),
    inference(forward_demodulation,[],[f2997,f264])).

fof(f2997,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f199,f1401,f64])).

fof(f7254,plain,
    ( spl5_1170
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7253,f3100,f354,f299,f263,f198,f6948])).

fof(f7253,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7252,f300])).

fof(f7252,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7251,f264])).

fof(f7251,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3039,f3101])).

fof(f3039,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_24
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f199,f355,f70])).

fof(f7250,plain,
    ( spl5_1170
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7249,f3100,f354,f299,f263,f198,f6948])).

fof(f7249,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7248,f300])).

fof(f7248,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7247,f264])).

fof(f7247,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3036,f3101])).

fof(f3036,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_24
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f199,f355,f70])).

fof(f7246,plain,
    ( spl5_1170
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7245,f2490,f307,f299,f263,f198,f6948])).

fof(f7245,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7244,f264])).

fof(f7244,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3278,f300])).

fof(f3278,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3213,f2491])).

fof(f3213,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)
    | ~ spl5_24
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f199,f308,f70])).

fof(f7243,plain,
    ( spl5_1170
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7242,f2490,f307,f299,f263,f198,f6948])).

fof(f7242,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7241,f264])).

fof(f7241,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3283,f300])).

fof(f3283,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3209,f2491])).

fof(f3209,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)
    | ~ spl5_24
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f199,f308,f70])).

fof(f7240,plain,
    ( spl5_1196
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_223 ),
    inference(avatar_split_clause,[],[f7239,f1393,f299,f263,f198,f7235])).

fof(f7239,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_223 ),
    inference(forward_demodulation,[],[f7238,f300])).

fof(f7238,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_223 ),
    inference(forward_demodulation,[],[f3505,f264])).

fof(f3505,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f199,f1394,f64])).

fof(f7237,plain,
    ( spl5_1196
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_225 ),
    inference(avatar_split_clause,[],[f7230,f1400,f299,f263,f198,f7235])).

fof(f7230,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_225 ),
    inference(forward_demodulation,[],[f7229,f300])).

fof(f7229,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_225 ),
    inference(forward_demodulation,[],[f3671,f264])).

fof(f3671,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f199,f1401,f64])).

fof(f7228,plain,
    ( spl5_1194
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59 ),
    inference(avatar_split_clause,[],[f7227,f376,f299,f263,f198,f7223])).

fof(f7223,plain,
    ( spl5_1194
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1194])])).

fof(f7227,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f7226,f300])).

fof(f7226,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f3843,f264])).

fof(f3843,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f199,f377,f64])).

fof(f7225,plain,
    ( spl5_1194
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61 ),
    inference(avatar_split_clause,[],[f7218,f383,f299,f263,f198,f7223])).

fof(f7218,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f7217,f300])).

fof(f7217,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f4044,f264])).

fof(f4044,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f199,f384,f64])).

fof(f7216,plain,
    ( spl5_1192
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_237 ),
    inference(avatar_split_clause,[],[f7209,f1500,f299,f263,f198,f7214])).

fof(f1500,plain,
    ( spl5_237
  <=> ~ v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f7209,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f7208,f300])).

fof(f7208,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f4601,f264])).

fof(f4601,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f199,f1501,f64])).

fof(f1501,plain,
    ( ~ v1_xboole_0(sK3(sK1))
    | ~ spl5_237 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f7207,plain,
    ( spl5_1158
    | ~ spl5_24
    | ~ spl5_36
    | spl5_237
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7206,f2490,f1500,f263,f198,f6885])).

fof(f7206,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_237
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4620,f264])).

fof(f4620,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_237
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4601,f2491])).

fof(f7205,plain,
    ( spl5_1190
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63 ),
    inference(avatar_split_clause,[],[f7198,f390,f299,f263,f198,f7203])).

fof(f7203,plain,
    ( spl5_1190
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1190])])).

fof(f7198,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f7197,f300])).

fof(f7197,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f4633,f264])).

fof(f4633,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f199,f391,f64])).

fof(f7196,plain,
    ( spl5_1188
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227 ),
    inference(avatar_split_clause,[],[f7189,f1408,f299,f263,f198,f7194])).

fof(f1408,plain,
    ( spl5_227
  <=> ~ v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_227])])).

fof(f7189,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7188,f300])).

fof(f7188,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f4750,f264])).

fof(f4750,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f199,f1409,f64])).

fof(f1409,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_227 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f7187,plain,
    ( spl5_1154
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7186,f2490,f1408,f299,f263,f198,f6869])).

fof(f7186,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7185,f300])).

fof(f7185,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_36
    | ~ spl5_227
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4769,f264])).

fof(f4769,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_227
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4750,f2491])).

fof(f7180,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7179,f3100,f354,f307,f299,f263,f6948])).

fof(f7179,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7178,f264])).

fof(f7178,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3281,f300])).

fof(f3281,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3210,f3101])).

fof(f3210,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_44
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f355,f308,f70])).

fof(f7173,plain,
    ( spl5_1170
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f7172,f307,f299,f263,f115,f6948])).

fof(f7172,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7171,f264])).

fof(f7171,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3335,f300])).

fof(f3335,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3200,f116])).

fof(f3200,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = k1_xboole_0
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f308,f59])).

fof(f7170,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7169,f3100,f354,f307,f299,f263,f6948])).

fof(f7169,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7168,f264])).

fof(f7168,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7167,f300])).

fof(f7167,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3214,f3101])).

fof(f3214,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_44
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f355,f308,f70])).

fof(f7166,plain,
    ( spl5_1170
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f7165,f307,f299,f263,f106,f6948])).

fof(f7165,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7164,f264])).

fof(f7164,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3212,f300])).

fof(f3212,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f107,f308,f70])).

fof(f7163,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7162,f3100,f354,f307,f299,f263,f6948])).

fof(f7162,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7161,f264])).

fof(f7161,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7160,f300])).

fof(f7160,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3210,f3101])).

fof(f7159,plain,
    ( spl5_1170
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f7158,f307,f299,f263,f106,f6948])).

fof(f7158,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7157,f264])).

fof(f7157,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3208,f300])).

fof(f3208,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f107,f308,f70])).

fof(f7156,plain,
    ( spl5_1168
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | spl5_137 ),
    inference(avatar_split_clause,[],[f7155,f816,f307,f299,f263,f6939])).

fof(f7155,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_137 ),
    inference(forward_demodulation,[],[f7154,f264])).

fof(f7154,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_137 ),
    inference(forward_demodulation,[],[f3207,f300])).

fof(f3207,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_44
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f308,f64])).

fof(f7153,plain,
    ( spl5_1170
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f7152,f307,f299,f263,f115,f6948])).

fof(f7152,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7151,f264])).

fof(f7151,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f7150,f300])).

fof(f7150,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f3200,f116])).

fof(f7149,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7148,f3100,f354,f307,f299,f263,f6948])).

fof(f7148,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7147,f264])).

fof(f7147,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3270,f300])).

fof(f3270,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3214,f3101])).

fof(f7146,plain,
    ( ~ spl5_1185
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7145,f667,f299,f7069])).

fof(f7069,plain,
    ( spl5_1185
  <=> ~ v1_xboole_0(sK3(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1185])])).

fof(f7145,plain,
    ( ~ v1_xboole_0(sK3(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f668,f300])).

fof(f7144,plain,
    ( spl5_1158
    | ~ spl5_6
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7143,f667,f299,f106,f6885])).

fof(f7143,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f2333,f300])).

fof(f2333,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f107,f668,f64])).

fof(f7142,plain,
    ( spl5_1156
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7141,f667,f299,f6877])).

fof(f6877,plain,
    ( spl5_1156
  <=> r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1156])])).

fof(f7141,plain,
    ( r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f2332,f300])).

fof(f2332,plain,
    ( r2_hidden(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f60,f668,f63])).

fof(f7140,plain,
    ( spl5_1158
    | ~ spl5_6
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7139,f667,f299,f106,f6885])).

fof(f7139,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f2989,f300])).

fof(f2989,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f107,f668,f64])).

fof(f7138,plain,
    ( spl5_1156
    | ~ spl5_42
    | spl5_117 ),
    inference(avatar_split_clause,[],[f7137,f667,f299,f6877])).

fof(f7137,plain,
    ( r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_117 ),
    inference(forward_demodulation,[],[f2988,f300])).

fof(f2988,plain,
    ( r2_hidden(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f60,f668,f63])).

fof(f7136,plain,
    ( spl5_1158
    | ~ spl5_42
    | ~ spl5_54
    | spl5_117
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7135,f3100,f667,f354,f299,f6885])).

fof(f7135,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_117
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7134,f300])).

fof(f7134,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_117
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3034,f3101])).

fof(f3034,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f668,f355,f64])).

fof(f7133,plain,
    ( ~ spl5_1125
    | ~ spl5_36
    | spl5_129 ),
    inference(avatar_split_clause,[],[f7132,f776,f263,f6674])).

fof(f7132,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f777,f264])).

fof(f7130,plain,
    ( spl5_1182
    | ~ spl5_36
    | spl5_129 ),
    inference(avatar_split_clause,[],[f7129,f776,f263,f7049])).

fof(f7129,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f2061,f264])).

fof(f2061,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1)),k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f60,f777,f63])).

fof(f7127,plain,
    ( spl5_1182
    | ~ spl5_36
    | spl5_129 ),
    inference(avatar_split_clause,[],[f7126,f776,f263,f7049])).

fof(f7126,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_129 ),
    inference(forward_demodulation,[],[f2197,f264])).

fof(f2197,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1)),k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f60,f777,f63])).

fof(f7108,plain,
    ( ~ spl5_137
    | ~ spl5_6
    | spl5_157 ),
    inference(avatar_split_clause,[],[f3678,f957,f106,f816])).

fof(f957,plain,
    ( spl5_157
  <=> o_0_0_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f3678,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_6
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f107,f958,f70])).

fof(f958,plain,
    ( o_0_0_xboole_0 != sK2
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f957])).

fof(f7107,plain,
    ( ~ spl5_137
    | ~ spl5_6
    | spl5_157 ),
    inference(avatar_split_clause,[],[f3677,f957,f106,f816])).

fof(f3677,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_6
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f107,f958,f70])).

fof(f7104,plain,
    ( ~ spl5_1125
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | spl5_221 ),
    inference(avatar_split_clause,[],[f7103,f1385,f299,f263,f106,f6674])).

fof(f1385,plain,
    ( spl5_221
  <=> k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_221])])).

fof(f7103,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_221 ),
    inference(forward_demodulation,[],[f7102,f300])).

fof(f7102,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_221 ),
    inference(forward_demodulation,[],[f2389,f264])).

fof(f2389,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_6
    | ~ spl5_221 ),
    inference(unit_resulting_resolution,[],[f107,f1386,f70])).

fof(f1386,plain,
    ( k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0
    | ~ spl5_221 ),
    inference(avatar_component_clause,[],[f1385])).

fof(f7101,plain,
    ( ~ spl5_1125
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | spl5_221 ),
    inference(avatar_split_clause,[],[f7100,f1385,f299,f263,f106,f6674])).

fof(f7100,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_221 ),
    inference(forward_demodulation,[],[f7099,f300])).

fof(f7099,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_221 ),
    inference(forward_demodulation,[],[f2388,f264])).

fof(f2388,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_6
    | ~ spl5_221 ),
    inference(unit_resulting_resolution,[],[f107,f1386,f70])).

fof(f7098,plain,
    ( ~ spl5_1187
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227 ),
    inference(avatar_split_clause,[],[f7091,f1408,f299,f263,f7096])).

fof(f7091,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7090,f300])).

fof(f7090,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f1409,f264])).

fof(f7089,plain,
    ( spl5_1154
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | spl5_227
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7088,f3100,f1408,f354,f299,f263,f6869])).

fof(f7088,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7087,f300])).

fof(f7087,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7086,f264])).

fof(f7086,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4751,f3101])).

fof(f4751,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f355,f1409,f64])).

fof(f7085,plain,
    ( spl5_1154
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227 ),
    inference(avatar_split_clause,[],[f7084,f1408,f299,f263,f106,f6869])).

fof(f7084,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7083,f300])).

fof(f7083,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f4749,f264])).

fof(f4749,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f107,f1409,f64])).

fof(f7082,plain,
    ( spl5_1152
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227 ),
    inference(avatar_split_clause,[],[f7081,f1408,f299,f263,f6860])).

fof(f6860,plain,
    ( spl5_1152
  <=> r2_hidden(sK3(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1152])])).

fof(f7081,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7080,f300])).

fof(f7080,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f4748,f264])).

fof(f4748,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f60,f1409,f63])).

fof(f7079,plain,
    ( ~ spl5_1125
    | spl5_960
    | ~ spl5_36
    | ~ spl5_42
    | spl5_227 ),
    inference(avatar_split_clause,[],[f7078,f1408,f299,f263,f5513,f6674])).

fof(f5513,plain,
    ( spl5_960
  <=> v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_960])])).

fof(f7078,plain,
    ( v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7077,f300])).

fof(f7077,plain,
    ( v1_xboole_0(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7076,f264])).

fof(f7076,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f7075,f300])).

fof(f7075,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_227 ),
    inference(forward_demodulation,[],[f4753,f264])).

fof(f4753,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_227 ),
    inference(resolution,[],[f1409,f64])).

fof(f7074,plain,
    ( spl5_1154
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | spl5_227
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7073,f3100,f1408,f354,f299,f263,f6869])).

fof(f7073,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7072,f300])).

fof(f7072,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4761,f264])).

fof(f4761,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_227
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4751,f3101])).

fof(f7071,plain,
    ( ~ spl5_1185
    | ~ spl5_36
    | spl5_237 ),
    inference(avatar_split_clause,[],[f7064,f1500,f263,f7069])).

fof(f7064,plain,
    ( ~ v1_xboole_0(sK3(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f1501,f264])).

fof(f7063,plain,
    ( spl5_1158
    | ~ spl5_36
    | ~ spl5_54
    | spl5_237
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7062,f3100,f1500,f354,f263,f6885])).

fof(f7062,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_237
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f7061,f264])).

fof(f7061,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_237
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4602,f3101])).

fof(f4602,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f355,f1501,f64])).

fof(f7060,plain,
    ( spl5_1158
    | ~ spl5_6
    | ~ spl5_36
    | spl5_237 ),
    inference(avatar_split_clause,[],[f7059,f1500,f263,f106,f6885])).

fof(f7059,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f4600,f264])).

fof(f4600,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f107,f1501,f64])).

fof(f7058,plain,
    ( spl5_1156
    | ~ spl5_36
    | spl5_237 ),
    inference(avatar_split_clause,[],[f7057,f1500,f263,f6877])).

fof(f7057,plain,
    ( r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_237 ),
    inference(forward_demodulation,[],[f4598,f264])).

fof(f4598,plain,
    ( r2_hidden(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f60,f1501,f63])).

fof(f7056,plain,
    ( spl5_1158
    | ~ spl5_36
    | ~ spl5_54
    | spl5_237
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f7055,f3100,f1500,f354,f263,f6885])).

fof(f7055,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_237
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4612,f264])).

fof(f4612,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_237
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4602,f3101])).

fof(f7051,plain,
    ( spl5_1182
    | ~ spl5_36
    | ~ spl5_330 ),
    inference(avatar_split_clause,[],[f7044,f2076,f263,f7049])).

fof(f2076,plain,
    ( spl5_330
  <=> r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1)),k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_330])])).

fof(f7044,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_330 ),
    inference(forward_demodulation,[],[f2077,f264])).

fof(f2077,plain,
    ( r2_hidden(sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1)),k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_330 ),
    inference(avatar_component_clause,[],[f2076])).

fof(f7039,plain,
    ( spl5_1158
    | ~ spl5_42
    | ~ spl5_386 ),
    inference(avatar_split_clause,[],[f7038,f2347,f299,f6885])).

fof(f2347,plain,
    ( spl5_386
  <=> v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_386])])).

fof(f7038,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_386 ),
    inference(forward_demodulation,[],[f2348,f300])).

fof(f2348,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_386 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f7037,plain,
    ( spl5_1156
    | ~ spl5_42
    | ~ spl5_388 ),
    inference(avatar_split_clause,[],[f7036,f2354,f299,f6877])).

fof(f2354,plain,
    ( spl5_388
  <=> r2_hidden(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_388])])).

fof(f7036,plain,
    ( r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_388 ),
    inference(forward_demodulation,[],[f2355,f300])).

fof(f2355,plain,
    ( r2_hidden(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl5_388 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f7032,plain,
    ( spl5_1172
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_402 ),
    inference(avatar_split_clause,[],[f7031,f2466,f299,f263,f6957])).

fof(f6957,plain,
    ( spl5_1172
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1172])])).

fof(f2466,plain,
    ( spl5_402
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_402])])).

fof(f7031,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_402 ),
    inference(forward_demodulation,[],[f7030,f300])).

fof(f7030,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_402 ),
    inference(forward_demodulation,[],[f2467,f264])).

fof(f2467,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_402 ),
    inference(avatar_component_clause,[],[f2466])).

fof(f7029,plain,
    ( spl5_1172
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_404 ),
    inference(avatar_split_clause,[],[f7028,f2473,f299,f263,f6957])).

fof(f2473,plain,
    ( spl5_404
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_404])])).

fof(f7028,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_404 ),
    inference(forward_demodulation,[],[f7027,f300])).

fof(f7027,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_404 ),
    inference(forward_demodulation,[],[f2474,f264])).

fof(f2474,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_404 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f7026,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7025,f2490,f299,f263,f6948])).

fof(f7025,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7024,f300])).

fof(f7024,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2491,f264])).

fof(f7023,plain,
    ( spl5_1168
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_410 ),
    inference(avatar_split_clause,[],[f7022,f2498,f299,f263,f6939])).

fof(f2498,plain,
    ( spl5_410
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_410])])).

fof(f7022,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_410 ),
    inference(forward_demodulation,[],[f7021,f300])).

fof(f7021,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_410 ),
    inference(forward_demodulation,[],[f2499,f264])).

fof(f2499,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_410 ),
    inference(avatar_component_clause,[],[f2498])).

fof(f7020,plain,
    ( spl5_1166
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_422 ),
    inference(avatar_split_clause,[],[f7019,f2540,f299,f263,f6930])).

fof(f2540,plain,
    ( spl5_422
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_422])])).

fof(f7019,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_422 ),
    inference(forward_demodulation,[],[f7018,f300])).

fof(f7018,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_422 ),
    inference(forward_demodulation,[],[f2541,f264])).

fof(f2541,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_422 ),
    inference(avatar_component_clause,[],[f2540])).

fof(f7017,plain,
    ( spl5_1166
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_424 ),
    inference(avatar_split_clause,[],[f7016,f2547,f299,f263,f6930])).

fof(f2547,plain,
    ( spl5_424
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_424])])).

fof(f7016,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_424 ),
    inference(forward_demodulation,[],[f7015,f300])).

fof(f7015,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_424 ),
    inference(forward_demodulation,[],[f2548,f264])).

fof(f2548,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_424 ),
    inference(avatar_component_clause,[],[f2547])).

fof(f7014,plain,
    ( ~ spl5_1175
    | ~ spl5_36
    | ~ spl5_42
    | spl5_433 ),
    inference(avatar_split_clause,[],[f7013,f2604,f299,f263,f6976])).

fof(f6976,plain,
    ( spl5_1175
  <=> ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1175])])).

fof(f2604,plain,
    ( spl5_433
  <=> ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_433])])).

fof(f7013,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_433 ),
    inference(forward_demodulation,[],[f7012,f264])).

fof(f7012,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_433 ),
    inference(forward_demodulation,[],[f2605,f300])).

fof(f2605,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_433 ),
    inference(avatar_component_clause,[],[f2604])).

fof(f7011,plain,
    ( ~ spl5_1181
    | ~ spl5_36
    | ~ spl5_42
    | spl5_435 ),
    inference(avatar_split_clause,[],[f7004,f2612,f299,f263,f7009])).

fof(f7009,plain,
    ( spl5_1181
  <=> ~ r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1181])])).

fof(f2612,plain,
    ( spl5_435
  <=> ~ r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_435])])).

fof(f7004,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_435 ),
    inference(forward_demodulation,[],[f7003,f264])).

fof(f7003,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_435 ),
    inference(forward_demodulation,[],[f2613,f300])).

fof(f2613,plain,
    ( ~ r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_435 ),
    inference(avatar_component_clause,[],[f2612])).

fof(f7002,plain,
    ( ~ spl5_1179
    | ~ spl5_42
    | spl5_449 ),
    inference(avatar_split_clause,[],[f6995,f2693,f299,f7000])).

fof(f7000,plain,
    ( spl5_1179
  <=> o_0_0_xboole_0 != sK3(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1179])])).

fof(f2693,plain,
    ( spl5_449
  <=> o_0_0_xboole_0 != sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_449])])).

fof(f6995,plain,
    ( o_0_0_xboole_0 != sK3(o_0_0_xboole_0)
    | ~ spl5_42
    | ~ spl5_449 ),
    inference(forward_demodulation,[],[f2694,f300])).

fof(f2694,plain,
    ( o_0_0_xboole_0 != sK3(sK0)
    | ~ spl5_449 ),
    inference(avatar_component_clause,[],[f2693])).

fof(f6994,plain,
    ( spl5_1176
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_452 ),
    inference(avatar_split_clause,[],[f6993,f2714,f299,f263,f6989])).

fof(f6989,plain,
    ( spl5_1176
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK3(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1176])])).

fof(f2714,plain,
    ( spl5_452
  <=> v1_xboole_0(k1_funct_2(sK1,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_452])])).

fof(f6993,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK3(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_452 ),
    inference(forward_demodulation,[],[f6992,f264])).

fof(f6992,plain,
    ( v1_xboole_0(k1_funct_2(sK1,sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_452 ),
    inference(forward_demodulation,[],[f2715,f300])).

fof(f2715,plain,
    ( v1_xboole_0(k1_funct_2(sK1,sK3(sK0)))
    | ~ spl5_452 ),
    inference(avatar_component_clause,[],[f2714])).

fof(f6991,plain,
    ( spl5_1176
    | ~ spl5_42
    | ~ spl5_454 ),
    inference(avatar_split_clause,[],[f6984,f2721,f299,f6989])).

fof(f2721,plain,
    ( spl5_454
  <=> v1_xboole_0(k1_funct_2(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_454])])).

fof(f6984,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_454 ),
    inference(forward_demodulation,[],[f2722,f300])).

fof(f2722,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK3(sK0)))
    | ~ spl5_454 ),
    inference(avatar_component_clause,[],[f2721])).

fof(f6983,plain,
    ( spl5_1158
    | ~ spl5_42
    | ~ spl5_530
    | ~ spl5_532 ),
    inference(avatar_split_clause,[],[f6982,f3111,f3100,f299,f6885])).

fof(f3111,plain,
    ( spl5_532
  <=> v1_xboole_0(k1_funct_2(sK3(sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_532])])).

fof(f6982,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_530
    | ~ spl5_532 ),
    inference(forward_demodulation,[],[f6981,f300])).

fof(f6981,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_532 ),
    inference(forward_demodulation,[],[f3112,f3101])).

fof(f3112,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_532 ),
    inference(avatar_component_clause,[],[f3111])).

fof(f6980,plain,
    ( spl5_144
    | ~ spl5_530
    | ~ spl5_534 ),
    inference(avatar_split_clause,[],[f6979,f3118,f3100,f852])).

fof(f852,plain,
    ( spl5_144
  <=> v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f3118,plain,
    ( spl5_534
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_534])])).

fof(f6979,plain,
    ( v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_534 ),
    inference(forward_demodulation,[],[f3119,f3101])).

fof(f3119,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_534 ),
    inference(avatar_component_clause,[],[f3118])).

fof(f6978,plain,
    ( ~ spl5_1175
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_530
    | spl5_549 ),
    inference(avatar_split_clause,[],[f6971,f3164,f3100,f299,f263,f6976])).

fof(f3164,plain,
    ( spl5_549
  <=> ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_549])])).

fof(f6971,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_530
    | ~ spl5_549 ),
    inference(forward_demodulation,[],[f6970,f264])).

fof(f6970,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_530
    | ~ spl5_549 ),
    inference(forward_demodulation,[],[f6969,f300])).

fof(f6969,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_549 ),
    inference(forward_demodulation,[],[f3165,f3101])).

fof(f3165,plain,
    ( ~ v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_549 ),
    inference(avatar_component_clause,[],[f3164])).

fof(f6962,plain,
    ( spl5_1172
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_560 ),
    inference(avatar_split_clause,[],[f6961,f3250,f299,f263,f6957])).

fof(f3250,plain,
    ( spl5_560
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_560])])).

fof(f6961,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_560 ),
    inference(forward_demodulation,[],[f6960,f264])).

fof(f6960,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_560 ),
    inference(forward_demodulation,[],[f3251,f300])).

fof(f3251,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_560 ),
    inference(avatar_component_clause,[],[f3250])).

fof(f6959,plain,
    ( spl5_1172
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_562 ),
    inference(avatar_split_clause,[],[f6952,f3257,f299,f263,f6957])).

fof(f3257,plain,
    ( spl5_562
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_562])])).

fof(f6952,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_562 ),
    inference(forward_demodulation,[],[f6951,f264])).

fof(f6951,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_562 ),
    inference(forward_demodulation,[],[f3258,f300])).

fof(f3258,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_562 ),
    inference(avatar_component_clause,[],[f3257])).

fof(f6950,plain,
    ( spl5_1170
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_566 ),
    inference(avatar_split_clause,[],[f6943,f3275,f299,f263,f6948])).

fof(f3275,plain,
    ( spl5_566
  <=> k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_566])])).

fof(f6943,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_566 ),
    inference(forward_demodulation,[],[f6942,f264])).

fof(f6942,plain,
    ( k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_566 ),
    inference(forward_demodulation,[],[f3276,f300])).

fof(f3276,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0) = o_0_0_xboole_0
    | ~ spl5_566 ),
    inference(avatar_component_clause,[],[f3275])).

fof(f6941,plain,
    ( spl5_1168
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_568 ),
    inference(avatar_split_clause,[],[f6934,f3290,f299,f263,f6939])).

fof(f3290,plain,
    ( spl5_568
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_568])])).

fof(f6934,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_568 ),
    inference(forward_demodulation,[],[f6933,f264])).

fof(f6933,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_568 ),
    inference(forward_demodulation,[],[f3291,f300])).

fof(f3291,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_568 ),
    inference(avatar_component_clause,[],[f3290])).

fof(f6932,plain,
    ( spl5_1166
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_580 ),
    inference(avatar_split_clause,[],[f6925,f3332,f299,f263,f6930])).

fof(f3332,plain,
    ( spl5_580
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_580])])).

fof(f6925,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_580 ),
    inference(forward_demodulation,[],[f6924,f264])).

fof(f6924,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_580 ),
    inference(forward_demodulation,[],[f3333,f300])).

fof(f3333,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_580 ),
    inference(avatar_component_clause,[],[f3332])).

fof(f6923,plain,
    ( spl5_1164
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_598 ),
    inference(avatar_split_clause,[],[f6922,f3451,f299,f263,f6912])).

fof(f6912,plain,
    ( spl5_1164
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1164])])).

fof(f3451,plain,
    ( spl5_598
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_598])])).

fof(f6922,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_598 ),
    inference(forward_demodulation,[],[f6921,f300])).

fof(f6921,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_598 ),
    inference(forward_demodulation,[],[f3452,f264])).

fof(f3452,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_598 ),
    inference(avatar_component_clause,[],[f3451])).

fof(f6920,plain,
    ( spl5_1164
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_600 ),
    inference(avatar_split_clause,[],[f6919,f3458,f299,f263,f6912])).

fof(f3458,plain,
    ( spl5_600
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_600])])).

fof(f6919,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_600 ),
    inference(forward_demodulation,[],[f6918,f300])).

fof(f6918,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_600 ),
    inference(forward_demodulation,[],[f3459,f264])).

fof(f3459,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_600 ),
    inference(avatar_component_clause,[],[f3458])).

fof(f6917,plain,
    ( spl5_1164
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_628 ),
    inference(avatar_split_clause,[],[f6916,f3610,f299,f263,f6912])).

fof(f3610,plain,
    ( spl5_628
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_628])])).

fof(f6916,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_628 ),
    inference(forward_demodulation,[],[f6915,f300])).

fof(f6915,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_628 ),
    inference(forward_demodulation,[],[f3611,f264])).

fof(f3611,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_628 ),
    inference(avatar_component_clause,[],[f3610])).

fof(f6914,plain,
    ( spl5_1164
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_630 ),
    inference(avatar_split_clause,[],[f6907,f3617,f299,f263,f6912])).

fof(f3617,plain,
    ( spl5_630
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_630])])).

fof(f6907,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_630 ),
    inference(forward_demodulation,[],[f6906,f300])).

fof(f6906,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_630 ),
    inference(forward_demodulation,[],[f3618,f264])).

fof(f3618,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_630 ),
    inference(avatar_component_clause,[],[f3617])).

fof(f6905,plain,
    ( ~ spl5_1163
    | ~ spl5_36
    | ~ spl5_42
    | spl5_737 ),
    inference(avatar_split_clause,[],[f6898,f4151,f299,f263,f6903])).

fof(f4151,plain,
    ( spl5_737
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_737])])).

fof(f6898,plain,
    ( ~ r1_tarski(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_737 ),
    inference(forward_demodulation,[],[f6897,f300])).

fof(f6897,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_737 ),
    inference(forward_demodulation,[],[f4152,f264])).

fof(f4152,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)
    | ~ spl5_737 ),
    inference(avatar_component_clause,[],[f4151])).

fof(f6896,plain,
    ( ~ spl5_1161
    | ~ spl5_36
    | ~ spl5_42
    | spl5_741 ),
    inference(avatar_split_clause,[],[f6889,f4169,f299,f263,f6894])).

fof(f4169,plain,
    ( spl5_741
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_741])])).

fof(f6889,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_741 ),
    inference(forward_demodulation,[],[f6888,f300])).

fof(f6888,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_741 ),
    inference(forward_demodulation,[],[f4170,f264])).

fof(f4170,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_741 ),
    inference(avatar_component_clause,[],[f4169])).

fof(f6887,plain,
    ( spl5_1158
    | ~ spl5_36
    | ~ spl5_834 ),
    inference(avatar_split_clause,[],[f6880,f4617,f263,f6885])).

fof(f4617,plain,
    ( spl5_834
  <=> v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_834])])).

fof(f6880,plain,
    ( v1_xboole_0(k1_funct_2(sK3(o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_834 ),
    inference(forward_demodulation,[],[f4618,f264])).

fof(f4618,plain,
    ( v1_xboole_0(k1_funct_2(sK3(sK1),o_0_0_xboole_0))
    | ~ spl5_834 ),
    inference(avatar_component_clause,[],[f4617])).

fof(f6879,plain,
    ( spl5_1156
    | ~ spl5_36
    | ~ spl5_836 ),
    inference(avatar_split_clause,[],[f6872,f4627,f263,f6877])).

fof(f4627,plain,
    ( spl5_836
  <=> r2_hidden(sK3(sK3(sK1)),sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_836])])).

fof(f6872,plain,
    ( r2_hidden(sK3(sK3(o_0_0_xboole_0)),sK3(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_836 ),
    inference(forward_demodulation,[],[f4628,f264])).

fof(f4628,plain,
    ( r2_hidden(sK3(sK3(sK1)),sK3(sK1))
    | ~ spl5_836 ),
    inference(avatar_component_clause,[],[f4627])).

fof(f6871,plain,
    ( spl5_1154
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_862 ),
    inference(avatar_split_clause,[],[f6864,f4766,f299,f263,f6869])).

fof(f4766,plain,
    ( spl5_862
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_862])])).

fof(f6864,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_862 ),
    inference(forward_demodulation,[],[f6863,f300])).

fof(f6863,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_862 ),
    inference(forward_demodulation,[],[f4767,f264])).

fof(f4767,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_862 ),
    inference(avatar_component_clause,[],[f4766])).

fof(f6862,plain,
    ( spl5_1152
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_864 ),
    inference(avatar_split_clause,[],[f6855,f4776,f299,f263,f6860])).

fof(f4776,plain,
    ( spl5_864
  <=> r2_hidden(sK3(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_864])])).

fof(f6855,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_864 ),
    inference(forward_demodulation,[],[f6854,f300])).

fof(f6854,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_864 ),
    inference(forward_demodulation,[],[f4777,f264])).

fof(f4777,plain,
    ( r2_hidden(sK3(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_864 ),
    inference(avatar_component_clause,[],[f4776])).

fof(f6847,plain,
    ( ~ spl5_991
    | ~ spl5_1151
    | ~ spl5_993
    | ~ spl5_8
    | spl5_959 ),
    inference(avatar_split_clause,[],[f6334,f5505,f115,f5662,f6845,f5653])).

fof(f5653,plain,
    ( spl5_991
  <=> ~ v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_991])])).

fof(f6845,plain,
    ( spl5_1151
  <=> ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1151])])).

fof(f5662,plain,
    ( spl5_993
  <=> ~ v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_993])])).

fof(f5505,plain,
    ( spl5_959
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_959])])).

fof(f6334,plain,
    ( ~ v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_8
    | ~ spl5_959 ),
    inference(resolution,[],[f5506,f237])).

fof(f5506,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_959 ),
    inference(avatar_component_clause,[],[f5505])).

fof(f6840,plain,
    ( spl5_972
    | ~ spl5_54
    | ~ spl5_530
    | spl5_961 ),
    inference(avatar_split_clause,[],[f6029,f5516,f3100,f354,f5569])).

fof(f5569,plain,
    ( spl5_972
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_972])])).

fof(f6029,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_530
    | ~ spl5_961 ),
    inference(forward_demodulation,[],[f6026,f3101])).

fof(f6026,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_961 ),
    inference(unit_resulting_resolution,[],[f355,f5517,f64])).

fof(f6839,plain,
    ( spl5_972
    | ~ spl5_6
    | spl5_961 ),
    inference(avatar_split_clause,[],[f6025,f5516,f106,f5569])).

fof(f6025,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_961 ),
    inference(unit_resulting_resolution,[],[f107,f5517,f64])).

fof(f6838,plain,
    ( spl5_970
    | spl5_961 ),
    inference(avatar_split_clause,[],[f6024,f5516,f5560])).

fof(f5560,plain,
    ( spl5_970
  <=> r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_970])])).

fof(f6024,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_961 ),
    inference(unit_resulting_resolution,[],[f60,f5517,f63])).

fof(f6837,plain,
    ( spl5_956
    | spl5_951 ),
    inference(avatar_split_clause,[],[f6066,f5467,f5496])).

fof(f5496,plain,
    ( spl5_956
  <=> r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_956])])).

fof(f6066,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_951 ),
    inference(unit_resulting_resolution,[],[f5468,f66])).

fof(f5468,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_951 ),
    inference(avatar_component_clause,[],[f5467])).

fof(f6836,plain,
    ( spl5_1148
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_456 ),
    inference(avatar_split_clause,[],[f6829,f2728,f299,f263,f6834])).

fof(f6834,plain,
    ( spl5_1148
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),sK3(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1148])])).

fof(f2728,plain,
    ( spl5_456
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_456])])).

fof(f6829,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0),sK3(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_456 ),
    inference(forward_demodulation,[],[f6828,f264])).

fof(f6828,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0),sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_456 ),
    inference(forward_demodulation,[],[f2729,f300])).

fof(f2729,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),sK3(sK0)))
    | ~ spl5_456 ),
    inference(avatar_component_clause,[],[f2728])).

fof(f6827,plain,
    ( ~ spl5_1147
    | ~ spl5_36
    | ~ spl5_42
    | spl5_463 ),
    inference(avatar_split_clause,[],[f6820,f2746,f299,f263,f6825])).

fof(f6825,plain,
    ( spl5_1147
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK3(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1147])])).

fof(f2746,plain,
    ( spl5_463
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_463])])).

fof(f6820,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK3(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_463 ),
    inference(forward_demodulation,[],[f6819,f264])).

fof(f6819,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_463 ),
    inference(forward_demodulation,[],[f2747,f300])).

fof(f2747,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK3(sK0)))
    | ~ spl5_463 ),
    inference(avatar_component_clause,[],[f2746])).

fof(f6818,plain,
    ( ~ spl5_1145
    | ~ spl5_42
    | spl5_451 ),
    inference(avatar_split_clause,[],[f6811,f2704,f299,f6816])).

fof(f6816,plain,
    ( spl5_1145
  <=> ~ v1_xboole_0(k1_funct_2(sK2,sK3(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1145])])).

fof(f2704,plain,
    ( spl5_451
  <=> ~ v1_xboole_0(k1_funct_2(sK2,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_451])])).

fof(f6811,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_451 ),
    inference(forward_demodulation,[],[f2705,f300])).

fof(f2705,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,sK3(sK0)))
    | ~ spl5_451 ),
    inference(avatar_component_clause,[],[f2704])).

fof(f6810,plain,
    ( spl5_1142
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_444 ),
    inference(avatar_split_clause,[],[f6809,f2678,f299,f263,f6805])).

fof(f6805,plain,
    ( spl5_1142
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1142])])).

fof(f2678,plain,
    ( spl5_444
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_444])])).

fof(f6809,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_444 ),
    inference(forward_demodulation,[],[f6808,f264])).

fof(f6808,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_444 ),
    inference(forward_demodulation,[],[f2679,f300])).

fof(f2679,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3(sK0)))
    | ~ spl5_444 ),
    inference(avatar_component_clause,[],[f2678])).

fof(f6807,plain,
    ( spl5_1142
    | ~ spl5_42
    | ~ spl5_442 ),
    inference(avatar_split_clause,[],[f6800,f2671,f299,f6805])).

fof(f2671,plain,
    ( spl5_442
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_442])])).

fof(f6800,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_442 ),
    inference(forward_demodulation,[],[f2672,f300])).

fof(f2672,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK3(sK0)))
    | ~ spl5_442 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f6796,plain,
    ( spl5_1140
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_352 ),
    inference(avatar_split_clause,[],[f6789,f2177,f299,f263,f6794])).

fof(f6794,plain,
    ( spl5_1140
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1140])])).

fof(f2177,plain,
    ( spl5_352
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_352])])).

fof(f6789,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_352 ),
    inference(forward_demodulation,[],[f6788,f300])).

fof(f6788,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_352 ),
    inference(forward_demodulation,[],[f2178,f264])).

fof(f2178,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_352 ),
    inference(avatar_component_clause,[],[f2177])).

fof(f6787,plain,
    ( ~ spl5_1139
    | ~ spl5_36
    | ~ spl5_42
    | spl5_357 ),
    inference(avatar_split_clause,[],[f6780,f2188,f299,f263,f6785])).

fof(f6785,plain,
    ( spl5_1139
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1139])])).

fof(f2188,plain,
    ( spl5_357
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_357])])).

fof(f6780,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_357 ),
    inference(forward_demodulation,[],[f6779,f300])).

fof(f6779,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_357 ),
    inference(forward_demodulation,[],[f2189,f264])).

fof(f2189,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_357 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f6775,plain,
    ( ~ spl5_1137
    | ~ spl5_36
    | spl5_347 ),
    inference(avatar_split_clause,[],[f6768,f2153,f263,f6773])).

fof(f6773,plain,
    ( spl5_1137
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1137])])).

fof(f2153,plain,
    ( spl5_347
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_347])])).

fof(f6768,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_347 ),
    inference(forward_demodulation,[],[f2154,f264])).

fof(f2154,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_347 ),
    inference(avatar_component_clause,[],[f2153])).

fof(f6764,plain,
    ( spl5_1114
    | ~ spl5_36
    | ~ spl5_206 ),
    inference(avatar_split_clause,[],[f6763,f1277,f263,f6635])).

fof(f6635,plain,
    ( spl5_1114
  <=> r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1114])])).

fof(f1277,plain,
    ( spl5_206
  <=> r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f6763,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_206 ),
    inference(forward_demodulation,[],[f1278,f264])).

fof(f1278,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_206 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f6762,plain,
    ( spl5_1116
    | ~ spl5_36
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f6761,f1270,f263,f6642])).

fof(f1270,plain,
    ( spl5_204
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f6761,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f1271,f264])).

fof(f1271,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f6759,plain,
    ( spl5_1114
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6758,f299,f263,f128,f6635])).

fof(f128,plain,
    ( spl5_10
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f6758,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1250,f264])).

fof(f1250,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(superposition,[],[f129,f300])).

fof(f129,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f6757,plain,
    ( spl5_1116
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6756,f299,f263,f92,f6642])).

fof(f92,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f6756,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f1249,f264])).

fof(f1249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(superposition,[],[f93,f300])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f6755,plain,
    ( ~ spl5_1127
    | ~ spl5_36
    | ~ spl5_42
    | spl5_573 ),
    inference(avatar_split_clause,[],[f6754,f3301,f299,f263,f6688])).

fof(f6688,plain,
    ( spl5_1127
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1127])])).

fof(f3301,plain,
    ( spl5_573
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_573])])).

fof(f6754,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_573 ),
    inference(forward_demodulation,[],[f5345,f264])).

fof(f5345,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_573 ),
    inference(forward_demodulation,[],[f3302,f300])).

fof(f3302,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_573 ),
    inference(avatar_component_clause,[],[f3301])).

fof(f6753,plain,
    ( ~ spl5_1127
    | ~ spl5_36
    | ~ spl5_42
    | spl5_571 ),
    inference(avatar_split_clause,[],[f6752,f3294,f299,f263,f6688])).

fof(f3294,plain,
    ( spl5_571
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_571])])).

fof(f6752,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_571 ),
    inference(forward_demodulation,[],[f5348,f264])).

fof(f5348,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_571 ),
    inference(forward_demodulation,[],[f3295,f300])).

fof(f3295,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_571 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f6749,plain,
    ( spl5_1116
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6748,f299,f263,f92,f6642])).

fof(f6748,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5801,f264])).

fof(f5801,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(superposition,[],[f93,f300])).

fof(f6747,plain,
    ( spl5_1114
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6746,f299,f263,f128,f6635])).

fof(f6746,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5802,f264])).

fof(f5802,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(superposition,[],[f129,f300])).

fof(f6744,plain,
    ( spl5_1100
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f6743,f1065,f299,f263,f6541])).

fof(f6541,plain,
    ( spl5_1100
  <=> m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1100])])).

fof(f1065,plain,
    ( spl5_172
  <=> m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f6743,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f5841,f264])).

fof(f5841,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_42
    | ~ spl5_172 ),
    inference(superposition,[],[f1066,f300])).

fof(f1066,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_172 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f6738,plain,
    ( ~ spl5_1135
    | ~ spl5_36
    | ~ spl5_42
    | spl5_163 ),
    inference(avatar_split_clause,[],[f6731,f979,f299,f263,f6736])).

fof(f6736,plain,
    ( spl5_1135
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1135])])).

fof(f979,plain,
    ( spl5_163
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f6731,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_163 ),
    inference(forward_demodulation,[],[f6730,f300])).

fof(f6730,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK2))
    | ~ spl5_36
    | ~ spl5_163 ),
    inference(forward_demodulation,[],[f980,f264])).

fof(f980,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_163 ),
    inference(avatar_component_clause,[],[f979])).

fof(f6729,plain,
    ( spl5_1132
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_148 ),
    inference(avatar_split_clause,[],[f6722,f902,f299,f263,f6727])).

fof(f6727,plain,
    ( spl5_1132
  <=> r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1132])])).

fof(f902,plain,
    ( spl5_148
  <=> r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f6722,plain,
    ( r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_148 ),
    inference(forward_demodulation,[],[f6721,f300])).

fof(f6721,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_148 ),
    inference(forward_demodulation,[],[f903,f264])).

fof(f903,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_148 ),
    inference(avatar_component_clause,[],[f902])).

fof(f6720,plain,
    ( ~ spl5_1127
    | ~ spl5_36
    | ~ spl5_42
    | spl5_935 ),
    inference(avatar_split_clause,[],[f6719,f5175,f299,f263,f6688])).

fof(f5175,plain,
    ( spl5_935
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_935])])).

fof(f6719,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_935 ),
    inference(forward_demodulation,[],[f6718,f300])).

fof(f6718,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_935 ),
    inference(forward_demodulation,[],[f5176,f264])).

fof(f5176,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_935 ),
    inference(avatar_component_clause,[],[f5175])).

fof(f6717,plain,
    ( ~ spl5_1131
    | ~ spl5_36
    | ~ spl5_42
    | spl5_643 ),
    inference(avatar_split_clause,[],[f6716,f3656,f299,f263,f6709])).

fof(f6709,plain,
    ( spl5_1131
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1131])])).

fof(f3656,plain,
    ( spl5_643
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_643])])).

fof(f6716,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_643 ),
    inference(forward_demodulation,[],[f6715,f300])).

fof(f6715,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_643 ),
    inference(forward_demodulation,[],[f3657,f264])).

fof(f3657,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_643 ),
    inference(avatar_component_clause,[],[f3656])).

fof(f6714,plain,
    ( ~ spl5_1129
    | ~ spl5_36
    | ~ spl5_42
    | spl5_627 ),
    inference(avatar_split_clause,[],[f6713,f3600,f299,f263,f6700])).

fof(f6700,plain,
    ( spl5_1129
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1129])])).

fof(f3600,plain,
    ( spl5_627
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_627])])).

fof(f6713,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_627 ),
    inference(forward_demodulation,[],[f6712,f300])).

fof(f6712,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_627 ),
    inference(forward_demodulation,[],[f3601,f264])).

fof(f3601,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_627 ),
    inference(avatar_component_clause,[],[f3600])).

fof(f6711,plain,
    ( ~ spl5_1131
    | ~ spl5_36
    | ~ spl5_42
    | spl5_611 ),
    inference(avatar_split_clause,[],[f6704,f3490,f299,f263,f6709])).

fof(f3490,plain,
    ( spl5_611
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_611])])).

fof(f6704,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_611 ),
    inference(forward_demodulation,[],[f6703,f300])).

fof(f6703,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_611 ),
    inference(forward_demodulation,[],[f3491,f264])).

fof(f3491,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_611 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f6702,plain,
    ( ~ spl5_1129
    | ~ spl5_36
    | ~ spl5_42
    | spl5_597 ),
    inference(avatar_split_clause,[],[f6695,f3441,f299,f263,f6700])).

fof(f3441,plain,
    ( spl5_597
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_597])])).

fof(f6695,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_597 ),
    inference(forward_demodulation,[],[f6694,f300])).

fof(f6694,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_597 ),
    inference(forward_demodulation,[],[f3442,f264])).

fof(f3442,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_597 ),
    inference(avatar_component_clause,[],[f3441])).

fof(f6693,plain,
    ( ~ spl5_1127
    | ~ spl5_36
    | ~ spl5_42
    | spl5_415 ),
    inference(avatar_split_clause,[],[f6692,f2509,f299,f263,f6688])).

fof(f2509,plain,
    ( spl5_415
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_415])])).

fof(f6692,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_415 ),
    inference(forward_demodulation,[],[f6691,f300])).

fof(f6691,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_415 ),
    inference(forward_demodulation,[],[f2510,f264])).

fof(f2510,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_415 ),
    inference(avatar_component_clause,[],[f2509])).

fof(f6690,plain,
    ( ~ spl5_1127
    | ~ spl5_36
    | ~ spl5_42
    | spl5_413 ),
    inference(avatar_split_clause,[],[f6683,f2502,f299,f263,f6688])).

fof(f2502,plain,
    ( spl5_413
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_413])])).

fof(f6683,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_413 ),
    inference(forward_demodulation,[],[f6682,f300])).

fof(f6682,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_413 ),
    inference(forward_demodulation,[],[f2503,f264])).

fof(f2503,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_413 ),
    inference(avatar_component_clause,[],[f2502])).

fof(f6679,plain,
    ( spl5_1122
    | spl5_1124
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6669,f299,f263,f92,f6677,f6671])).

fof(f6671,plain,
    ( spl5_1122
  <=> ! [X3] :
        ( r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1122])])).

fof(f6677,plain,
    ( spl5_1124
  <=> v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1124])])).

fof(f6669,plain,
    ( ! [X3] :
        ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK2) )
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f6668,f264])).

fof(f6668,plain,
    ( ! [X3] :
        ( r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK2)
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1)) )
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f6667,f264])).

fof(f6667,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)),sK2)
        | r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1)) )
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f774,f264])).

fof(f774,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1)),sK2)
        | r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1)) )
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f773,f300])).

fof(f773,plain,
    ( ! [X3] :
        ( r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1))
        | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(sK0,sK1)),sK2) )
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f772,f300])).

fof(f772,plain,
    ( ! [X3] :
        ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1))
        | r1_tarski(X3,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(sK0,sK1)),sK2) )
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f770,f300])).

fof(f770,plain,
    ( ! [X3] :
        ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X3,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(sK0,sK1)),sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f158,f201])).

fof(f201,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f78,f93])).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(sK4(X1,X2),X2)
      | v1_xboole_0(X2)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f67,f63])).

fof(f6662,plain,
    ( spl5_1120
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_932 ),
    inference(avatar_split_clause,[],[f6655,f5130,f299,f263,f6660])).

fof(f6660,plain,
    ( spl5_1120
  <=> r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1120])])).

fof(f5130,plain,
    ( spl5_932
  <=> r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_932])])).

fof(f6655,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_932 ),
    inference(forward_demodulation,[],[f5291,f300])).

fof(f5291,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_932 ),
    inference(forward_demodulation,[],[f5131,f264])).

fof(f5131,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_932 ),
    inference(avatar_component_clause,[],[f5130])).

fof(f6654,plain,
    ( spl5_1058
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_930 ),
    inference(avatar_split_clause,[],[f6653,f5121,f299,f263,f6377])).

fof(f6377,plain,
    ( spl5_1058
  <=> v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1058])])).

fof(f5121,plain,
    ( spl5_930
  <=> v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_930])])).

fof(f6653,plain,
    ( v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_930 ),
    inference(forward_demodulation,[],[f5301,f300])).

fof(f5301,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_930 ),
    inference(forward_demodulation,[],[f5122,f264])).

fof(f5122,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0,sK1)
    | ~ spl5_930 ),
    inference(avatar_component_clause,[],[f5121])).

fof(f6652,plain,
    ( ~ spl5_273
    | ~ spl5_42
    | spl5_187 ),
    inference(avatar_split_clause,[],[f5410,f1186,f299,f1701])).

fof(f1701,plain,
    ( spl5_273
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_273])])).

fof(f1186,plain,
    ( spl5_187
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f5410,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_187 ),
    inference(forward_demodulation,[],[f1187,f300])).

fof(f1187,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_187 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f6651,plain,
    ( ~ spl5_1119
    | spl5_1
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5461,f299,f263,f85,f6649])).

fof(f85,plain,
    ( spl5_1
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f5461,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5412,f300])).

fof(f5412,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_1
    | ~ spl5_36 ),
    inference(superposition,[],[f86,f264])).

fof(f86,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f6644,plain,
    ( spl5_1116
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5470,f299,f263,f92,f6642])).

fof(f5470,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5413,f300])).

fof(f5413,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(superposition,[],[f93,f264])).

fof(f6637,plain,
    ( spl5_1114
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5479,f299,f263,f128,f6635])).

fof(f5479,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5414,f300])).

fof(f5414,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_10
    | ~ spl5_36 ),
    inference(superposition,[],[f129,f264])).

fof(f6630,plain,
    ( ~ spl5_1113
    | spl5_13
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5481,f299,f263,f135,f6628])).

fof(f6628,plain,
    ( spl5_1113
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1113])])).

fof(f135,plain,
    ( spl5_13
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f5481,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_13
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5415,f300])).

fof(f5415,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_13
    | ~ spl5_36 ),
    inference(superposition,[],[f136,f264])).

fof(f136,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f6623,plain,
    ( spl5_1110
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6616,f299,f263,f153,f6621])).

fof(f6621,plain,
    ( spl5_1110
  <=> r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1110])])).

fof(f6616,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5416,f300])).

fof(f5416,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k5_partfun1(sK0,o_0_0_xboole_0,sK2))
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(superposition,[],[f154,f264])).

fof(f6615,plain,
    ( ~ spl5_1109
    | spl5_17
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5499,f299,f263,f164,f6613])).

fof(f164,plain,
    ( spl5_17
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f5499,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_17
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5417,f300])).

fof(f5417,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_17
    | ~ spl5_36 ),
    inference(superposition,[],[f165,f264])).

fof(f165,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f6608,plain,
    ( ~ spl5_1107
    | spl5_31
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f6601,f299,f263,f223,f6606])).

fof(f6601,plain,
    ( ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5419,f300])).

fof(f5419,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,o_0_0_xboole_0,sK2))
    | ~ spl5_31
    | ~ spl5_36 ),
    inference(superposition,[],[f224,f264])).

fof(f6600,plain,
    ( ~ spl5_1099
    | spl5_33
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5519,f299,f263,f251,f6534])).

fof(f6534,plain,
    ( spl5_1099
  <=> ~ v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1099])])).

fof(f251,plain,
    ( spl5_33
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f5519,plain,
    ( ~ v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_33
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5420,f300])).

fof(f5420,plain,
    ( ~ v1_funct_2(sK2,sK0,o_0_0_xboole_0)
    | ~ spl5_33
    | ~ spl5_36 ),
    inference(superposition,[],[f252,f264])).

fof(f252,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f251])).

fof(f6599,plain,
    ( ~ spl5_1097
    | spl5_35
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f5528,f299,f263,f254,f6527])).

fof(f6527,plain,
    ( spl5_1097
  <=> ~ r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1097])])).

fof(f254,plain,
    ( spl5_35
  <=> ~ r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f5528,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_35
    | ~ spl5_36
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f5421,f300])).

fof(f5421,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(superposition,[],[f255,f264])).

fof(f255,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f254])).

fof(f6598,plain,
    ( ~ spl5_1095
    | ~ spl5_36
    | ~ spl5_42
    | spl5_51 ),
    inference(avatar_split_clause,[],[f6597,f337,f299,f263,f6520])).

fof(f6520,plain,
    ( spl5_1095
  <=> ~ r2_hidden(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1095])])).

fof(f337,plain,
    ( spl5_51
  <=> ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f6597,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f5423,f300])).

fof(f5423,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_51 ),
    inference(superposition,[],[f338,f264])).

fof(f338,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f337])).

fof(f6596,plain,
    ( spl5_1092
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f6595,f347,f299,f263,f6512])).

fof(f6512,plain,
    ( spl5_1092
  <=> r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1092])])).

fof(f6595,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f5424,f300])).

fof(f5424,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k5_partfun1(sK0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_52 ),
    inference(superposition,[],[f348,f264])).

fof(f6594,plain,
    ( spl5_1090
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f6593,f354,f299,f263,f6504])).

fof(f6504,plain,
    ( spl5_1090
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1090])])).

fof(f6593,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f5425,f300])).

fof(f5425,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54 ),
    inference(superposition,[],[f355,f264])).

fof(f6592,plain,
    ( ~ spl5_1089
    | ~ spl5_36
    | ~ spl5_42
    | spl5_57 ),
    inference(avatar_split_clause,[],[f6591,f368,f299,f263,f6496])).

fof(f6496,plain,
    ( spl5_1089
  <=> k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1089])])).

fof(f368,plain,
    ( spl5_57
  <=> k5_partfun1(sK0,sK1,sK2) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f6591,plain,
    ( k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) != o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f5426,f300])).

fof(f5426,plain,
    ( k5_partfun1(sK0,o_0_0_xboole_0,sK2) != o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_57 ),
    inference(superposition,[],[f369,f264])).

fof(f369,plain,
    ( k5_partfun1(sK0,sK1,sK2) != o_0_0_xboole_0
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f368])).

fof(f6590,plain,
    ( ~ spl5_1087
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59 ),
    inference(avatar_split_clause,[],[f6589,f376,f299,f263,f6486])).

fof(f6486,plain,
    ( spl5_1087
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1087])])).

fof(f6589,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f5427,f300])).

fof(f5427,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_59 ),
    inference(superposition,[],[f377,f264])).

fof(f6588,plain,
    ( ~ spl5_1087
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61 ),
    inference(avatar_split_clause,[],[f6587,f383,f299,f263,f6486])).

fof(f6587,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f5428,f300])).

fof(f5428,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_61 ),
    inference(superposition,[],[f384,f264])).

fof(f6586,plain,
    ( ~ spl5_1085
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63 ),
    inference(avatar_split_clause,[],[f6585,f390,f299,f263,f6478])).

fof(f6478,plain,
    ( spl5_1085
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1085])])).

fof(f6585,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f5429,f300])).

fof(f5429,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k5_partfun1(sK0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_63 ),
    inference(superposition,[],[f391,f264])).

fof(f6584,plain,
    ( ~ spl5_1105
    | ~ spl5_36
    | ~ spl5_42
    | spl5_65 ),
    inference(avatar_split_clause,[],[f5604,f407,f299,f263,f6582])).

fof(f6582,plain,
    ( spl5_1105
  <=> ~ m1_subset_1(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1105])])).

fof(f407,plain,
    ( spl5_65
  <=> ~ m1_subset_1(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f5604,plain,
    ( ~ m1_subset_1(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f5431,f300])).

fof(f5431,plain,
    ( ~ m1_subset_1(sK2,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_65 ),
    inference(superposition,[],[f408,f264])).

fof(f408,plain,
    ( ~ m1_subset_1(sK2,k1_funct_2(sK0,sK1))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f407])).

fof(f6577,plain,
    ( ~ spl5_1083
    | ~ spl5_36
    | ~ spl5_42
    | spl5_69 ),
    inference(avatar_split_clause,[],[f5614,f426,f299,f263,f6470])).

fof(f6470,plain,
    ( spl5_1083
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1083])])).

fof(f426,plain,
    ( spl5_69
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f5614,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f5433,f300])).

fof(f5433,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_69 ),
    inference(superposition,[],[f427,f264])).

fof(f427,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f426])).

fof(f6576,plain,
    ( ~ spl5_1081
    | ~ spl5_36
    | ~ spl5_42
    | spl5_71 ),
    inference(avatar_split_clause,[],[f5623,f433,f299,f263,f6463])).

fof(f6463,plain,
    ( spl5_1081
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1081])])).

fof(f433,plain,
    ( spl5_71
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f5623,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_71 ),
    inference(forward_demodulation,[],[f5434,f300])).

fof(f5434,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0)))))
    | ~ spl5_36
    | ~ spl5_71 ),
    inference(superposition,[],[f434,f264])).

fof(f434,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f433])).

fof(f6575,plain,
    ( ~ spl5_1079
    | ~ spl5_36
    | ~ spl5_42
    | spl5_73 ),
    inference(avatar_split_clause,[],[f5632,f442,f299,f263,f6456])).

fof(f6456,plain,
    ( spl5_1079
  <=> ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1079])])).

fof(f442,plain,
    ( spl5_73
  <=> ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f5632,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f5435,f300])).

fof(f5435,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_73 ),
    inference(superposition,[],[f443,f264])).

fof(f443,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f442])).

fof(f6574,plain,
    ( ~ spl5_1077
    | ~ spl5_36
    | ~ spl5_42
    | spl5_75 ),
    inference(avatar_split_clause,[],[f6573,f464,f299,f263,f6449])).

fof(f6449,plain,
    ( spl5_1077
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1077])])).

fof(f464,plain,
    ( spl5_75
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f6573,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f5436,f300])).

fof(f5436,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_75 ),
    inference(superposition,[],[f465,f264])).

fof(f465,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f464])).

fof(f6572,plain,
    ( spl5_1074
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f5650,f486,f299,f263,f6441])).

fof(f6441,plain,
    ( spl5_1074
  <=> v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1074])])).

fof(f486,plain,
    ( spl5_80
  <=> v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f5650,plain,
    ( v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f5437,f300])).

fof(f5437,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_80 ),
    inference(superposition,[],[f487,f264])).

fof(f487,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f486])).

fof(f6571,plain,
    ( spl5_1072
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f5659,f493,f299,f263,f6434])).

fof(f6434,plain,
    ( spl5_1072
  <=> v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1072])])).

fof(f493,plain,
    ( spl5_82
  <=> v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f5659,plain,
    ( v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82 ),
    inference(forward_demodulation,[],[f5438,f300])).

fof(f5438,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),sK0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_82 ),
    inference(superposition,[],[f494,f264])).

fof(f494,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f493])).

fof(f6570,plain,
    ( ~ spl5_1071
    | ~ spl5_36
    | ~ spl5_42
    | spl5_87 ),
    inference(avatar_split_clause,[],[f6569,f523,f299,f263,f6427])).

fof(f6427,plain,
    ( spl5_1071
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1071])])).

fof(f523,plain,
    ( spl5_87
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f6569,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_87 ),
    inference(forward_demodulation,[],[f5439,f300])).

fof(f5439,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_87 ),
    inference(superposition,[],[f524,f264])).

fof(f524,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f523])).

fof(f6568,plain,
    ( ~ spl5_1103
    | ~ spl5_36
    | ~ spl5_42
    | spl5_91 ),
    inference(avatar_split_clause,[],[f5677,f546,f299,f263,f6566])).

fof(f6566,plain,
    ( spl5_1103
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1103])])).

fof(f546,plain,
    ( spl5_91
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f5677,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_91 ),
    inference(forward_demodulation,[],[f5440,f300])).

fof(f5440,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_91 ),
    inference(superposition,[],[f547,f264])).

fof(f547,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f546])).

fof(f6561,plain,
    ( ~ spl5_1069
    | ~ spl5_36
    | ~ spl5_42
    | spl5_103 ),
    inference(avatar_split_clause,[],[f6560,f612,f299,f263,f6419])).

fof(f6419,plain,
    ( spl5_1069
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1069])])).

fof(f612,plain,
    ( spl5_103
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f6560,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_103 ),
    inference(forward_demodulation,[],[f5441,f300])).

fof(f5441,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_103 ),
    inference(superposition,[],[f613,f264])).

fof(f613,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_103 ),
    inference(avatar_component_clause,[],[f612])).

fof(f6559,plain,
    ( ~ spl5_1067
    | ~ spl5_36
    | ~ spl5_42
    | spl5_109 ),
    inference(avatar_split_clause,[],[f6558,f643,f299,f263,f6411])).

fof(f6411,plain,
    ( spl5_1067
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1067])])).

fof(f643,plain,
    ( spl5_109
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f6558,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_109 ),
    inference(forward_demodulation,[],[f5443,f300])).

fof(f5443,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_109 ),
    inference(superposition,[],[f644,f264])).

fof(f644,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f643])).

fof(f6556,plain,
    ( ~ spl5_1065
    | ~ spl5_36
    | ~ spl5_42
    | spl5_139 ),
    inference(avatar_split_clause,[],[f6555,f826,f299,f263,f6402])).

fof(f6402,plain,
    ( spl5_1065
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1065])])).

fof(f826,plain,
    ( spl5_139
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f6555,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK2)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(forward_demodulation,[],[f5447,f300])).

fof(f5447,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),sK2)
    | ~ spl5_36
    | ~ spl5_139 ),
    inference(superposition,[],[f827,f264])).

fof(f827,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK2)
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f826])).

fof(f6554,plain,
    ( spl5_1062
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f6553,f917,f299,f263,f6394])).

fof(f6394,plain,
    ( spl5_1062
  <=> v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1062])])).

fof(f917,plain,
    ( spl5_150
  <=> v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f6553,plain,
    ( v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150 ),
    inference(forward_demodulation,[],[f5448,f300])).

fof(f5448,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_150 ),
    inference(superposition,[],[f918,f264])).

fof(f918,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_150 ),
    inference(avatar_component_clause,[],[f917])).

fof(f6551,plain,
    ( ~ spl5_1061
    | ~ spl5_36
    | ~ spl5_42
    | spl5_165 ),
    inference(avatar_split_clause,[],[f6550,f1008,f299,f263,f6385])).

fof(f6385,plain,
    ( spl5_1061
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1061])])).

fof(f1008,plain,
    ( spl5_165
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f6550,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_165 ),
    inference(forward_demodulation,[],[f5450,f300])).

fof(f5450,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2))))
    | ~ spl5_36
    | ~ spl5_165 ),
    inference(superposition,[],[f1009,f264])).

fof(f1009,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f1008])).

fof(f6549,plain,
    ( spl5_1058
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f5746,f1028,f299,f263,f6377])).

fof(f1028,plain,
    ( spl5_166
  <=> v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f5746,plain,
    ( v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_166 ),
    inference(forward_demodulation,[],[f5451,f300])).

fof(f5451,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)),sK0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_166 ),
    inference(superposition,[],[f1029,f264])).

fof(f1029,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1)
    | ~ spl5_166 ),
    inference(avatar_component_clause,[],[f1028])).

fof(f6548,plain,
    ( ~ spl5_1057
    | ~ spl5_36
    | ~ spl5_42
    | spl5_169 ),
    inference(avatar_split_clause,[],[f6547,f1035,f299,f263,f6370])).

fof(f6370,plain,
    ( spl5_1057
  <=> ~ m1_subset_1(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1057])])).

fof(f1035,plain,
    ( spl5_169
  <=> ~ m1_subset_1(sK2,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f6547,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_169 ),
    inference(forward_demodulation,[],[f5452,f300])).

fof(f5452,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(sK0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_169 ),
    inference(superposition,[],[f1036,f264])).

fof(f1036,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f6543,plain,
    ( spl5_1100
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f5761,f1065,f299,f263,f6541])).

fof(f5761,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f5454,f300])).

fof(f5454,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_172 ),
    inference(superposition,[],[f1066,f264])).

fof(f6536,plain,
    ( ~ spl5_1099
    | ~ spl5_36
    | spl5_197 ),
    inference(avatar_split_clause,[],[f5455,f1226,f263,f6534])).

fof(f1226,plain,
    ( spl5_197
  <=> ~ v1_funct_2(sK2,o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f5455,plain,
    ( ~ v1_funct_2(sK2,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_197 ),
    inference(superposition,[],[f1227,f264])).

fof(f1227,plain,
    ( ~ v1_funct_2(sK2,o_0_0_xboole_0,sK1)
    | ~ spl5_197 ),
    inference(avatar_component_clause,[],[f1226])).

fof(f6529,plain,
    ( ~ spl5_1097
    | ~ spl5_36
    | spl5_199 ),
    inference(avatar_split_clause,[],[f5456,f1229,f263,f6527])).

fof(f1229,plain,
    ( spl5_199
  <=> ~ r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f5456,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_199 ),
    inference(superposition,[],[f1230,f264])).

fof(f1230,plain,
    ( ~ r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_199 ),
    inference(avatar_component_clause,[],[f1229])).

fof(f6522,plain,
    ( ~ spl5_1095
    | ~ spl5_36
    | ~ spl5_42
    | spl5_51 ),
    inference(avatar_split_clause,[],[f6515,f337,f299,f263,f6520])).

fof(f6515,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_51 ),
    inference(forward_demodulation,[],[f5811,f264])).

fof(f5811,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_42
    | ~ spl5_51 ),
    inference(superposition,[],[f338,f300])).

fof(f6514,plain,
    ( spl5_1092
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f6507,f347,f299,f263,f6512])).

fof(f6507,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52 ),
    inference(forward_demodulation,[],[f5812,f264])).

fof(f5812,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)),k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_42
    | ~ spl5_52 ),
    inference(superposition,[],[f348,f300])).

fof(f6506,plain,
    ( spl5_1090
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f6499,f354,f299,f263,f6504])).

fof(f6499,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f5813,f264])).

fof(f5813,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_54 ),
    inference(superposition,[],[f355,f300])).

fof(f6498,plain,
    ( ~ spl5_1089
    | ~ spl5_36
    | ~ spl5_42
    | spl5_57 ),
    inference(avatar_split_clause,[],[f6491,f368,f299,f263,f6496])).

fof(f6491,plain,
    ( k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2) != o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_57 ),
    inference(forward_demodulation,[],[f5814,f264])).

fof(f5814,plain,
    ( k5_partfun1(o_0_0_xboole_0,sK1,sK2) != o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_57 ),
    inference(superposition,[],[f369,f300])).

fof(f6490,plain,
    ( ~ spl5_1087
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59 ),
    inference(avatar_split_clause,[],[f6489,f376,f299,f263,f6486])).

fof(f6489,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59 ),
    inference(forward_demodulation,[],[f5815,f264])).

fof(f5815,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k5_partfun1(o_0_0_xboole_0,sK1,sK2)))
    | ~ spl5_42
    | ~ spl5_59 ),
    inference(superposition,[],[f377,f300])).

fof(f6488,plain,
    ( ~ spl5_1087
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61 ),
    inference(avatar_split_clause,[],[f6481,f383,f299,f263,f6486])).

fof(f6481,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61 ),
    inference(forward_demodulation,[],[f5816,f264])).

fof(f5816,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,sK1,sK2)))
    | ~ spl5_42
    | ~ spl5_61 ),
    inference(superposition,[],[f384,f300])).

fof(f6480,plain,
    ( ~ spl5_1085
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63 ),
    inference(avatar_split_clause,[],[f6473,f390,f299,f263,f6478])).

fof(f6473,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63 ),
    inference(forward_demodulation,[],[f5817,f264])).

fof(f5817,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k5_partfun1(o_0_0_xboole_0,sK1,sK2)))
    | ~ spl5_42
    | ~ spl5_63 ),
    inference(superposition,[],[f391,f300])).

fof(f6472,plain,
    ( ~ spl5_1083
    | ~ spl5_36
    | ~ spl5_42
    | spl5_69 ),
    inference(avatar_split_clause,[],[f5865,f426,f299,f263,f6470])).

fof(f5865,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_69 ),
    inference(forward_demodulation,[],[f5821,f264])).

fof(f5821,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1)))
    | ~ spl5_42
    | ~ spl5_69 ),
    inference(superposition,[],[f427,f300])).

fof(f6465,plain,
    ( ~ spl5_1081
    | ~ spl5_36
    | ~ spl5_42
    | spl5_71 ),
    inference(avatar_split_clause,[],[f5867,f433,f299,f263,f6463])).

fof(f5867,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_71 ),
    inference(forward_demodulation,[],[f5822,f264])).

fof(f5822,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1)))))
    | ~ spl5_42
    | ~ spl5_71 ),
    inference(superposition,[],[f434,f300])).

fof(f6458,plain,
    ( ~ spl5_1079
    | ~ spl5_36
    | ~ spl5_42
    | spl5_73 ),
    inference(avatar_split_clause,[],[f5869,f442,f299,f263,f6456])).

fof(f5869,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f5823,f264])).

fof(f5823,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_42
    | ~ spl5_73 ),
    inference(superposition,[],[f443,f300])).

fof(f6451,plain,
    ( ~ spl5_1077
    | ~ spl5_36
    | ~ spl5_42
    | spl5_75 ),
    inference(avatar_split_clause,[],[f6444,f464,f299,f263,f6449])).

fof(f6444,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f5824,f264])).

fof(f5824,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_75 ),
    inference(superposition,[],[f465,f300])).

fof(f6443,plain,
    ( spl5_1074
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(avatar_split_clause,[],[f5873,f486,f299,f263,f6441])).

fof(f5873,plain,
    ( v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f5825,f264])).

fof(f5825,plain,
    ( v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)))
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(superposition,[],[f487,f300])).

fof(f6436,plain,
    ( spl5_1072
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f5875,f493,f299,f263,f6434])).

fof(f5875,plain,
    ( v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82 ),
    inference(forward_demodulation,[],[f5826,f264])).

fof(f5826,plain,
    ( v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),o_0_0_xboole_0,sK1)
    | ~ spl5_42
    | ~ spl5_82 ),
    inference(superposition,[],[f494,f300])).

fof(f6429,plain,
    ( ~ spl5_1071
    | ~ spl5_36
    | ~ spl5_42
    | spl5_87 ),
    inference(avatar_split_clause,[],[f6422,f523,f299,f263,f6427])).

fof(f6422,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_87 ),
    inference(forward_demodulation,[],[f5827,f264])).

fof(f5827,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_42
    | ~ spl5_87 ),
    inference(superposition,[],[f524,f300])).

fof(f6421,plain,
    ( ~ spl5_1069
    | ~ spl5_36
    | ~ spl5_42
    | spl5_103 ),
    inference(avatar_split_clause,[],[f6414,f612,f299,f263,f6419])).

fof(f6414,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_103 ),
    inference(forward_demodulation,[],[f5829,f264])).

fof(f5829,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_103 ),
    inference(superposition,[],[f613,f300])).

fof(f6413,plain,
    ( ~ spl5_1067
    | ~ spl5_36
    | ~ spl5_42
    | spl5_109 ),
    inference(avatar_split_clause,[],[f6406,f643,f299,f263,f6411])).

fof(f6406,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_109 ),
    inference(forward_demodulation,[],[f5830,f264])).

fof(f5830,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)))
    | ~ spl5_42
    | ~ spl5_109 ),
    inference(superposition,[],[f644,f300])).

fof(f6404,plain,
    ( ~ spl5_1065
    | ~ spl5_36
    | ~ spl5_42
    | spl5_139 ),
    inference(avatar_split_clause,[],[f6397,f826,f299,f263,f6402])).

fof(f6397,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),sK2)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(forward_demodulation,[],[f5834,f264])).

fof(f5834,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK2)
    | ~ spl5_42
    | ~ spl5_139 ),
    inference(superposition,[],[f827,f300])).

fof(f6396,plain,
    ( spl5_1062
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f6389,f917,f299,f263,f6394])).

fof(f6389,plain,
    ( v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150 ),
    inference(forward_demodulation,[],[f5835,f264])).

fof(f5835,plain,
    ( v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)))
    | ~ spl5_42
    | ~ spl5_150 ),
    inference(superposition,[],[f918,f300])).

fof(f6387,plain,
    ( ~ spl5_1061
    | ~ spl5_36
    | ~ spl5_42
    | spl5_165 ),
    inference(avatar_split_clause,[],[f6380,f1008,f299,f263,f6385])).

fof(f6380,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_165 ),
    inference(forward_demodulation,[],[f5837,f264])).

fof(f5837,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,sK1,sK2))))
    | ~ spl5_42
    | ~ spl5_165 ),
    inference(superposition,[],[f1009,f300])).

fof(f6379,plain,
    ( spl5_1058
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_166 ),
    inference(avatar_split_clause,[],[f5895,f1028,f299,f263,f6377])).

fof(f5895,plain,
    ( v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_166 ),
    inference(forward_demodulation,[],[f5838,f264])).

fof(f5838,plain,
    ( v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)),o_0_0_xboole_0,sK1)
    | ~ spl5_42
    | ~ spl5_166 ),
    inference(superposition,[],[f1029,f300])).

fof(f6372,plain,
    ( ~ spl5_1057
    | ~ spl5_36
    | ~ spl5_42
    | spl5_169 ),
    inference(avatar_split_clause,[],[f6365,f1035,f299,f263,f6370])).

fof(f6365,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_169 ),
    inference(forward_demodulation,[],[f5839,f264])).

fof(f5839,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_42
    | ~ spl5_169 ),
    inference(superposition,[],[f1036,f300])).

fof(f6361,plain,
    ( ~ spl5_1055
    | spl5_961 ),
    inference(avatar_split_clause,[],[f6027,f5516,f6359])).

fof(f6359,plain,
    ( spl5_1055
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1055])])).

fof(f6027,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_961 ),
    inference(unit_resulting_resolution,[],[f60,f5517,f143])).

fof(f6354,plain,
    ( ~ spl5_1053
    | ~ spl5_36
    | ~ spl5_42
    | spl5_847 ),
    inference(avatar_split_clause,[],[f6308,f4681,f299,f263,f6352])).

fof(f6352,plain,
    ( spl5_1053
  <=> ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1053])])).

fof(f4681,plain,
    ( spl5_847
  <=> ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_847])])).

fof(f6308,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_847 ),
    inference(forward_demodulation,[],[f6307,f300])).

fof(f6307,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_847 ),
    inference(forward_demodulation,[],[f4682,f264])).

fof(f4682,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_847 ),
    inference(avatar_component_clause,[],[f4681])).

fof(f6347,plain,
    ( spl5_1050
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f6318,f657,f299,f263,f6345])).

fof(f657,plain,
    ( spl5_112
  <=> v1_xboole_0(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f6318,plain,
    ( v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f6317,f300])).

fof(f6317,plain,
    ( v1_xboole_0(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f658,f264])).

fof(f658,plain,
    ( v1_xboole_0(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f657])).

fof(f6339,plain,
    ( ~ spl5_991
    | ~ spl5_993
    | ~ spl5_943
    | ~ spl5_8
    | spl5_959
    | ~ spl5_1022 ),
    inference(avatar_split_clause,[],[f6338,f5971,f5505,f115,f5281,f5662,f5653])).

fof(f5971,plain,
    ( spl5_1022
  <=> k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1022])])).

fof(f6338,plain,
    ( ~ r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_8
    | ~ spl5_959
    | ~ spl5_1022 ),
    inference(forward_demodulation,[],[f6334,f5972])).

fof(f5972,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_1022 ),
    inference(avatar_component_clause,[],[f5971])).

fof(f6316,plain,
    ( ~ spl5_1049
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | spl5_847 ),
    inference(avatar_split_clause,[],[f6309,f4681,f960,f299,f263,f6314])).

fof(f6314,plain,
    ( spl5_1049
  <=> ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1049])])).

fof(f960,plain,
    ( spl5_156
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f6309,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_847 ),
    inference(forward_demodulation,[],[f6308,f961])).

fof(f961,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_156 ),
    inference(avatar_component_clause,[],[f960])).

fof(f6298,plain,
    ( spl5_1038
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6297,f1411,f1388,f299,f263,f115,f6201])).

fof(f6201,plain,
    ( spl5_1038
  <=> k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1038])])).

fof(f1388,plain,
    ( spl5_220
  <=> k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_220])])).

fof(f6297,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6296,f300])).

fof(f6296,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6295,f264])).

fof(f6295,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6294,f1389])).

fof(f1389,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_220 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f6293,plain,
    ( spl5_1046
    | spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6292,f1411,f1388,f960,f299,f263,f223,f6286])).

fof(f6286,plain,
    ( spl5_1046
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1046])])).

fof(f6292,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6291,f961])).

fof(f6291,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6290,f300])).

fof(f6290,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6289,f264])).

fof(f6289,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6106,f1389])).

fof(f6288,plain,
    ( spl5_1046
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226
    | spl5_961 ),
    inference(avatar_split_clause,[],[f6281,f5516,f1411,f1388,f299,f263,f6286])).

fof(f6281,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_961 ),
    inference(forward_demodulation,[],[f6280,f300])).

fof(f6280,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_961 ),
    inference(forward_demodulation,[],[f6279,f264])).

fof(f6279,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_961 ),
    inference(forward_demodulation,[],[f6107,f1389])).

fof(f6107,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_226
    | ~ spl5_961 ),
    inference(unit_resulting_resolution,[],[f5517,f1412,f64])).

fof(f6278,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | spl5_45
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6277,f1411,f1388,f304,f299,f263,f6235])).

fof(f6235,plain,
    ( spl5_1042
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1042])])).

fof(f304,plain,
    ( spl5_45
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f6277,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_45
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6276,f300])).

fof(f6276,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,sK0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_45
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6275,f264])).

fof(f6275,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,sK0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_45
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6108,f1389])).

fof(f6108,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_45
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f305,f1412,f64])).

fof(f305,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f304])).

fof(f6274,plain,
    ( spl5_1044
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6273,f1411,f1388,f960,f390,f299,f263,f6246])).

fof(f6246,plain,
    ( spl5_1044
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1044])])).

fof(f6273,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6272,f961])).

fof(f6272,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6271,f300])).

fof(f6271,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_63
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6270,f264])).

fof(f6270,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_63
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6109,f1389])).

fof(f6269,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | spl5_201
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6268,f1411,f1388,f1240,f299,f263,f6235])).

fof(f6268,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_201
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6267,f300])).

fof(f6267,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_201
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6266,f264])).

fof(f6266,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_201
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6110,f1389])).

fof(f6265,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | spl5_67
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6264,f1411,f1388,f410,f299,f263,f6235])).

fof(f6264,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_67
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6263,f300])).

fof(f6263,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_67
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6262,f264])).

fof(f6262,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_67
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6111,f1389])).

fof(f6261,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | spl5_225
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6260,f1411,f1400,f1388,f299,f263,f6235])).

fof(f6260,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6259,f300])).

fof(f6259,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6258,f264])).

fof(f6258,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_225
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6112,f1389])).

fof(f6257,plain,
    ( spl5_1044
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6256,f1411,f1388,f960,f383,f299,f263,f6246])).

fof(f6256,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6255,f961])).

fof(f6255,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6254,f300])).

fof(f6254,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_61
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6253,f264])).

fof(f6253,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_61
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6113,f1389])).

fof(f6252,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | spl5_223
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6251,f1411,f1393,f1388,f299,f263,f6235])).

fof(f6251,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6250,f300])).

fof(f6250,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6249,f264])).

fof(f6249,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_223
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6114,f1389])).

fof(f6248,plain,
    ( spl5_1044
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6241,f1411,f1388,f960,f376,f299,f263,f6246])).

fof(f6241,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6240,f961])).

fof(f6240,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6239,f300])).

fof(f6239,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,sK2)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_59
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6238,f264])).

fof(f6238,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_59
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6115,f1389])).

fof(f6237,plain,
    ( spl5_1042
    | ~ spl5_36
    | ~ spl5_42
    | spl5_49
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6230,f1411,f1388,f324,f299,f263,f6235])).

fof(f6230,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_49
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6229,f300])).

fof(f6229,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_49
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6228,f264])).

fof(f6228,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_49
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6116,f1389])).

fof(f6227,plain,
    ( spl5_1040
    | ~ spl5_36
    | ~ spl5_42
    | spl5_113
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6220,f1411,f1388,f960,f654,f299,f263,f6225])).

fof(f6225,plain,
    ( spl5_1040
  <=> v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1040])])).

fof(f654,plain,
    ( spl5_113
  <=> ~ v1_xboole_0(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f6220,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_113
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6219,f961])).

fof(f6219,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_113
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6218,f300])).

fof(f6218,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_113
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6217,f264])).

fof(f6217,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_113
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6117,f1389])).

fof(f6117,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_113
    | ~ spl5_226 ),
    inference(unit_resulting_resolution,[],[f655,f1412,f64])).

fof(f655,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f654])).

fof(f6216,plain,
    ( spl5_1038
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6215,f1411,f1388,f299,f263,f106,f6201])).

fof(f6215,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6214,f300])).

fof(f6214,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6213,f264])).

fof(f6213,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6118,f1389])).

fof(f6212,plain,
    ( spl5_1038
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f6211,f3100,f1411,f1388,f354,f299,f263,f6201])).

fof(f6211,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6210,f300])).

fof(f6210,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6209,f264])).

fof(f6209,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6208,f3101])).

fof(f6208,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6119,f1389])).

fof(f6207,plain,
    ( spl5_1038
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6206,f1411,f1388,f299,f263,f106,f6201])).

fof(f6206,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6205,f300])).

fof(f6205,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6204,f264])).

fof(f6204,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6121,f1389])).

fof(f6203,plain,
    ( spl5_1038
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f6196,f3100,f1411,f1388,f354,f299,f263,f6201])).

fof(f6196,plain,
    ( k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6195,f300])).

fof(f6195,plain,
    ( k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6194,f264])).

fof(f6194,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f6193,f3101])).

fof(f6193,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6122,f1389])).

fof(f6189,plain,
    ( ~ spl5_1037
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6188,f1411,f1388,f960,f299,f263,f153,f6182])).

fof(f6182,plain,
    ( spl5_1037
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1037])])).

fof(f6188,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6187,f961])).

fof(f6187,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6186,f300])).

fof(f6186,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6185,f264])).

fof(f6185,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6125,f1389])).

fof(f6184,plain,
    ( ~ spl5_1037
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6177,f1411,f1388,f960,f347,f299,f263,f6182])).

fof(f6177,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6176,f961])).

fof(f6176,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6175,f300])).

fof(f6175,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6174,f264])).

fof(f6174,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0)))
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6126,f1389])).

fof(f6167,plain,
    ( ~ spl5_1035
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6166,f1411,f1388,f960,f299,f263,f153,f6146])).

fof(f6146,plain,
    ( spl5_1035
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1035])])).

fof(f6166,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6165,f961])).

fof(f6165,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6164,f300])).

fof(f6164,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6163,f264])).

fof(f6163,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6129,f1389])).

fof(f6162,plain,
    ( ~ spl5_1035
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6161,f1411,f1388,f960,f347,f299,f263,f6146])).

fof(f6161,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6160,f961])).

fof(f6160,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6159,f300])).

fof(f6159,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6158,f264])).

fof(f6158,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_52
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6130,f1389])).

fof(f6148,plain,
    ( ~ spl5_1035
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(avatar_split_clause,[],[f6141,f1411,f1388,f960,f299,f263,f153,f6146])).

fof(f6141,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6140,f961])).

fof(f6140,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6139,f300])).

fof(f6139,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6138,f264])).

fof(f6138,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_220
    | ~ spl5_226 ),
    inference(forward_demodulation,[],[f6134,f1389])).

fof(f6104,plain,
    ( spl5_1032
    | ~ spl5_262
    | spl5_951
    | ~ spl5_952
    | ~ spl5_1022 ),
    inference(avatar_split_clause,[],[f6097,f5971,f5476,f5467,f1622,f6102])).

fof(f6102,plain,
    ( spl5_1032
  <=> m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1032])])).

fof(f1622,plain,
    ( spl5_262
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_262])])).

fof(f5476,plain,
    ( spl5_952
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_952])])).

fof(f6097,plain,
    ( m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_262
    | ~ spl5_951
    | ~ spl5_952
    | ~ spl5_1022 ),
    inference(forward_demodulation,[],[f6063,f5972])).

fof(f6063,plain,
    ( m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_262
    | ~ spl5_951
    | ~ spl5_952 ),
    inference(unit_resulting_resolution,[],[f1623,f5477,f5468,f270])).

fof(f5477,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_952 ),
    inference(avatar_component_clause,[],[f5476])).

fof(f1623,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl5_262 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f6096,plain,
    ( spl5_1030
    | spl5_951 ),
    inference(avatar_split_clause,[],[f6069,f5467,f6094])).

fof(f6094,plain,
    ( spl5_1030
  <=> m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1030])])).

fof(f6069,plain,
    ( m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_951 ),
    inference(unit_resulting_resolution,[],[f5468,f146])).

fof(f6089,plain,
    ( ~ spl5_1029
    | spl5_951 ),
    inference(avatar_split_clause,[],[f6070,f5467,f6087])).

fof(f6087,plain,
    ( spl5_1029
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1029])])).

fof(f6070,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_951 ),
    inference(unit_resulting_resolution,[],[f5468,f147])).

fof(f6082,plain,
    ( ~ spl5_1027
    | spl5_951 ),
    inference(avatar_split_clause,[],[f6074,f5467,f6080])).

fof(f6080,plain,
    ( spl5_1027
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1027])])).

fof(f6074,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_951 ),
    inference(unit_resulting_resolution,[],[f121,f5468,f170])).

fof(f6007,plain,
    ( spl5_1024
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220 ),
    inference(avatar_split_clause,[],[f6003,f1388,f299,f263,f115,f103,f6005])).

fof(f6005,plain,
    ( spl5_1024
  <=> ! [X5] :
        ( ~ v1_funct_2(X5,o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(o_0_0_xboole_0))
        | r2_hidden(X5,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1024])])).

fof(f103,plain,
    ( spl5_7
  <=> ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f6003,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | ~ v1_funct_2(X5,o_0_0_xboole_0,o_0_0_xboole_0)
        | r2_hidden(X5,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ v1_funct_1(X5) )
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f6002,f300])).

fof(f6002,plain,
    ( ! [X5] :
        ( ~ v1_funct_2(X5,o_0_0_xboole_0,o_0_0_xboole_0)
        | r2_hidden(X5,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ v1_funct_1(X5)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f6001,f264])).

fof(f6001,plain,
    ( ! [X5] :
        ( r2_hidden(X5,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ v1_funct_2(X5,o_0_0_xboole_0,sK1)
        | ~ v1_funct_1(X5)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_8
    | ~ spl5_36
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f5961,f264])).

fof(f5961,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(o_0_0_xboole_0))
        | r2_hidden(X5,k1_funct_2(o_0_0_xboole_0,sK1))
        | ~ v1_funct_2(X5,o_0_0_xboole_0,sK1)
        | ~ v1_funct_1(X5)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_8
    | ~ spl5_220 ),
    inference(superposition,[],[f239,f1389])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | r2_hidden(X1,k1_funct_2(o_0_0_xboole_0,X2))
        | ~ v1_funct_2(X1,o_0_0_xboole_0,X2)
        | ~ v1_funct_1(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f238,f116])).

fof(f238,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k1_funct_2(o_0_0_xboole_0,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X1,k1_xboole_0,X2)
        | ~ v1_funct_1(X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f231,f116])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | r2_hidden(X1,k1_funct_2(k1_xboole_0,X2))
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f80,f59])).

fof(f5973,plain,
    ( spl5_1022
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220 ),
    inference(avatar_split_clause,[],[f5966,f1388,f299,f263,f5971])).

fof(f5966,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f5945,f300])).

fof(f5945,plain,
    ( k2_zfmisc_1(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_220 ),
    inference(superposition,[],[f1389,f264])).

fof(f5912,plain,
    ( spl5_1020
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_172
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5905,f2148,f1065,f960,f299,f263,f5910])).

fof(f5910,plain,
    ( spl5_1020
  <=> m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1020])])).

fof(f2148,plain,
    ( spl5_344
  <=> k2_zfmisc_1(o_0_0_xboole_0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_344])])).

fof(f5905,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_172
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f5904,f264])).

fof(f5904,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_172
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f5903,f961])).

fof(f5903,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,sK1,sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_172
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f5841,f2149])).

fof(f2149,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK1) = o_0_0_xboole_0
    | ~ spl5_344 ),
    inference(avatar_component_clause,[],[f2148])).

fof(f5799,plain,
    ( ~ spl5_1019
    | ~ spl5_36
    | ~ spl5_42
    | spl5_225 ),
    inference(avatar_split_clause,[],[f5798,f1400,f299,f263,f5795])).

fof(f5795,plain,
    ( spl5_1019
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1019])])).

fof(f5798,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_225 ),
    inference(forward_demodulation,[],[f5460,f300])).

fof(f5460,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_225 ),
    inference(superposition,[],[f1401,f264])).

fof(f5797,plain,
    ( ~ spl5_1019
    | ~ spl5_36
    | ~ spl5_42
    | spl5_223 ),
    inference(avatar_split_clause,[],[f5790,f1393,f299,f263,f5795])).

fof(f5790,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_223 ),
    inference(forward_demodulation,[],[f5459,f300])).

fof(f5459,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_223 ),
    inference(superposition,[],[f1394,f264])).

fof(f5789,plain,
    ( ~ spl5_1017
    | ~ spl5_36
    | ~ spl5_42
    | spl5_219 ),
    inference(avatar_split_clause,[],[f5782,f1381,f299,f263,f5787])).

fof(f5787,plain,
    ( spl5_1017
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1017])])).

fof(f5782,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f5458,f300])).

fof(f5458,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_219 ),
    inference(superposition,[],[f1382,f264])).

fof(f5781,plain,
    ( ~ spl5_1015
    | ~ spl5_36
    | ~ spl5_42
    | spl5_217 ),
    inference(avatar_split_clause,[],[f5774,f1372,f299,f263,f5779])).

fof(f1372,plain,
    ( spl5_217
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_217])])).

fof(f5774,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_217 ),
    inference(forward_demodulation,[],[f5457,f300])).

fof(f5457,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k2_zfmisc_1(sK0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_217 ),
    inference(superposition,[],[f1373,f264])).

fof(f1373,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_217 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f5773,plain,
    ( ~ spl5_965
    | ~ spl5_36
    | ~ spl5_156
    | spl5_199 ),
    inference(avatar_split_clause,[],[f5772,f1229,f960,f263,f5534])).

fof(f5534,plain,
    ( spl5_965
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_965])])).

fof(f5772,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_199 ),
    inference(forward_demodulation,[],[f5456,f961])).

fof(f5771,plain,
    ( ~ spl5_963
    | ~ spl5_36
    | ~ spl5_156
    | spl5_197 ),
    inference(avatar_split_clause,[],[f5770,f1226,f960,f263,f5525])).

fof(f5770,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_197 ),
    inference(forward_demodulation,[],[f5455,f961])).

fof(f5769,plain,
    ( spl5_1012
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f5762,f1065,f960,f299,f263,f5767])).

fof(f5767,plain,
    ( spl5_1012
  <=> m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1012])])).

fof(f5762,plain,
    ( m1_subset_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f5761,f961])).

fof(f5756,plain,
    ( ~ spl5_1011
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | spl5_169 ),
    inference(avatar_split_clause,[],[f5749,f1035,f960,f299,f263,f5754])).

fof(f5754,plain,
    ( spl5_1011
  <=> ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1011])])).

fof(f5749,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_169 ),
    inference(forward_demodulation,[],[f5748,f300])).

fof(f5748,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_169 ),
    inference(forward_demodulation,[],[f5452,f961])).

fof(f5745,plain,
    ( ~ spl5_1009
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | spl5_165 ),
    inference(avatar_split_clause,[],[f5738,f1008,f960,f299,f263,f5743])).

fof(f5743,plain,
    ( spl5_1009
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1009])])).

fof(f5738,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_165 ),
    inference(forward_demodulation,[],[f5737,f300])).

fof(f5737,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_165 ),
    inference(forward_demodulation,[],[f5450,f961])).

fof(f5734,plain,
    ( spl5_1006
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5727,f960,f917,f299,f263,f5732])).

fof(f5732,plain,
    ( spl5_1006
  <=> v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1006])])).

fof(f5727,plain,
    ( v1_funct_1(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_150
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5726,f300])).

fof(f5726,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_150
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5448,f961])).

fof(f5725,plain,
    ( ~ spl5_995
    | ~ spl5_36
    | ~ spl5_42
    | spl5_139
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5724,f960,f826,f299,f263,f5674])).

fof(f5674,plain,
    ( spl5_995
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_995])])).

fof(f5724,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_139
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5723,f300])).

fof(f5723,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_139
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5447,f961])).

fof(f5720,plain,
    ( ~ spl5_1005
    | ~ spl5_36
    | ~ spl5_42
    | spl5_113
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5713,f960,f654,f299,f263,f5718])).

fof(f5713,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_113
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5712,f961])).

fof(f5712,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_113 ),
    inference(forward_demodulation,[],[f5445,f300])).

fof(f5445,plain,
    ( ~ v1_xboole_0(sK4(k5_partfun1(sK0,o_0_0_xboole_0,sK2),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_113 ),
    inference(superposition,[],[f655,f264])).

fof(f5711,plain,
    ( ~ spl5_1003
    | ~ spl5_36
    | ~ spl5_42
    | spl5_111 ),
    inference(avatar_split_clause,[],[f5704,f650,f299,f263,f5709])).

fof(f5709,plain,
    ( spl5_1003
  <=> ~ r2_hidden(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1003])])).

fof(f650,plain,
    ( spl5_111
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f5704,plain,
    ( ~ r2_hidden(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),sK3(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_111 ),
    inference(forward_demodulation,[],[f5444,f300])).

fof(f5444,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK3(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_111 ),
    inference(superposition,[],[f651,f264])).

fof(f651,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f650])).

fof(f5701,plain,
    ( ~ spl5_1001
    | ~ spl5_36
    | spl5_107 ),
    inference(avatar_split_clause,[],[f5442,f636,f263,f5699])).

fof(f5699,plain,
    ( spl5_1001
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1001])])).

fof(f636,plain,
    ( spl5_107
  <=> ~ r2_hidden(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f5442,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_107 ),
    inference(superposition,[],[f637,f264])).

fof(f637,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f636])).

fof(f5694,plain,
    ( ~ spl5_999
    | ~ spl5_36
    | ~ spl5_42
    | spl5_103
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5687,f960,f612,f299,f263,f5692])).

fof(f5692,plain,
    ( spl5_999
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_999])])).

fof(f5687,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_103
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5686,f300])).

fof(f5686,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_103
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5441,f961])).

fof(f5685,plain,
    ( ~ spl5_997
    | ~ spl5_36
    | ~ spl5_42
    | spl5_91
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5678,f960,f546,f299,f263,f5683])).

fof(f5683,plain,
    ( spl5_997
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_997])])).

fof(f5678,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_91
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5677,f961])).

fof(f5676,plain,
    ( ~ spl5_995
    | ~ spl5_36
    | ~ spl5_42
    | spl5_87
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5669,f960,f523,f299,f263,f5674])).

fof(f5669,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_87
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5668,f300])).

fof(f5668,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_87
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5439,f961])).

fof(f5667,plain,
    ( spl5_992
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5660,f960,f493,f299,f263,f5665])).

fof(f5665,plain,
    ( spl5_992
  <=> v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_992])])).

fof(f5660,plain,
    ( v1_funct_2(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_82
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5659,f961])).

fof(f5658,plain,
    ( spl5_990
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5651,f960,f486,f299,f263,f5656])).

fof(f5656,plain,
    ( spl5_990
  <=> v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_990])])).

fof(f5651,plain,
    ( v1_funct_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_80
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5650,f961])).

fof(f5649,plain,
    ( ~ spl5_989
    | ~ spl5_36
    | ~ spl5_42
    | spl5_75
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5642,f960,f464,f299,f263,f5647])).

fof(f5647,plain,
    ( spl5_989
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_989])])).

fof(f5642,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_75
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5641,f300])).

fof(f5641,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_75
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5436,f961])).

fof(f5640,plain,
    ( ~ spl5_987
    | ~ spl5_36
    | ~ spl5_42
    | spl5_73
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5633,f960,f442,f299,f263,f5638])).

fof(f5638,plain,
    ( spl5_987
  <=> ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_987])])).

fof(f5633,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_73
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5632,f961])).

fof(f5631,plain,
    ( ~ spl5_985
    | ~ spl5_36
    | ~ spl5_42
    | spl5_71
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5624,f960,f433,f299,f263,f5629])).

fof(f5629,plain,
    ( spl5_985
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_985])])).

fof(f5624,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_71
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5623,f961])).

fof(f5622,plain,
    ( ~ spl5_983
    | ~ spl5_36
    | ~ spl5_42
    | spl5_69
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5615,f960,f426,f299,f263,f5620])).

fof(f5620,plain,
    ( spl5_983
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_983])])).

fof(f5615,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_69
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5614,f961])).

fof(f5612,plain,
    ( ~ spl5_981
    | ~ spl5_36
    | ~ spl5_42
    | spl5_65
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5605,f960,f407,f299,f263,f5610])).

fof(f5610,plain,
    ( spl5_981
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_981])])).

fof(f5605,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_65
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5604,f961])).

fof(f5601,plain,
    ( ~ spl5_979
    | ~ spl5_36
    | ~ spl5_42
    | spl5_63
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5594,f960,f390,f299,f263,f5599])).

fof(f5599,plain,
    ( spl5_979
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_979])])).

fof(f5594,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_63
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5593,f300])).

fof(f5593,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_63
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5429,f961])).

fof(f5592,plain,
    ( ~ spl5_977
    | ~ spl5_36
    | ~ spl5_42
    | spl5_61
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5591,f960,f383,f299,f263,f5587])).

fof(f5587,plain,
    ( spl5_977
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_977])])).

fof(f5591,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_61
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5590,f300])).

fof(f5590,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_61
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5428,f961])).

fof(f5589,plain,
    ( ~ spl5_977
    | ~ spl5_36
    | ~ spl5_42
    | spl5_59
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5582,f960,f376,f299,f263,f5587])).

fof(f5582,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_59
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5581,f300])).

fof(f5581,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_59
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5427,f961])).

fof(f5580,plain,
    ( ~ spl5_975
    | ~ spl5_36
    | ~ spl5_42
    | spl5_57
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5573,f960,f368,f299,f263,f5578])).

fof(f5578,plain,
    ( spl5_975
  <=> k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_975])])).

fof(f5573,plain,
    ( k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_57
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5572,f300])).

fof(f5572,plain,
    ( k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl5_36
    | ~ spl5_57
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5426,f961])).

fof(f5571,plain,
    ( spl5_972
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5564,f960,f354,f299,f263,f5569])).

fof(f5564,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_54
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5563,f300])).

fof(f5563,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_54
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5425,f961])).

fof(f5562,plain,
    ( spl5_970
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5555,f960,f347,f299,f263,f5560])).

fof(f5555,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_52
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5554,f300])).

fof(f5554,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_52
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5424,f961])).

fof(f5553,plain,
    ( ~ spl5_969
    | ~ spl5_36
    | ~ spl5_42
    | spl5_51
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5546,f960,f337,f299,f263,f5551])).

fof(f5551,plain,
    ( spl5_969
  <=> ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_969])])).

fof(f5546,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_51
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5545,f300])).

fof(f5545,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_51
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5423,f961])).

fof(f5544,plain,
    ( ~ spl5_967
    | ~ spl5_36
    | ~ spl5_42
    | spl5_45 ),
    inference(avatar_split_clause,[],[f5537,f304,f299,f263,f5542])).

fof(f5542,plain,
    ( spl5_967
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_967])])).

fof(f5537,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_45 ),
    inference(forward_demodulation,[],[f5422,f300])).

fof(f5422,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),sK0))
    | ~ spl5_36
    | ~ spl5_45 ),
    inference(superposition,[],[f305,f264])).

fof(f5536,plain,
    ( ~ spl5_965
    | spl5_35
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5529,f960,f299,f263,f254,f5534])).

fof(f5529,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_35
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5528,f961])).

fof(f5527,plain,
    ( ~ spl5_963
    | spl5_33
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5520,f960,f299,f263,f251,f5525])).

fof(f5520,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_33
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5519,f961])).

fof(f5518,plain,
    ( ~ spl5_961
    | spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5511,f960,f299,f263,f223,f5516])).

fof(f5511,plain,
    ( ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5510,f300])).

fof(f5510,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_31
    | ~ spl5_36
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5419,f961])).

fof(f5507,plain,
    ( ~ spl5_959
    | spl5_17
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5500,f960,f299,f263,f164,f5505])).

fof(f5500,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_17
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5499,f961])).

fof(f5498,plain,
    ( spl5_956
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5491,f960,f299,f263,f153,f5496])).

fof(f5491,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5490,f300])).

fof(f5490,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,o_0_0_xboole_0)),k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_36
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5416,f961])).

fof(f5489,plain,
    ( ~ spl5_955
    | spl5_13
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5482,f960,f299,f263,f135,f5487])).

fof(f5482,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_13
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5481,f961])).

fof(f5478,plain,
    ( spl5_952
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5471,f960,f299,f263,f92,f5476])).

fof(f5471,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_2
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5470,f961])).

fof(f5469,plain,
    ( ~ spl5_951
    | spl5_1
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f5462,f960,f299,f263,f85,f5467])).

fof(f5462,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_1
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f5461,f961])).

fof(f5400,plain,
    ( ~ spl5_949
    | ~ spl5_36
    | ~ spl5_42
    | spl5_261 ),
    inference(avatar_split_clause,[],[f5399,f1608,f299,f263,f5380])).

fof(f5380,plain,
    ( spl5_949
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_949])])).

fof(f1608,plain,
    ( spl5_261
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_261])])).

fof(f5399,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_261 ),
    inference(forward_demodulation,[],[f5398,f300])).

fof(f5398,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_261 ),
    inference(forward_demodulation,[],[f1609,f264])).

fof(f1609,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_261 ),
    inference(avatar_component_clause,[],[f1608])).

fof(f5394,plain,
    ( ~ spl5_949
    | ~ spl5_36
    | spl5_281 ),
    inference(avatar_split_clause,[],[f5393,f1733,f263,f5380])).

fof(f1733,plain,
    ( spl5_281
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_281])])).

fof(f5393,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_281 ),
    inference(forward_demodulation,[],[f1734,f264])).

fof(f1734,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_281 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f5392,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | spl5_319 ),
    inference(avatar_split_clause,[],[f5391,f1992,f960,f299,f263,f1753])).

fof(f1753,plain,
    ( spl5_285
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_285])])).

fof(f1992,plain,
    ( spl5_319
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_319])])).

fof(f5391,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_319 ),
    inference(forward_demodulation,[],[f5390,f961])).

fof(f5390,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_319 ),
    inference(forward_demodulation,[],[f5389,f300])).

fof(f5389,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_319 ),
    inference(forward_demodulation,[],[f1993,f264])).

fof(f1993,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,sK1)))
    | ~ spl5_319 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f5388,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | spl5_321 ),
    inference(avatar_split_clause,[],[f5387,f1999,f299,f263,f1753])).

fof(f1999,plain,
    ( spl5_321
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_321])])).

fof(f5387,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_321 ),
    inference(forward_demodulation,[],[f5386,f300])).

fof(f5386,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_321 ),
    inference(forward_demodulation,[],[f2000,f264])).

fof(f2000,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,sK1)))
    | ~ spl5_321 ),
    inference(avatar_component_clause,[],[f1999])).

fof(f5385,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | spl5_323 ),
    inference(avatar_split_clause,[],[f5384,f2006,f299,f263,f1753])).

fof(f2006,plain,
    ( spl5_323
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_323])])).

fof(f5384,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_323 ),
    inference(forward_demodulation,[],[f5383,f300])).

fof(f5383,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_323 ),
    inference(forward_demodulation,[],[f2007,f264])).

fof(f2007,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,sK1)))
    | ~ spl5_323 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f5382,plain,
    ( ~ spl5_949
    | ~ spl5_36
    | ~ spl5_42
    | spl5_327 ),
    inference(avatar_split_clause,[],[f5375,f2020,f299,f263,f5380])).

fof(f2020,plain,
    ( spl5_327
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_327])])).

fof(f5375,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_327 ),
    inference(forward_demodulation,[],[f5374,f300])).

fof(f5374,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,o_0_0_xboole_0),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_327 ),
    inference(forward_demodulation,[],[f2021,f264])).

fof(f2021,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl5_327 ),
    inference(avatar_component_clause,[],[f2020])).

fof(f5373,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | spl5_377 ),
    inference(avatar_split_clause,[],[f5372,f2297,f299,f1753])).

fof(f2297,plain,
    ( spl5_377
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_377])])).

fof(f5372,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_377 ),
    inference(forward_demodulation,[],[f2298,f300])).

fof(f2298,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_377 ),
    inference(avatar_component_clause,[],[f2297])).

fof(f5371,plain,
    ( ~ spl5_285
    | ~ spl5_220
    | spl5_383 ),
    inference(avatar_split_clause,[],[f5370,f2319,f1388,f1753])).

fof(f2319,plain,
    ( spl5_383
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_383])])).

fof(f5370,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_383 ),
    inference(forward_demodulation,[],[f2320,f1389])).

fof(f2320,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_383 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f5369,plain,
    ( ~ spl5_285
    | ~ spl5_156
    | ~ spl5_220
    | spl5_411 ),
    inference(avatar_split_clause,[],[f5368,f2495,f1388,f960,f1753])).

fof(f2495,plain,
    ( spl5_411
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_411])])).

fof(f5368,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_411 ),
    inference(forward_demodulation,[],[f5367,f961])).

fof(f5367,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_411 ),
    inference(forward_demodulation,[],[f2496,f1389])).

fof(f2496,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_411 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f5366,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_220
    | spl5_413 ),
    inference(avatar_split_clause,[],[f5365,f2502,f1388,f263,f1753])).

fof(f5365,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_413 ),
    inference(forward_demodulation,[],[f5364,f264])).

fof(f5364,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_413 ),
    inference(forward_demodulation,[],[f2503,f1389])).

fof(f5363,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_220
    | spl5_415 ),
    inference(avatar_split_clause,[],[f5362,f2509,f1388,f299,f1753])).

fof(f5362,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_415 ),
    inference(forward_demodulation,[],[f5361,f300])).

fof(f5361,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_415 ),
    inference(forward_demodulation,[],[f2510,f1389])).

fof(f5360,plain,
    ( ~ spl5_285
    | ~ spl5_220
    | ~ spl5_344
    | spl5_423 ),
    inference(avatar_split_clause,[],[f5359,f2537,f2148,f1388,f1753])).

fof(f2537,plain,
    ( spl5_423
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_423])])).

fof(f5359,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_344
    | ~ spl5_423 ),
    inference(forward_demodulation,[],[f5358,f2149])).

fof(f5358,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_423 ),
    inference(forward_demodulation,[],[f2538,f1389])).

fof(f2538,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_423 ),
    inference(avatar_component_clause,[],[f2537])).

fof(f5357,plain,
    ( ~ spl5_285
    | ~ spl5_220
    | spl5_425 ),
    inference(avatar_split_clause,[],[f5356,f2544,f1388,f1753])).

fof(f2544,plain,
    ( spl5_425
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_425])])).

fof(f5356,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_425 ),
    inference(forward_demodulation,[],[f2545,f1389])).

fof(f2545,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_425 ),
    inference(avatar_component_clause,[],[f2544])).

fof(f5355,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_344
    | spl5_569 ),
    inference(avatar_split_clause,[],[f5354,f3287,f2148,f960,f299,f1753])).

fof(f3287,plain,
    ( spl5_569
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_569])])).

fof(f5354,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_344
    | ~ spl5_569 ),
    inference(forward_demodulation,[],[f5353,f961])).

fof(f5353,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_344
    | ~ spl5_569 ),
    inference(forward_demodulation,[],[f5352,f2149])).

fof(f5352,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_569 ),
    inference(forward_demodulation,[],[f3288,f300])).

fof(f3288,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_569 ),
    inference(avatar_component_clause,[],[f3287])).

fof(f5351,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_344
    | spl5_571 ),
    inference(avatar_split_clause,[],[f5350,f3294,f2148,f299,f263,f1753])).

fof(f5350,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_344
    | ~ spl5_571 ),
    inference(forward_demodulation,[],[f5349,f264])).

fof(f5349,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_344
    | ~ spl5_571 ),
    inference(forward_demodulation,[],[f5348,f2149])).

fof(f5347,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_344
    | spl5_573 ),
    inference(avatar_split_clause,[],[f5346,f3301,f2148,f299,f1753])).

fof(f5346,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_344
    | ~ spl5_573 ),
    inference(forward_demodulation,[],[f5345,f2149])).

fof(f5344,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_344
    | spl5_581 ),
    inference(avatar_split_clause,[],[f5343,f3329,f2148,f299,f1753])).

fof(f3329,plain,
    ( spl5_581
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_581])])).

fof(f5343,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_344
    | ~ spl5_581 ),
    inference(forward_demodulation,[],[f5342,f2149])).

fof(f5342,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_581 ),
    inference(forward_demodulation,[],[f3330,f300])).

fof(f3330,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_581 ),
    inference(avatar_component_clause,[],[f3329])).

fof(f5341,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_220
    | spl5_597 ),
    inference(avatar_split_clause,[],[f5340,f3441,f1388,f960,f263,f1753])).

fof(f5340,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_597 ),
    inference(forward_demodulation,[],[f5339,f961])).

fof(f5339,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_597 ),
    inference(forward_demodulation,[],[f5338,f264])).

fof(f5338,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_597 ),
    inference(forward_demodulation,[],[f3442,f1389])).

fof(f5337,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_220
    | spl5_599 ),
    inference(avatar_split_clause,[],[f5336,f3448,f1388,f263,f1753])).

fof(f3448,plain,
    ( spl5_599
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_599])])).

fof(f5336,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_599 ),
    inference(forward_demodulation,[],[f5335,f264])).

fof(f5335,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_599 ),
    inference(forward_demodulation,[],[f3449,f1389])).

fof(f3449,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_599 ),
    inference(avatar_component_clause,[],[f3448])).

fof(f5334,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | spl5_601 ),
    inference(avatar_split_clause,[],[f5333,f3455,f1388,f299,f263,f1753])).

fof(f3455,plain,
    ( spl5_601
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_601])])).

fof(f5333,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_601 ),
    inference(forward_demodulation,[],[f5332,f300])).

fof(f5332,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_601 ),
    inference(forward_demodulation,[],[f5331,f264])).

fof(f5331,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_601 ),
    inference(forward_demodulation,[],[f3456,f1389])).

fof(f3456,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_601 ),
    inference(avatar_component_clause,[],[f3455])).

fof(f5330,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_220
    | spl5_611 ),
    inference(avatar_split_clause,[],[f5329,f3490,f1388,f263,f1753])).

fof(f5329,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_220
    | ~ spl5_611 ),
    inference(forward_demodulation,[],[f5328,f264])).

fof(f5328,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_611 ),
    inference(forward_demodulation,[],[f3491,f1389])).

fof(f5327,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | spl5_627 ),
    inference(avatar_split_clause,[],[f5326,f3600,f1388,f960,f299,f1753])).

fof(f5326,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_220
    | ~ spl5_627 ),
    inference(forward_demodulation,[],[f5325,f961])).

fof(f5325,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_627 ),
    inference(forward_demodulation,[],[f5324,f300])).

fof(f5324,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_627 ),
    inference(forward_demodulation,[],[f3601,f1389])).

fof(f5323,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | spl5_629 ),
    inference(avatar_split_clause,[],[f5322,f3607,f1388,f299,f263,f1753])).

fof(f3607,plain,
    ( spl5_629
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_629])])).

fof(f5322,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_629 ),
    inference(forward_demodulation,[],[f5321,f264])).

fof(f5321,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_629 ),
    inference(forward_demodulation,[],[f5320,f300])).

fof(f5320,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_629 ),
    inference(forward_demodulation,[],[f3608,f1389])).

fof(f3608,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_629 ),
    inference(avatar_component_clause,[],[f3607])).

fof(f5319,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_220
    | spl5_631 ),
    inference(avatar_split_clause,[],[f5318,f3614,f1388,f299,f1753])).

fof(f3614,plain,
    ( spl5_631
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_631])])).

fof(f5318,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_631 ),
    inference(forward_demodulation,[],[f5317,f300])).

fof(f5317,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_631 ),
    inference(forward_demodulation,[],[f3615,f1389])).

fof(f3615,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_631 ),
    inference(avatar_component_clause,[],[f3614])).

fof(f5316,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | ~ spl5_220
    | spl5_643 ),
    inference(avatar_split_clause,[],[f5315,f3656,f1388,f299,f1753])).

fof(f5315,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_220
    | ~ spl5_643 ),
    inference(forward_demodulation,[],[f5314,f300])).

fof(f5314,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_643 ),
    inference(forward_demodulation,[],[f3657,f1389])).

fof(f5310,plain,
    ( spl5_946
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_930 ),
    inference(avatar_split_clause,[],[f5303,f5121,f960,f299,f263,f5308])).

fof(f5308,plain,
    ( spl5_946
  <=> v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_946])])).

fof(f5303,plain,
    ( v1_funct_2(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_930 ),
    inference(forward_demodulation,[],[f5302,f300])).

fof(f5302,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_930 ),
    inference(forward_demodulation,[],[f5301,f961])).

fof(f5300,plain,
    ( spl5_944
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_932 ),
    inference(avatar_split_clause,[],[f5293,f5130,f960,f299,f263,f5298])).

fof(f5298,plain,
    ( spl5_944
  <=> r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_944])])).

fof(f5293,plain,
    ( r2_hidden(sK3(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_156
    | ~ spl5_932 ),
    inference(forward_demodulation,[],[f5292,f300])).

fof(f5292,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_36
    | ~ spl5_156
    | ~ spl5_932 ),
    inference(forward_demodulation,[],[f5291,f961])).

fof(f5290,plain,
    ( ~ spl5_285
    | ~ spl5_220
    | spl5_935 ),
    inference(avatar_split_clause,[],[f5289,f5175,f1388,f1753])).

fof(f5289,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_220
    | ~ spl5_935 ),
    inference(forward_demodulation,[],[f5176,f1389])).

fof(f5288,plain,
    ( ~ spl5_285
    | ~ spl5_36
    | spl5_937 ),
    inference(avatar_split_clause,[],[f5287,f5201,f263,f1753])).

fof(f5201,plain,
    ( spl5_937
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_937])])).

fof(f5287,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_36
    | ~ spl5_937 ),
    inference(forward_demodulation,[],[f5202,f264])).

fof(f5202,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_937 ),
    inference(avatar_component_clause,[],[f5201])).

fof(f5286,plain,
    ( spl5_942
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_940 ),
    inference(avatar_split_clause,[],[f5279,f5230,f299,f263,f5284])).

fof(f5284,plain,
    ( spl5_942
  <=> r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_942])])).

fof(f5230,plain,
    ( spl5_940
  <=> r1_tarski(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK0,sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_940])])).

fof(f5279,plain,
    ( r1_tarski(sK4(k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_42
    | ~ spl5_940 ),
    inference(forward_demodulation,[],[f5278,f300])).

fof(f5278,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl5_36
    | ~ spl5_940 ),
    inference(forward_demodulation,[],[f5231,f264])).

fof(f5231,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK0,sK1)),o_0_0_xboole_0)
    | ~ spl5_940 ),
    inference(avatar_component_clause,[],[f5230])).

fof(f5241,plain,
    ( spl5_936
    | ~ spl5_42
    | ~ spl5_260
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5240,f2148,f1611,f299,f5204])).

fof(f5204,plain,
    ( spl5_936
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_936])])).

fof(f1611,plain,
    ( spl5_260
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_260])])).

fof(f5240,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_260
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f1731,f2149])).

fof(f1731,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_260 ),
    inference(forward_demodulation,[],[f1612,f300])).

fof(f1612,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_260 ),
    inference(avatar_component_clause,[],[f1611])).

fof(f5232,plain,
    ( spl5_940
    | ~ spl5_148
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(avatar_split_clause,[],[f5225,f1388,f960,f902,f5230])).

fof(f5225,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK0,sK1)),o_0_0_xboole_0)
    | ~ spl5_148
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f5224,f961])).

fof(f5224,plain,
    ( r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0)
    | ~ spl5_148
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f903,f1389])).

fof(f5223,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_263
    | ~ spl5_939
    | spl5_31
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(avatar_split_clause,[],[f5222,f1388,f960,f223,f5219,f1625,f220,f214])).

fof(f214,plain,
    ( spl5_26
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f220,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f5219,plain,
    ( spl5_939
  <=> ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_939])])).

fof(f5222,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_31
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f1620,f1389])).

fof(f1620,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_31
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1619,f961])).

fof(f1619,plain,
    ( ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_31
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f995,f961])).

fof(f995,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_31 ),
    inference(resolution,[],[f224,f209])).

fof(f209,plain,(
    ! [X4,X2,X3] :
      ( v1_xboole_0(k5_partfun1(X2,X3,X4))
      | ~ v1_funct_1(X4)
      | ~ v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3)) ) ),
    inference(resolution,[],[f72,f69])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_xboole_0(k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2)
        & v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k5_partfun1(X0,X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',fc2_partfun1)).

fof(f5221,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_263
    | ~ spl5_939
    | spl5_31
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(avatar_split_clause,[],[f5214,f1388,f960,f223,f5219,f1625,f220,f214])).

fof(f5214,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_31
    | ~ spl5_156
    | ~ spl5_220 ),
    inference(forward_demodulation,[],[f1635,f1389])).

fof(f1635,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_31
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1634,f961])).

fof(f1634,plain,
    ( ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_31
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f871,f961])).

fof(f871,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_31 ),
    inference(resolution,[],[f209,f224])).

fof(f5212,plain,
    ( ~ spl5_49
    | ~ spl5_156
    | spl5_159 ),
    inference(avatar_split_clause,[],[f1662,f965,f960,f324])).

fof(f965,plain,
    ( spl5_159
  <=> ~ v1_xboole_0(k1_funct_2(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1662,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_156
    | ~ spl5_159 ),
    inference(forward_demodulation,[],[f966,f961])).

fof(f966,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,sK2))
    | ~ spl5_159 ),
    inference(avatar_component_clause,[],[f965])).

fof(f5206,plain,
    ( spl5_936
    | ~ spl5_280
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5199,f2148,f1736,f5204])).

fof(f1736,plain,
    ( spl5_280
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_280])])).

fof(f5199,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_280
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f1737,f2149])).

fof(f1737,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_280 ),
    inference(avatar_component_clause,[],[f1736])).

fof(f5197,plain,
    ( spl5_94
    | ~ spl5_332
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5196,f2148,f2103,f567])).

fof(f567,plain,
    ( spl5_94
  <=> r1_tarski(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f2103,plain,
    ( spl5_332
  <=> r1_tarski(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_332])])).

fof(f5196,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_332
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f2104,f2149])).

fof(f2104,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_332 ),
    inference(avatar_component_clause,[],[f2103])).

fof(f5195,plain,
    ( spl5_228
    | ~ spl5_334
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5194,f2148,f2110,f1471])).

fof(f1471,plain,
    ( spl5_228
  <=> r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_228])])).

fof(f2110,plain,
    ( spl5_334
  <=> r1_tarski(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_334])])).

fof(f5194,plain,
    ( r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_334
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f2111,f2149])).

fof(f2111,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_334 ),
    inference(avatar_component_clause,[],[f2110])).

fof(f5193,plain,
    ( spl5_92
    | ~ spl5_338
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5192,f2148,f2124,f560])).

fof(f560,plain,
    ( spl5_92
  <=> m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f2124,plain,
    ( spl5_338
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_338])])).

fof(f5192,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_338
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f2125,f2149])).

fof(f2125,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_338 ),
    inference(avatar_component_clause,[],[f2124])).

fof(f5191,plain,
    ( spl5_232
    | ~ spl5_340
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5190,f2148,f2131,f1485])).

fof(f1485,plain,
    ( spl5_232
  <=> m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f2131,plain,
    ( spl5_340
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_340])])).

fof(f5190,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_340
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f2132,f2149])).

fof(f2132,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_340 ),
    inference(avatar_component_clause,[],[f2131])).

fof(f5189,plain,
    ( ~ spl5_145
    | ~ spl5_344
    | spl5_347 ),
    inference(avatar_split_clause,[],[f5188,f2153,f2148,f849])).

fof(f849,plain,
    ( spl5_145
  <=> ~ v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f5188,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0))
    | ~ spl5_344
    | ~ spl5_347 ),
    inference(forward_demodulation,[],[f2154,f2149])).

fof(f5187,plain,
    ( ~ spl5_49
    | ~ spl5_344
    | spl5_349 ),
    inference(avatar_split_clause,[],[f5186,f2160,f2148,f324])).

fof(f2160,plain,
    ( spl5_349
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_349])])).

fof(f5186,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_344
    | ~ spl5_349 ),
    inference(forward_demodulation,[],[f2161,f2149])).

fof(f2161,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_349 ),
    inference(avatar_component_clause,[],[f2160])).

fof(f5185,plain,
    ( ~ spl5_41
    | ~ spl5_344
    | spl5_351 ),
    inference(avatar_split_clause,[],[f5184,f2167,f2148,f281])).

fof(f281,plain,
    ( spl5_41
  <=> ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f2167,plain,
    ( spl5_351
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_351])])).

fof(f5184,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_344
    | ~ spl5_351 ),
    inference(forward_demodulation,[],[f2168,f2149])).

fof(f2168,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_351 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f5183,plain,
    ( ~ spl5_25
    | ~ spl5_344
    | spl5_357 ),
    inference(avatar_split_clause,[],[f5182,f2188,f2148,f195])).

fof(f195,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f5182,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_344
    | ~ spl5_357 ),
    inference(forward_demodulation,[],[f2189,f2149])).

fof(f5180,plain,
    ( spl5_934
    | ~ spl5_344
    | ~ spl5_422 ),
    inference(avatar_split_clause,[],[f5173,f2540,f2148,f5178])).

fof(f5178,plain,
    ( spl5_934
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_934])])).

fof(f5173,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_344
    | ~ spl5_422 ),
    inference(forward_demodulation,[],[f2541,f2149])).

fof(f5172,plain,
    ( spl5_94
    | ~ spl5_436
    | ~ spl5_448 ),
    inference(avatar_split_clause,[],[f5171,f2696,f2650,f567])).

fof(f2650,plain,
    ( spl5_436
  <=> r1_tarski(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_436])])).

fof(f2696,plain,
    ( spl5_448
  <=> o_0_0_xboole_0 = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_448])])).

fof(f5171,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_436
    | ~ spl5_448 ),
    inference(forward_demodulation,[],[f2651,f2697])).

fof(f2697,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_448 ),
    inference(avatar_component_clause,[],[f2696])).

fof(f2651,plain,
    ( r1_tarski(sK0,sK3(sK0))
    | ~ spl5_436 ),
    inference(avatar_component_clause,[],[f2650])).

fof(f5170,plain,
    ( spl5_228
    | ~ spl5_438
    | ~ spl5_448 ),
    inference(avatar_split_clause,[],[f5169,f2696,f2657,f1471])).

fof(f2657,plain,
    ( spl5_438
  <=> r1_tarski(sK1,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_438])])).

fof(f5169,plain,
    ( r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_438
    | ~ spl5_448 ),
    inference(forward_demodulation,[],[f2658,f2697])).

fof(f2658,plain,
    ( r1_tarski(sK1,sK3(sK0))
    | ~ spl5_438 ),
    inference(avatar_component_clause,[],[f2657])).

fof(f5168,plain,
    ( spl5_92
    | ~ spl5_442
    | ~ spl5_448 ),
    inference(avatar_split_clause,[],[f5167,f2696,f2671,f560])).

fof(f5167,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_442
    | ~ spl5_448 ),
    inference(forward_demodulation,[],[f2672,f2697])).

fof(f5166,plain,
    ( spl5_232
    | ~ spl5_444
    | ~ spl5_448 ),
    inference(avatar_split_clause,[],[f5165,f2696,f2678,f1485])).

fof(f5165,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_444
    | ~ spl5_448 ),
    inference(forward_demodulation,[],[f2679,f2697])).

fof(f5164,plain,
    ( ~ spl5_145
    | ~ spl5_448
    | spl5_451 ),
    inference(avatar_split_clause,[],[f5163,f2704,f2696,f849])).

fof(f5163,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0))
    | ~ spl5_448
    | ~ spl5_451 ),
    inference(forward_demodulation,[],[f2705,f2697])).

fof(f5162,plain,
    ( ~ spl5_49
    | ~ spl5_448
    | spl5_453 ),
    inference(avatar_split_clause,[],[f5161,f2711,f2696,f324])).

fof(f2711,plain,
    ( spl5_453
  <=> ~ v1_xboole_0(k1_funct_2(sK1,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_453])])).

fof(f5161,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_448
    | ~ spl5_453 ),
    inference(forward_demodulation,[],[f2712,f2697])).

fof(f2712,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,sK3(sK0)))
    | ~ spl5_453 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f5160,plain,
    ( ~ spl5_41
    | ~ spl5_448
    | spl5_455 ),
    inference(avatar_split_clause,[],[f5159,f2718,f2696,f281])).

fof(f2718,plain,
    ( spl5_455
  <=> ~ v1_xboole_0(k1_funct_2(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_455])])).

fof(f5159,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_448
    | ~ spl5_455 ),
    inference(forward_demodulation,[],[f2719,f2697])).

fof(f2719,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,sK3(sK0)))
    | ~ spl5_455 ),
    inference(avatar_component_clause,[],[f2718])).

fof(f5158,plain,
    ( ~ spl5_25
    | ~ spl5_448
    | spl5_463 ),
    inference(avatar_split_clause,[],[f5157,f2746,f2696,f195])).

fof(f5157,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_448
    | ~ spl5_463 ),
    inference(forward_demodulation,[],[f2747,f2697])).

fof(f5156,plain,
    ( spl5_94
    | ~ spl5_518
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f5155,f3100,f3054,f567])).

fof(f3054,plain,
    ( spl5_518
  <=> r1_tarski(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_518])])).

fof(f5155,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_518
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3055,f3101])).

fof(f3055,plain,
    ( r1_tarski(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_518 ),
    inference(avatar_component_clause,[],[f3054])).

fof(f5154,plain,
    ( spl5_228
    | ~ spl5_520
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f5153,f3100,f3061,f1471])).

fof(f3061,plain,
    ( spl5_520
  <=> r1_tarski(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_520])])).

fof(f5153,plain,
    ( r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_520
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3062,f3101])).

fof(f3062,plain,
    ( r1_tarski(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_520 ),
    inference(avatar_component_clause,[],[f3061])).

fof(f5152,plain,
    ( spl5_92
    | ~ spl5_524
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f5151,f3100,f3075,f560])).

fof(f3075,plain,
    ( spl5_524
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_524])])).

fof(f5151,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_524
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3076,f3101])).

fof(f3076,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_524 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f5150,plain,
    ( spl5_232
    | ~ spl5_526
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f5149,f3100,f3082,f1485])).

fof(f3082,plain,
    ( spl5_526
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_526])])).

fof(f5149,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_526
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3083,f3101])).

fof(f3083,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_526 ),
    inference(avatar_component_clause,[],[f3082])).

fof(f5148,plain,
    ( ~ spl5_145
    | ~ spl5_530
    | spl5_535 ),
    inference(avatar_split_clause,[],[f5147,f3115,f3100,f849])).

fof(f3115,plain,
    ( spl5_535
  <=> ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_535])])).

fof(f5147,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_535 ),
    inference(forward_demodulation,[],[f3116,f3101])).

fof(f3116,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_535 ),
    inference(avatar_component_clause,[],[f3115])).

fof(f5146,plain,
    ( ~ spl5_49
    | ~ spl5_530
    | spl5_537 ),
    inference(avatar_split_clause,[],[f5145,f3122,f3100,f324])).

fof(f3122,plain,
    ( spl5_537
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_537])])).

fof(f5145,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_537 ),
    inference(forward_demodulation,[],[f3123,f3101])).

fof(f3123,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_537 ),
    inference(avatar_component_clause,[],[f3122])).

fof(f5144,plain,
    ( ~ spl5_41
    | ~ spl5_530
    | spl5_539 ),
    inference(avatar_split_clause,[],[f5143,f3129,f3100,f281])).

fof(f3129,plain,
    ( spl5_539
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_539])])).

fof(f5143,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_539 ),
    inference(forward_demodulation,[],[f3130,f3101])).

fof(f3130,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_539 ),
    inference(avatar_component_clause,[],[f3129])).

fof(f5142,plain,
    ( ~ spl5_25
    | ~ spl5_530
    | spl5_553 ),
    inference(avatar_split_clause,[],[f5141,f3178,f3100,f195])).

fof(f3178,plain,
    ( spl5_553
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_553])])).

fof(f5141,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_553 ),
    inference(forward_demodulation,[],[f3179,f3101])).

fof(f3179,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_553 ),
    inference(avatar_component_clause,[],[f3178])).

fof(f5140,plain,
    ( ~ spl5_149
    | ~ spl5_81
    | ~ spl5_83
    | spl5_36
    | ~ spl5_8
    | spl5_17 ),
    inference(avatar_split_clause,[],[f2037,f164,f115,f263,f490,f483,f905])).

fof(f905,plain,
    ( spl5_149
  <=> ~ r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f483,plain,
    ( spl5_81
  <=> ~ v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f490,plain,
    ( spl5_83
  <=> ~ v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f2037,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(resolution,[],[f165,f267])).

fof(f267,plain,
    ( ! [X4,X2,X3] :
        ( r2_hidden(X3,k1_funct_2(X4,X2))
        | o_0_0_xboole_0 = X2
        | ~ v1_funct_2(X3,X4,X2)
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(X3,k2_zfmisc_1(X4,X2)) )
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f245,f116])).

fof(f245,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 = X2
      | r2_hidden(X3,k1_funct_2(X4,X2))
      | ~ v1_funct_2(X3,X4,X2)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X2)) ) ),
    inference(resolution,[],[f73,f69])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | r2_hidden(X2,k1_funct_2(X0,X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5139,plain,
    ( ~ spl5_11
    | spl5_26
    | ~ spl5_29
    | ~ spl5_5
    | spl5_31 ),
    inference(avatar_split_clause,[],[f995,f223,f96,f220,f214,f125])).

fof(f125,plain,
    ( spl5_11
  <=> ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f96,plain,
    ( spl5_5
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f5138,plain,
    ( ~ spl5_11
    | spl5_26
    | ~ spl5_29
    | ~ spl5_5
    | spl5_31 ),
    inference(avatar_split_clause,[],[f871,f223,f96,f220,f214,f125])).

fof(f5137,plain,
    ( spl5_26
    | ~ spl5_29
    | spl5_67 ),
    inference(avatar_split_clause,[],[f2047,f410,f220,f214])).

fof(f2047,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_67 ),
    inference(resolution,[],[f411,f64])).

fof(f5136,plain,
    ( spl5_26
    | ~ spl5_29
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1911,f410,f220,f214])).

fof(f1911,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_67 ),
    inference(resolution,[],[f411,f64])).

fof(f5135,plain,
    ( spl5_26
    | ~ spl5_29
    | spl5_67 ),
    inference(avatar_split_clause,[],[f2952,f410,f220,f214])).

fof(f2952,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_67 ),
    inference(resolution,[],[f411,f64])).

fof(f5134,plain,
    ( spl5_20
    | ~ spl5_27
    | spl5_45 ),
    inference(avatar_split_clause,[],[f2594,f304,f211,f179])).

fof(f179,plain,
    ( spl5_20
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f211,plain,
    ( spl5_27
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f2594,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_45 ),
    inference(resolution,[],[f305,f64])).

fof(f5133,plain,
    ( spl5_20
    | ~ spl5_27
    | spl5_45 ),
    inference(avatar_split_clause,[],[f3350,f304,f211,f179])).

fof(f3350,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_45 ),
    inference(resolution,[],[f305,f64])).

fof(f5132,plain,
    ( ~ spl5_27
    | ~ spl5_151
    | ~ spl5_931
    | spl5_932
    | ~ spl5_8
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4926,f1065,f115,f5130,f5124,f914,f211])).

fof(f914,plain,
    ( spl5_151
  <=> ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f5124,plain,
    ( spl5_931
  <=> ~ v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_931])])).

fof(f4926,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0,sK1)
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ v1_xboole_0(sK0)
    | ~ spl5_8
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f239])).

fof(f5119,plain,
    ( spl5_28
    | ~ spl5_21
    | spl5_223 ),
    inference(avatar_split_clause,[],[f2964,f1393,f182,f217])).

fof(f217,plain,
    ( spl5_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f2964,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_223 ),
    inference(resolution,[],[f1394,f64])).

fof(f5118,plain,
    ( spl5_28
    | ~ spl5_21
    | spl5_223 ),
    inference(avatar_split_clause,[],[f3508,f1393,f182,f217])).

fof(f3508,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_223 ),
    inference(resolution,[],[f1394,f64])).

fof(f5117,plain,
    ( spl5_26
    | ~ spl5_21
    | spl5_225 ),
    inference(avatar_split_clause,[],[f2999,f1400,f182,f214])).

fof(f2999,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl5_225 ),
    inference(resolution,[],[f1401,f64])).

fof(f5116,plain,
    ( spl5_26
    | ~ spl5_21
    | spl5_225 ),
    inference(avatar_split_clause,[],[f3674,f1400,f182,f214])).

fof(f3674,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl5_225 ),
    inference(resolution,[],[f1401,f64])).

fof(f5115,plain,
    ( spl5_928
    | ~ spl5_21
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4930,f1065,f182,f5113])).

fof(f5113,plain,
    ( spl5_928
  <=> ! [X3] : ~ r2_hidden(X3,sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_928])])).

fof(f4930,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X3,sK3(k5_partfun1(sK0,sK1,sK2))) )
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f79])).

fof(f5111,plain,
    ( ~ spl5_917
    | ~ spl5_132
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5048,f905,f786,f5071])).

fof(f5071,plain,
    ( spl5_917
  <=> ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_917])])).

fof(f786,plain,
    ( spl5_132
  <=> ! [X3] :
        ( r1_tarski(X3,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK4(X3,k2_zfmisc_1(sK0,sK1)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f5048,plain,
    ( ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl5_132
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f787])).

fof(f787,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK4(X3,k2_zfmisc_1(sK0,sK1)),sK2)
        | r1_tarski(X3,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f786])).

fof(f906,plain,
    ( ~ r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_149 ),
    inference(avatar_component_clause,[],[f905])).

fof(f5110,plain,
    ( spl5_926
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5049,f905,f5108])).

fof(f5108,plain,
    ( spl5_926
  <=> r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_926])])).

fof(f5049,plain,
    ( r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f66])).

fof(f5103,plain,
    ( ~ spl5_919
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5050,f905,f5078])).

fof(f5078,plain,
    ( spl5_919
  <=> ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_919])])).

fof(f5050,plain,
    ( ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f67])).

fof(f5102,plain,
    ( ~ spl5_85
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5051,f905,f497])).

fof(f497,plain,
    ( spl5_85
  <=> ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f5051,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f68])).

fof(f5101,plain,
    ( spl5_924
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5052,f905,f5099])).

fof(f5099,plain,
    ( spl5_924
  <=> m1_subset_1(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_924])])).

fof(f5052,plain,
    ( m1_subset_1(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f146])).

fof(f5094,plain,
    ( ~ spl5_923
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5053,f905,f5092])).

fof(f5092,plain,
    ( spl5_923
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_923])])).

fof(f5053,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f906,f147])).

fof(f5087,plain,
    ( ~ spl5_921
    | spl5_21
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5055,f905,f182,f5085])).

fof(f5085,plain,
    ( spl5_921
  <=> ~ m1_subset_1(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_921])])).

fof(f5055,plain,
    ( ~ m1_subset_1(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f183,f906,f158])).

fof(f5080,plain,
    ( ~ spl5_919
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5056,f905,f5078])).

fof(f5056,plain,
    ( ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f159,f906,f170])).

fof(f5073,plain,
    ( ~ spl5_917
    | ~ spl5_10
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5057,f905,f128,f5071])).

fof(f5057,plain,
    ( ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl5_10
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f129,f906,f170])).

fof(f5066,plain,
    ( ~ spl5_915
    | spl5_149 ),
    inference(avatar_split_clause,[],[f5058,f905,f5064])).

fof(f5064,plain,
    ( spl5_915
  <=> ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_915])])).

fof(f5058,plain,
    ( ~ r2_hidden(sK4(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1)),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_149 ),
    inference(unit_resulting_resolution,[],[f121,f906,f170])).

fof(f5047,plain,
    ( spl5_136
    | spl5_912
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f5042,f786,f5045,f819])).

fof(f819,plain,
    ( spl5_136
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f5045,plain,
    ( spl5_912
  <=> ! [X2] :
        ( r1_tarski(X2,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK4(X2,k2_zfmisc_1(sK0,sK1)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_912])])).

fof(f5042,plain,
    ( ! [X2] :
        ( r1_tarski(X2,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK4(X2,k2_zfmisc_1(sK0,sK1)),sK2) )
    | ~ spl5_132 ),
    inference(resolution,[],[f787,f63])).

fof(f5030,plain,
    ( ~ spl5_909
    | spl5_910
    | spl5_71 ),
    inference(avatar_split_clause,[],[f5010,f433,f5028,f5022])).

fof(f5022,plain,
    ( spl5_909
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_909])])).

fof(f5028,plain,
    ( spl5_910
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_910])])).

fof(f5010,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))
    | ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))
    | ~ spl5_71 ),
    inference(resolution,[],[f434,f63])).

fof(f5017,plain,
    ( ~ spl5_907
    | spl5_71 ),
    inference(avatar_split_clause,[],[f5008,f433,f5015])).

fof(f5015,plain,
    ( spl5_907
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_907])])).

fof(f5008,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))))
    | ~ spl5_71 ),
    inference(unit_resulting_resolution,[],[f121,f434,f65])).

fof(f5006,plain,
    ( spl5_884
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4931,f1065,f4936])).

fof(f4936,plain,
    ( spl5_884
  <=> r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_884])])).

fof(f4931,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f68])).

fof(f5005,plain,
    ( ~ spl5_151
    | ~ spl5_167
    | spl5_904
    | spl5_36
    | ~ spl5_8
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4998,f1065,f115,f263,f5003,f1025,f914])).

fof(f1025,plain,
    ( spl5_167
  <=> ~ v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f5003,plain,
    ( spl5_904
  <=> r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_904])])).

fof(f4998,plain,
    ( o_0_0_xboole_0 = sK1
    | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1)
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_8
    | ~ spl5_172 ),
    inference(forward_demodulation,[],[f4927,f116])).

fof(f4927,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k1_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1)
    | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f73])).

fof(f4997,plain,
    ( spl5_898
    | ~ spl5_151
    | spl5_902
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4925,f1065,f4995,f914,f4988])).

fof(f4988,plain,
    ( spl5_898
  <=> v1_xboole_0(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_898])])).

fof(f4995,plain,
    ( spl5_902
  <=> ! [X1] :
        ( v1_funct_1(X1)
        | ~ m1_subset_1(X1,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_902])])).

fof(f4925,plain,
    ( ! [X1] :
        ( v1_funct_1(X1)
        | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
        | v1_xboole_0(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
        | ~ m1_subset_1(X1,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) )
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f205])).

fof(f4993,plain,
    ( spl5_898
    | ~ spl5_151
    | spl5_900
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4924,f1065,f4991,f914,f4988])).

fof(f4991,plain,
    ( spl5_900
  <=> ! [X0] :
        ( v1_funct_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_900])])).

fof(f4924,plain,
    ( ! [X0] :
        ( v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
        | v1_xboole_0(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
        | ~ m1_subset_1(X0,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) )
    | ~ spl5_172 ),
    inference(resolution,[],[f1066,f241])).

fof(f4983,plain,
    ( ~ spl5_897
    | ~ spl5_150
    | ~ spl5_172
    | spl5_263 ),
    inference(avatar_split_clause,[],[f4914,f1625,f1065,f917,f4978])).

fof(f4978,plain,
    ( spl5_897
  <=> ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_897])])).

fof(f4914,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f1626,f918,f1066,f75])).

fof(f4982,plain,
    ( ~ spl5_893
    | spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4915,f1065,f917,f251,f4964])).

fof(f4964,plain,
    ( spl5_893
  <=> ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_893])])).

fof(f4915,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(unit_resulting_resolution,[],[f252,f918,f1066,f76])).

fof(f4981,plain,
    ( ~ spl5_889
    | ~ spl5_150
    | ~ spl5_172
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4916,f1381,f1065,f917,f4950])).

fof(f4950,plain,
    ( spl5_889
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_889])])).

fof(f4916,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f918,f1066,f77])).

fof(f4980,plain,
    ( ~ spl5_897
    | ~ spl5_150
    | ~ spl5_172
    | spl5_263 ),
    inference(avatar_split_clause,[],[f4917,f1625,f1065,f917,f4978])).

fof(f4917,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f1626,f918,f159,f1066,f204])).

fof(f4973,plain,
    ( ~ spl5_895
    | ~ spl5_150
    | ~ spl5_172
    | spl5_263 ),
    inference(avatar_split_clause,[],[f4918,f1625,f1065,f917,f4971])).

fof(f4971,plain,
    ( spl5_895
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_895])])).

fof(f4918,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f1626,f918,f121,f1066,f204])).

fof(f4966,plain,
    ( ~ spl5_893
    | spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4919,f1065,f917,f251,f4964])).

fof(f4919,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(unit_resulting_resolution,[],[f252,f918,f159,f1066,f240])).

fof(f4959,plain,
    ( ~ spl5_891
    | spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4920,f1065,f917,f251,f4957])).

fof(f4957,plain,
    ( spl5_891
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_891])])).

fof(f4920,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))))
    | ~ spl5_33
    | ~ spl5_150
    | ~ spl5_172 ),
    inference(unit_resulting_resolution,[],[f252,f918,f121,f1066,f240])).

fof(f4952,plain,
    ( ~ spl5_889
    | ~ spl5_150
    | ~ spl5_172
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4921,f1381,f1065,f917,f4950])).

fof(f4921,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f918,f159,f1066,f268])).

fof(f268,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k5_partfun1(X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X0,X4)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f77,f65])).

fof(f4945,plain,
    ( ~ spl5_887
    | ~ spl5_150
    | ~ spl5_172
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4922,f1381,f1065,f917,f4943])).

fof(f4943,plain,
    ( spl5_887
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_887])])).

fof(f4922,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3(k5_partfun1(sK0,sK1,sK2))))))
    | ~ spl5_150
    | ~ spl5_172
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f918,f121,f1066,f268])).

fof(f4938,plain,
    ( spl5_884
    | ~ spl5_172 ),
    inference(avatar_split_clause,[],[f4923,f1065,f4936])).

fof(f4923,plain,
    ( r1_tarski(sK3(k5_partfun1(sK0,sK1,sK2)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_172 ),
    inference(unit_resulting_resolution,[],[f1066,f68])).

fof(f4905,plain,
    ( spl5_882
    | spl5_427 ),
    inference(avatar_split_clause,[],[f4876,f2568,f4903])).

fof(f4903,plain,
    ( spl5_882
  <=> r2_hidden(sK4(sK2,o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_882])])).

fof(f2568,plain,
    ( spl5_427
  <=> ~ r1_tarski(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_427])])).

fof(f4876,plain,
    ( r2_hidden(sK4(sK2,o_0_0_xboole_0),sK2)
    | ~ spl5_427 ),
    inference(unit_resulting_resolution,[],[f2569,f66])).

fof(f2569,plain,
    ( ~ r1_tarski(sK2,o_0_0_xboole_0)
    | ~ spl5_427 ),
    inference(avatar_component_clause,[],[f2568])).

fof(f4898,plain,
    ( spl5_880
    | spl5_427 ),
    inference(avatar_split_clause,[],[f4879,f2568,f4896])).

fof(f4896,plain,
    ( spl5_880
  <=> m1_subset_1(sK4(sK2,o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_880])])).

fof(f4879,plain,
    ( m1_subset_1(sK4(sK2,o_0_0_xboole_0),sK2)
    | ~ spl5_427 ),
    inference(unit_resulting_resolution,[],[f2569,f146])).

fof(f4891,plain,
    ( ~ spl5_879
    | spl5_427 ),
    inference(avatar_split_clause,[],[f4880,f2568,f4889])).

fof(f4889,plain,
    ( spl5_879
  <=> ~ r2_hidden(sK2,sK4(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_879])])).

fof(f4880,plain,
    ( ~ r2_hidden(sK2,sK4(sK2,o_0_0_xboole_0))
    | ~ spl5_427 ),
    inference(unit_resulting_resolution,[],[f2569,f147])).

fof(f4862,plain,
    ( ~ spl5_155
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2815,f826,f953])).

fof(f953,plain,
    ( spl5_155
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f2815,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f827,f68])).

fof(f4861,plain,
    ( spl5_874
    | ~ spl5_877
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f4813,f347,f4859,f4853])).

fof(f4853,plain,
    ( spl5_874
  <=> v1_xboole_0(sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_874])])).

fof(f4859,plain,
    ( spl5_877
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_877])])).

fof(f4813,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK3(k5_partfun1(sK0,sK1,sK2)))
    | v1_xboole_0(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_52 ),
    inference(resolution,[],[f348,f143])).

fof(f4848,plain,
    ( spl5_872
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f4785,f823,f347,f4846])).

fof(f4846,plain,
    ( spl5_872
  <=> r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_872])])).

fof(f823,plain,
    ( spl5_138
  <=> r1_tarski(k5_partfun1(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f4785,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),sK2)
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f824,f348,f65])).

fof(f824,plain,
    ( r1_tarski(k5_partfun1(sK0,sK1,sK2),sK2)
    | ~ spl5_138 ),
    inference(avatar_component_clause,[],[f823])).

fof(f4839,plain,
    ( spl5_870
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f4793,f823,f347,f4837])).

fof(f4837,plain,
    ( spl5_870
  <=> m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_870])])).

fof(f4793,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2)),sK2)
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f824,f348,f167])).

fof(f4832,plain,
    ( ~ spl5_869
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f4795,f823,f347,f4830])).

fof(f4830,plain,
    ( spl5_869
  <=> ~ r2_hidden(sK2,sK3(k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_869])])).

fof(f4795,plain,
    ( ~ r2_hidden(sK2,sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_52
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f824,f348,f168])).

fof(f168,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,X3)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f65,f61])).

fof(f4825,plain,
    ( ~ spl5_867
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f4798,f347,f4823])).

fof(f4823,plain,
    ( spl5_867
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK3(k5_partfun1(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_867])])).

fof(f4798,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK3(k5_partfun1(sK0,sK1,sK2)))))
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f121,f348,f168])).

fof(f4778,plain,
    ( spl5_864
    | spl5_227 ),
    inference(avatar_split_clause,[],[f4748,f1408,f4776])).

fof(f4771,plain,
    ( spl5_862
    | ~ spl5_6
    | spl5_227 ),
    inference(avatar_split_clause,[],[f4749,f1408,f106,f4766])).

fof(f4770,plain,
    ( spl5_862
    | ~ spl5_24
    | spl5_227
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4769,f2490,f1408,f198,f4766])).

fof(f4768,plain,
    ( spl5_862
    | ~ spl5_54
    | spl5_227
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4761,f3100,f1408,f354,f4766])).

fof(f4760,plain,
    ( ~ spl5_861
    | spl5_227 ),
    inference(avatar_split_clause,[],[f4752,f1408,f4758])).

fof(f4758,plain,
    ( spl5_861
  <=> ~ r2_hidden(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_861])])).

fof(f4752,plain,
    ( ~ r2_hidden(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f60,f1409,f143])).

fof(f4747,plain,
    ( ~ spl5_859
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4697,f1381,f223,f99,f92,f4745])).

fof(f4745,plain,
    ( spl5_859
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_859])])).

fof(f4697,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f100,f224,f93,f1382,f269])).

fof(f269,plain,(
    ! [X6,X8,X7,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X8)
      | v1_xboole_0(k5_partfun1(X6,X7,X8))
      | ~ m1_subset_1(X5,k5_partfun1(X6,X7,X8)) ) ),
    inference(resolution,[],[f77,f63])).

fof(f4740,plain,
    ( ~ spl5_855
    | ~ spl5_2
    | ~ spl5_4
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4698,f1381,f99,f92,f4730])).

fof(f4730,plain,
    ( spl5_855
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_855])])).

fof(f4698,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f100,f159,f93,f1382,f268])).

fof(f4739,plain,
    ( ~ spl5_857
    | ~ spl5_2
    | ~ spl5_4
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4699,f1381,f99,f92,f4737])).

fof(f4737,plain,
    ( spl5_857
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_857])])).

fof(f4699,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f100,f121,f93,f1382,f268])).

fof(f4732,plain,
    ( ~ spl5_855
    | ~ spl5_2
    | ~ spl5_4
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4700,f1381,f99,f92,f4730])).

fof(f4700,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f100,f93,f1382,f77])).

fof(f4725,plain,
    ( ~ spl5_851
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4702,f1381,f4713])).

fof(f4713,plain,
    ( spl5_851
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_851])])).

fof(f4702,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f159,f1382,f167])).

fof(f4724,plain,
    ( ~ spl5_853
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4703,f1381,f4720])).

fof(f4720,plain,
    ( spl5_853
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_853])])).

fof(f4703,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f121,f1382,f167])).

fof(f4723,plain,
    ( ~ spl5_853
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4704,f1381,f4720])).

fof(f4704,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f202])).

fof(f4722,plain,
    ( ~ spl5_853
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4705,f1381,f4720])).

fof(f4705,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK3(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f60,f1382,f78])).

fof(f4715,plain,
    ( ~ spl5_851
    | spl5_219 ),
    inference(avatar_split_clause,[],[f4706,f1381,f4713])).

fof(f4706,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1382,f62])).

fof(f4696,plain,
    ( spl5_848
    | spl5_113 ),
    inference(avatar_split_clause,[],[f4666,f654,f4694])).

fof(f4694,plain,
    ( spl5_848
  <=> r2_hidden(sK3(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_848])])).

fof(f4666,plain,
    ( r2_hidden(sK3(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f60,f655,f63])).

fof(f4689,plain,
    ( spl5_846
    | ~ spl5_6
    | spl5_113 ),
    inference(avatar_split_clause,[],[f4667,f654,f106,f4684])).

fof(f4684,plain,
    ( spl5_846
  <=> v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_846])])).

fof(f4667,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f107,f655,f64])).

fof(f4688,plain,
    ( spl5_846
    | ~ spl5_24
    | spl5_113
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4687,f2490,f654,f198,f4684])).

fof(f4687,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_113
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4668,f2491])).

fof(f4668,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f199,f655,f64])).

fof(f4686,plain,
    ( spl5_846
    | ~ spl5_54
    | spl5_113
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4679,f3100,f654,f354,f4684])).

fof(f4679,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_113
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4669,f3101])).

fof(f4669,plain,
    ( v1_xboole_0(k1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f355,f655,f64])).

fof(f4678,plain,
    ( ~ spl5_845
    | spl5_113 ),
    inference(avatar_split_clause,[],[f4671,f654,f4676])).

fof(f4676,plain,
    ( spl5_845
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK3(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_845])])).

fof(f4671,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK3(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))))
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f60,f655,f143])).

fof(f4661,plain,
    ( spl5_842
    | spl5_63 ),
    inference(avatar_split_clause,[],[f4631,f390,f4659])).

fof(f4659,plain,
    ( spl5_842
  <=> r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_842])])).

fof(f4631,plain,
    ( r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f60,f391,f63])).

fof(f4654,plain,
    ( spl5_840
    | ~ spl5_6
    | spl5_63 ),
    inference(avatar_split_clause,[],[f4632,f390,f106,f4649])).

fof(f4649,plain,
    ( spl5_840
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_840])])).

fof(f4632,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f107,f391,f64])).

fof(f4653,plain,
    ( spl5_840
    | ~ spl5_24
    | spl5_63
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4652,f2490,f390,f198,f4649])).

fof(f4652,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_63
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4633,f2491])).

fof(f4651,plain,
    ( spl5_840
    | ~ spl5_54
    | spl5_63
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4644,f3100,f390,f354,f4649])).

fof(f4644,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_63
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4634,f3101])).

fof(f4634,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f355,f391,f64])).

fof(f4643,plain,
    ( ~ spl5_839
    | spl5_63 ),
    inference(avatar_split_clause,[],[f4635,f390,f4641])).

fof(f4641,plain,
    ( spl5_839
  <=> ~ r2_hidden(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_839])])).

fof(f4635,plain,
    ( ~ r2_hidden(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f60,f391,f143])).

fof(f4629,plain,
    ( spl5_836
    | spl5_237 ),
    inference(avatar_split_clause,[],[f4598,f1500,f4627])).

fof(f4622,plain,
    ( spl5_834
    | ~ spl5_6
    | spl5_237 ),
    inference(avatar_split_clause,[],[f4600,f1500,f106,f4617])).

fof(f4621,plain,
    ( spl5_834
    | ~ spl5_24
    | spl5_237
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4620,f2490,f1500,f198,f4617])).

fof(f4619,plain,
    ( spl5_834
    | ~ spl5_54
    | spl5_237
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4612,f3100,f1500,f354,f4617])).

fof(f4611,plain,
    ( ~ spl5_833
    | spl5_237 ),
    inference(avatar_split_clause,[],[f4604,f1500,f4609])).

fof(f4609,plain,
    ( spl5_833
  <=> ~ r2_hidden(sK3(sK1),sK3(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_833])])).

fof(f4604,plain,
    ( ~ r2_hidden(sK3(sK1),sK3(sK3(sK1)))
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f60,f1501,f143])).

fof(f4597,plain,
    ( spl5_806
    | ~ spl5_8
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4596,f393,f115,f4501])).

fof(f4501,plain,
    ( spl5_806
  <=> k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_806])])).

fof(f393,plain,
    ( spl5_62
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f4596,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f4403,f116])).

fof(f4403,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = k1_xboole_0
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f394,f59])).

fof(f394,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f393])).

fof(f4595,plain,
    ( spl5_830
    | spl5_21
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4404,f393,f182,f4593])).

fof(f4593,plain,
    ( spl5_830
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_830])])).

fof(f4404,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_21
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f183,f394,f64])).

fof(f4588,plain,
    ( spl5_828
    | spl5_31
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4405,f393,f223,f4586])).

fof(f4586,plain,
    ( spl5_828
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_828])])).

fof(f4405,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_31
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f224,f394,f64])).

fof(f4581,plain,
    ( spl5_826
    | spl5_45
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4406,f393,f304,f4579])).

fof(f4579,plain,
    ( spl5_826
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_826])])).

fof(f4406,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_45
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f305,f394,f64])).

fof(f4574,plain,
    ( spl5_824
    | ~ spl5_62
    | spl5_201 ),
    inference(avatar_split_clause,[],[f4407,f1240,f393,f4572])).

fof(f4572,plain,
    ( spl5_824
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_824])])).

fof(f4407,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_62
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f394,f64])).

fof(f4567,plain,
    ( spl5_822
    | ~ spl5_62
    | spl5_67 ),
    inference(avatar_split_clause,[],[f4408,f410,f393,f4565])).

fof(f4565,plain,
    ( spl5_822
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_822])])).

fof(f4408,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f394,f64])).

fof(f4560,plain,
    ( spl5_820
    | ~ spl5_62
    | spl5_225 ),
    inference(avatar_split_clause,[],[f4409,f1400,f393,f4558])).

fof(f4558,plain,
    ( spl5_820
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_820])])).

fof(f4409,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_62
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f1401,f394,f64])).

fof(f4553,plain,
    ( spl5_818
    | spl5_61
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4410,f393,f383,f4551])).

fof(f4551,plain,
    ( spl5_818
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_818])])).

fof(f4410,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_61
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f384,f394,f64])).

fof(f4546,plain,
    ( spl5_816
    | ~ spl5_62
    | spl5_223 ),
    inference(avatar_split_clause,[],[f4411,f1393,f393,f4544])).

fof(f4544,plain,
    ( spl5_816
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_816])])).

fof(f4411,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_62
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f1394,f394,f64])).

fof(f4539,plain,
    ( spl5_814
    | spl5_59
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4412,f393,f376,f4537])).

fof(f4537,plain,
    ( spl5_814
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_814])])).

fof(f4412,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_59
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f377,f394,f64])).

fof(f4532,plain,
    ( spl5_812
    | spl5_27
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4413,f393,f211,f4530])).

fof(f4530,plain,
    ( spl5_812
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_812])])).

fof(f4413,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_27
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f212,f394,f64])).

fof(f212,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f211])).

fof(f4525,plain,
    ( spl5_810
    | spl5_29
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4414,f393,f220,f4523])).

fof(f4523,plain,
    ( spl5_810
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_810])])).

fof(f4414,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_29
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f221,f394,f64])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f220])).

fof(f4518,plain,
    ( spl5_808
    | ~ spl5_62
    | spl5_137 ),
    inference(avatar_split_clause,[],[f4415,f816,f393,f4516])).

fof(f4516,plain,
    ( spl5_808
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_808])])).

fof(f4415,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_62
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f394,f64])).

fof(f4511,plain,
    ( spl5_806
    | ~ spl5_6
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4416,f393,f106,f4501])).

fof(f4416,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f107,f394,f70])).

fof(f4510,plain,
    ( spl5_806
    | ~ spl5_24
    | ~ spl5_62
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4509,f2490,f393,f198,f4501])).

fof(f4509,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_62
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4417,f2491])).

fof(f4417,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f199,f394,f70])).

fof(f4508,plain,
    ( spl5_806
    | ~ spl5_54
    | ~ spl5_62
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4507,f3100,f393,f354,f4501])).

fof(f4507,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_62
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4418,f3101])).

fof(f4418,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f355,f394,f70])).

fof(f4506,plain,
    ( spl5_806
    | ~ spl5_6
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4420,f393,f106,f4501])).

fof(f4420,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f107,f394,f70])).

fof(f4505,plain,
    ( spl5_806
    | ~ spl5_24
    | ~ spl5_62
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4504,f2490,f393,f198,f4501])).

fof(f4504,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_62
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4421,f2491])).

fof(f4421,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f199,f394,f70])).

fof(f4503,plain,
    ( spl5_806
    | ~ spl5_54
    | ~ spl5_62
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4496,f3100,f393,f354,f4501])).

fof(f4496,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_62
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4422,f3101])).

fof(f4422,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f355,f394,f70])).

fof(f4495,plain,
    ( ~ spl5_805
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4425,f393,f153,f4493])).

fof(f4493,plain,
    ( spl5_805
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_805])])).

fof(f4425,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f154,f394,f79])).

fof(f4488,plain,
    ( ~ spl5_803
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4426,f393,f320,f4486])).

fof(f4486,plain,
    ( spl5_803
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_803])])).

fof(f320,plain,
    ( spl5_46
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f4426,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f321,f394,f79])).

fof(f321,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f320])).

fof(f4481,plain,
    ( ~ spl5_801
    | ~ spl5_38
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4427,f393,f277,f4479])).

fof(f4479,plain,
    ( spl5_801
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_801])])).

fof(f277,plain,
    ( spl5_38
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f4427,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_38
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f278,f394,f79])).

fof(f278,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f277])).

fof(f4474,plain,
    ( ~ spl5_799
    | ~ spl5_22
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4428,f393,f191,f4472])).

fof(f4472,plain,
    ( spl5_799
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_799])])).

fof(f4428,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_22
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f192,f394,f79])).

fof(f4467,plain,
    ( ~ spl5_791
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4431,f393,f153,f4443])).

fof(f4443,plain,
    ( spl5_791
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_791])])).

fof(f4431,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f154,f394,f169])).

fof(f4466,plain,
    ( ~ spl5_797
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4432,f393,f320,f4464])).

fof(f4464,plain,
    ( spl5_797
  <=> ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_797])])).

fof(f4432,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_46
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f321,f394,f169])).

fof(f4459,plain,
    ( ~ spl5_795
    | ~ spl5_38
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4433,f393,f277,f4457])).

fof(f4457,plain,
    ( spl5_795
  <=> ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_795])])).

fof(f4433,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_38
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f278,f394,f169])).

fof(f4452,plain,
    ( ~ spl5_793
    | ~ spl5_22
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4434,f393,f191,f4450])).

fof(f4450,plain,
    ( spl5_793
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_793])])).

fof(f4434,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_22
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f192,f394,f169])).

fof(f4445,plain,
    ( ~ spl5_791
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f4438,f393,f153,f4443])).

fof(f4438,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f394,f703])).

fof(f4402,plain,
    ( ~ spl5_783
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4344,f1372,f4377])).

fof(f4377,plain,
    ( spl5_783
  <=> ~ v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_783])])).

fof(f4344,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_217 ),
    inference(resolution,[],[f1373,f148])).

fof(f4401,plain,
    ( spl5_788
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4334,f1372,f4399])).

fof(f4399,plain,
    ( spl5_788
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k5_partfun1(sK0,sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_788])])).

fof(f4334,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f1373,f66])).

fof(f4394,plain,
    ( ~ spl5_779
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4335,f1372,f4363])).

fof(f4363,plain,
    ( spl5_779
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_779])])).

fof(f4335,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f1373,f67])).

fof(f4393,plain,
    ( spl5_786
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4337,f1372,f4391])).

fof(f4391,plain,
    ( spl5_786
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k5_partfun1(sK0,sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_786])])).

fof(f4337,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f1373,f146])).

fof(f4386,plain,
    ( ~ spl5_785
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4338,f1372,f4384])).

fof(f4384,plain,
    ( spl5_785
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_785])])).

fof(f4338,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,o_0_0_xboole_0),sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f1373,f147])).

fof(f4379,plain,
    ( ~ spl5_783
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4339,f1372,f4377])).

fof(f4339,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,o_0_0_xboole_0))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f1373,f148])).

fof(f4372,plain,
    ( ~ spl5_781
    | spl5_21
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4340,f1372,f182,f4370])).

fof(f4370,plain,
    ( spl5_781
  <=> ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_781])])).

fof(f4340,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_21
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f183,f1373,f158])).

fof(f4365,plain,
    ( ~ spl5_779
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4341,f1372,f4363])).

fof(f4341,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f159,f1373,f170])).

fof(f4358,plain,
    ( ~ spl5_777
    | ~ spl5_10
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4342,f1372,f128,f4356])).

fof(f4356,plain,
    ( spl5_777
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_777])])).

fof(f4342,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl5_10
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f129,f1373,f170])).

fof(f4351,plain,
    ( ~ spl5_775
    | spl5_217 ),
    inference(avatar_split_clause,[],[f4343,f1372,f4349])).

fof(f4349,plain,
    ( spl5_775
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_775])])).

fof(f4343,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)),sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_217 ),
    inference(unit_resulting_resolution,[],[f121,f1373,f170])).

fof(f4333,plain,
    ( ~ spl5_771
    | spl5_772
    | spl5_165 ),
    inference(avatar_split_clause,[],[f4313,f1008,f4331,f4325])).

fof(f4325,plain,
    ( spl5_771
  <=> ~ m1_subset_1(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_771])])).

fof(f4331,plain,
    ( spl5_772
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_772])])).

fof(f4313,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ m1_subset_1(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_165 ),
    inference(resolution,[],[f1009,f63])).

fof(f4320,plain,
    ( ~ spl5_769
    | spl5_165 ),
    inference(avatar_split_clause,[],[f4311,f1008,f4318])).

fof(f4318,plain,
    ( spl5_769
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_769])])).

fof(f4311,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))))
    | ~ spl5_165 ),
    inference(unit_resulting_resolution,[],[f121,f1009,f65])).

fof(f4291,plain,
    ( spl5_766
    | ~ spl5_2
    | ~ spl5_4
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4231,f612,f99,f92,f4289])).

fof(f4289,plain,
    ( spl5_766
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_766])])).

fof(f4231,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f100,f93,f613,f270])).

fof(f4284,plain,
    ( spl5_764
    | ~ spl5_2
    | ~ spl5_4
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4232,f612,f99,f92,f4282])).

fof(f4282,plain,
    ( spl5_764
  <=> v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_764])])).

fof(f4232,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f100,f93,f613,f242])).

fof(f242,plain,(
    ! [X12,X10,X11,X9] :
      ( v1_funct_2(sK4(k5_partfun1(X9,X10,X11),X12),X9,X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11)
      | r1_tarski(k5_partfun1(X9,X10,X11),X12) ) ),
    inference(resolution,[],[f76,f66])).

fof(f4277,plain,
    ( spl5_762
    | ~ spl5_2
    | ~ spl5_4
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4233,f612,f99,f92,f4275])).

fof(f4275,plain,
    ( spl5_762
  <=> v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_762])])).

fof(f4233,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f100,f93,f613,f206])).

fof(f206,plain,(
    ! [X12,X10,X11,X9] :
      ( v1_funct_1(sK4(k5_partfun1(X9,X10,X11),X12))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11)
      | r1_tarski(k5_partfun1(X9,X10,X11),X12) ) ),
    inference(resolution,[],[f75,f66])).

fof(f4270,plain,
    ( spl5_760
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4234,f612,f4268])).

fof(f4268,plain,
    ( spl5_760
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_760])])).

fof(f4234,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f613,f66])).

fof(f4263,plain,
    ( ~ spl5_759
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4236,f612,f4261])).

fof(f4261,plain,
    ( spl5_759
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK3(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_759])])).

fof(f4236,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK3(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f613,f68])).

fof(f4256,plain,
    ( spl5_756
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4237,f612,f4254])).

fof(f4254,plain,
    ( spl5_756
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_756])])).

fof(f4237,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f613,f146])).

fof(f4249,plain,
    ( ~ spl5_755
    | spl5_103 ),
    inference(avatar_split_clause,[],[f4238,f612,f4247])).

fof(f4247,plain,
    ( spl5_755
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_755])])).

fof(f4238,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_103 ),
    inference(unit_resulting_resolution,[],[f613,f147])).

fof(f4230,plain,
    ( spl5_752
    | spl5_229 ),
    inference(avatar_split_clause,[],[f4201,f1474,f4228])).

fof(f4228,plain,
    ( spl5_752
  <=> r2_hidden(sK4(sK1,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_752])])).

fof(f1474,plain,
    ( spl5_229
  <=> ~ r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_229])])).

fof(f4201,plain,
    ( r2_hidden(sK4(sK1,o_0_0_xboole_0),sK1)
    | ~ spl5_229 ),
    inference(unit_resulting_resolution,[],[f1475,f66])).

fof(f1475,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_229 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f4223,plain,
    ( spl5_750
    | spl5_229 ),
    inference(avatar_split_clause,[],[f4204,f1474,f4221])).

fof(f4221,plain,
    ( spl5_750
  <=> m1_subset_1(sK4(sK1,o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_750])])).

fof(f4204,plain,
    ( m1_subset_1(sK4(sK1,o_0_0_xboole_0),sK1)
    | ~ spl5_229 ),
    inference(unit_resulting_resolution,[],[f1475,f146])).

fof(f4216,plain,
    ( ~ spl5_749
    | spl5_229 ),
    inference(avatar_split_clause,[],[f4205,f1474,f4214])).

fof(f4214,plain,
    ( spl5_749
  <=> ~ r2_hidden(sK1,sK4(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_749])])).

fof(f4205,plain,
    ( ~ r2_hidden(sK1,sK4(sK1,o_0_0_xboole_0))
    | ~ spl5_229 ),
    inference(unit_resulting_resolution,[],[f1475,f147])).

fof(f4195,plain,
    ( spl5_744
    | ~ spl5_747
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4142,f191,f4193,f4187])).

fof(f4187,plain,
    ( spl5_744
  <=> v1_xboole_0(sK3(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_744])])).

fof(f4193,plain,
    ( spl5_747
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),sK3(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_747])])).

fof(f4142,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),sK3(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK3(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_22 ),
    inference(resolution,[],[f192,f143])).

fof(f4182,plain,
    ( ~ spl5_737
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4125,f191,f106,f4151])).

fof(f4181,plain,
    ( ~ spl5_743
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4126,f191,f106,f4179])).

fof(f4179,plain,
    ( spl5_743
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_743])])).

fof(f4126,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f171,f192,f65])).

fof(f171,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f107,f60,f79])).

fof(f4174,plain,
    ( ~ spl5_741
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4128,f191,f106,f4169])).

fof(f4173,plain,
    ( ~ spl5_741
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4172,f2490,f198,f191,f4169])).

fof(f4171,plain,
    ( ~ spl5_741
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4164,f3100,f354,f191,f4169])).

fof(f4163,plain,
    ( ~ spl5_739
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4134,f191,f4161])).

fof(f4161,plain,
    ( spl5_739
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(k1_zfmisc_1(sK3(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_739])])).

fof(f4134,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(k1_zfmisc_1(sK3(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f121,f192,f168])).

fof(f4156,plain,
    ( ~ spl5_737
    | ~ spl5_6
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f4135,f191,f106,f4151])).

fof(f4155,plain,
    ( ~ spl5_737
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4154,f2490,f198,f191,f4151])).

fof(f4153,plain,
    ( ~ spl5_737
    | ~ spl5_22
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4146,f3100,f354,f191,f4151])).

fof(f4120,plain,
    ( ~ spl5_733
    | spl5_734
    | spl5_91 ),
    inference(avatar_split_clause,[],[f4100,f546,f4118,f4112])).

fof(f4112,plain,
    ( spl5_733
  <=> ~ m1_subset_1(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_733])])).

fof(f4118,plain,
    ( spl5_734
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_734])])).

fof(f4100,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))
    | ~ m1_subset_1(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))
    | ~ spl5_91 ),
    inference(resolution,[],[f547,f63])).

fof(f4107,plain,
    ( ~ spl5_731
    | spl5_91 ),
    inference(avatar_split_clause,[],[f4098,f546,f4105])).

fof(f4105,plain,
    ( spl5_731
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_731])])).

fof(f4098,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))))
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f121,f547,f65])).

fof(f4096,plain,
    ( ~ spl5_727
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4074,f464,f4084])).

fof(f4084,plain,
    ( spl5_727
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_727])])).

fof(f4074,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f159,f465,f167])).

fof(f4095,plain,
    ( ~ spl5_729
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4075,f464,f4091])).

fof(f4091,plain,
    ( spl5_729
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_729])])).

fof(f4075,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f121,f465,f167])).

fof(f4094,plain,
    ( ~ spl5_729
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4076,f464,f4091])).

fof(f4076,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f465,f202])).

fof(f4093,plain,
    ( ~ spl5_729
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4077,f464,f4091])).

fof(f4077,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f60,f465,f78])).

fof(f4086,plain,
    ( ~ spl5_727
    | spl5_75 ),
    inference(avatar_split_clause,[],[f4078,f464,f4084])).

fof(f4078,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f465,f62])).

fof(f4072,plain,
    ( spl5_724
    | spl5_61 ),
    inference(avatar_split_clause,[],[f4042,f383,f4070])).

fof(f4070,plain,
    ( spl5_724
  <=> r2_hidden(sK3(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_724])])).

fof(f4042,plain,
    ( r2_hidden(sK3(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f60,f384,f63])).

fof(f4065,plain,
    ( spl5_722
    | ~ spl5_6
    | spl5_61 ),
    inference(avatar_split_clause,[],[f4043,f383,f106,f4060])).

fof(f4060,plain,
    ( spl5_722
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_722])])).

fof(f4043,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f107,f384,f64])).

fof(f4064,plain,
    ( spl5_722
    | ~ spl5_24
    | spl5_61
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f4063,f2490,f383,f198,f4060])).

fof(f4063,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_61
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f4044,f2491])).

fof(f4062,plain,
    ( spl5_722
    | ~ spl5_54
    | spl5_61
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f4055,f3100,f383,f354,f4060])).

fof(f4055,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_61
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f4045,f3101])).

fof(f4045,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f355,f384,f64])).

fof(f4054,plain,
    ( ~ spl5_721
    | spl5_61 ),
    inference(avatar_split_clause,[],[f4046,f383,f4052])).

fof(f4052,plain,
    ( spl5_721
  <=> ~ r2_hidden(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_721])])).

fof(f4046,plain,
    ( ~ r2_hidden(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f60,f384,f143])).

fof(f4040,plain,
    ( spl5_696
    | ~ spl5_8
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f4039,f386,f115,f3951])).

fof(f3951,plain,
    ( spl5_696
  <=> k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_696])])).

fof(f386,plain,
    ( spl5_60
  <=> v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f4039,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f3872,f116])).

fof(f3872,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = k1_xboole_0
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f387,f59])).

fof(f387,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f386])).

fof(f4038,plain,
    ( spl5_718
    | spl5_21
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3873,f386,f182,f4036])).

fof(f4036,plain,
    ( spl5_718
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_718])])).

fof(f3873,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_21
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f183,f387,f64])).

fof(f4031,plain,
    ( spl5_716
    | spl5_31
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3874,f386,f223,f4029])).

fof(f4029,plain,
    ( spl5_716
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_716])])).

fof(f3874,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_31
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f224,f387,f64])).

fof(f4024,plain,
    ( spl5_714
    | spl5_45
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3875,f386,f304,f4022])).

fof(f4022,plain,
    ( spl5_714
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_714])])).

fof(f3875,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_45
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f305,f387,f64])).

fof(f4017,plain,
    ( spl5_712
    | ~ spl5_60
    | spl5_201 ),
    inference(avatar_split_clause,[],[f3876,f1240,f386,f4015])).

fof(f4015,plain,
    ( spl5_712
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_712])])).

fof(f3876,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_60
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f387,f64])).

fof(f4010,plain,
    ( spl5_710
    | ~ spl5_60
    | spl5_67 ),
    inference(avatar_split_clause,[],[f3877,f410,f386,f4008])).

fof(f4008,plain,
    ( spl5_710
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_710])])).

fof(f3877,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_60
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f387,f64])).

fof(f4003,plain,
    ( spl5_708
    | ~ spl5_60
    | spl5_225 ),
    inference(avatar_split_clause,[],[f3878,f1400,f386,f4001])).

fof(f4001,plain,
    ( spl5_708
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_708])])).

fof(f3878,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_60
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f1401,f387,f64])).

fof(f3996,plain,
    ( spl5_706
    | ~ spl5_60
    | spl5_223 ),
    inference(avatar_split_clause,[],[f3879,f1393,f386,f3994])).

fof(f3994,plain,
    ( spl5_706
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_706])])).

fof(f3879,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_60
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f1394,f387,f64])).

fof(f3989,plain,
    ( spl5_704
    | spl5_59
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3880,f386,f376,f3987])).

fof(f3987,plain,
    ( spl5_704
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_704])])).

fof(f3880,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_59
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f377,f387,f64])).

fof(f3982,plain,
    ( spl5_702
    | spl5_27
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3881,f386,f211,f3980])).

fof(f3980,plain,
    ( spl5_702
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_702])])).

fof(f3881,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_27
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f212,f387,f64])).

fof(f3975,plain,
    ( spl5_700
    | spl5_29
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3882,f386,f220,f3973])).

fof(f3973,plain,
    ( spl5_700
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_700])])).

fof(f3882,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_29
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f221,f387,f64])).

fof(f3968,plain,
    ( spl5_698
    | ~ spl5_60
    | spl5_137 ),
    inference(avatar_split_clause,[],[f3883,f816,f386,f3966])).

fof(f3966,plain,
    ( spl5_698
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_698])])).

fof(f3883,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_60
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f387,f64])).

fof(f3961,plain,
    ( spl5_696
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3884,f386,f106,f3951])).

fof(f3884,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f107,f387,f70])).

fof(f3960,plain,
    ( spl5_696
    | ~ spl5_24
    | ~ spl5_60
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3959,f2490,f386,f198,f3951])).

fof(f3959,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_60
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3885,f2491])).

fof(f3885,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f199,f387,f70])).

fof(f3958,plain,
    ( spl5_696
    | ~ spl5_54
    | ~ spl5_60
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3957,f3100,f386,f354,f3951])).

fof(f3957,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_60
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3886,f3101])).

fof(f3886,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f355,f387,f70])).

fof(f3956,plain,
    ( spl5_696
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3888,f386,f106,f3951])).

fof(f3888,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f107,f387,f70])).

fof(f3955,plain,
    ( spl5_696
    | ~ spl5_24
    | ~ spl5_60
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3954,f2490,f386,f198,f3951])).

fof(f3954,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_60
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3889,f2491])).

fof(f3889,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f199,f387,f70])).

fof(f3953,plain,
    ( spl5_696
    | ~ spl5_54
    | ~ spl5_60
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3946,f3100,f386,f354,f3951])).

fof(f3946,plain,
    ( k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_60
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3890,f3101])).

fof(f3890,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f355,f387,f70])).

fof(f3945,plain,
    ( ~ spl5_695
    | ~ spl5_14
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3893,f386,f153,f3943])).

fof(f3943,plain,
    ( spl5_695
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_695])])).

fof(f3893,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_14
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f154,f387,f79])).

fof(f3938,plain,
    ( ~ spl5_693
    | ~ spl5_46
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3894,f386,f320,f3936])).

fof(f3936,plain,
    ( spl5_693
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_693])])).

fof(f3894,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_46
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f321,f387,f79])).

fof(f3931,plain,
    ( ~ spl5_691
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3895,f386,f277,f3929])).

fof(f3929,plain,
    ( spl5_691
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_691])])).

fof(f3895,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f278,f387,f79])).

fof(f3924,plain,
    ( ~ spl5_689
    | ~ spl5_14
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3898,f386,f153,f3922])).

fof(f3922,plain,
    ( spl5_689
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_689])])).

fof(f3898,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f154,f387,f169])).

fof(f3917,plain,
    ( ~ spl5_687
    | ~ spl5_46
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3899,f386,f320,f3915])).

fof(f3915,plain,
    ( spl5_687
  <=> ~ r1_tarski(sK1,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_687])])).

fof(f3899,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_46
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f321,f387,f169])).

fof(f3910,plain,
    ( ~ spl5_685
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f3900,f386,f277,f3908])).

fof(f3908,plain,
    ( spl5_685
  <=> ~ r1_tarski(sK0,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_685])])).

fof(f3900,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_38
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f278,f387,f169])).

fof(f3871,plain,
    ( spl5_682
    | spl5_59 ),
    inference(avatar_split_clause,[],[f3841,f376,f3869])).

fof(f3869,plain,
    ( spl5_682
  <=> r2_hidden(sK3(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_682])])).

fof(f3841,plain,
    ( r2_hidden(sK3(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f60,f377,f63])).

fof(f3864,plain,
    ( spl5_680
    | ~ spl5_6
    | spl5_59 ),
    inference(avatar_split_clause,[],[f3842,f376,f106,f3859])).

fof(f3859,plain,
    ( spl5_680
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_680])])).

fof(f3842,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f107,f377,f64])).

fof(f3863,plain,
    ( spl5_680
    | ~ spl5_24
    | spl5_59
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3862,f2490,f376,f198,f3859])).

fof(f3862,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_59
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3843,f2491])).

fof(f3861,plain,
    ( spl5_680
    | ~ spl5_54
    | spl5_59
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3854,f3100,f376,f354,f3859])).

fof(f3854,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),o_0_0_xboole_0))
    | ~ spl5_54
    | ~ spl5_59
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3844,f3101])).

fof(f3844,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f355,f377,f64])).

fof(f3853,plain,
    ( ~ spl5_679
    | spl5_59 ),
    inference(avatar_split_clause,[],[f3845,f376,f3851])).

fof(f3851,plain,
    ( spl5_679
  <=> ~ r2_hidden(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_679])])).

fof(f3845,plain,
    ( ~ r2_hidden(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)),sK3(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f60,f377,f143])).

fof(f3839,plain,
    ( spl5_656
    | ~ spl5_8
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3838,f379,f115,f3757])).

fof(f3757,plain,
    ( spl5_656
  <=> k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_656])])).

fof(f379,plain,
    ( spl5_58
  <=> v1_xboole_0(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f3838,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f3679,f116])).

fof(f3679,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = k1_xboole_0
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f380,f59])).

fof(f380,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f379])).

fof(f3837,plain,
    ( spl5_676
    | spl5_21
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3680,f379,f182,f3835])).

fof(f3835,plain,
    ( spl5_676
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_676])])).

fof(f3680,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_21
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f183,f380,f64])).

fof(f3830,plain,
    ( spl5_674
    | spl5_31
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3681,f379,f223,f3828])).

fof(f3828,plain,
    ( spl5_674
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_674])])).

fof(f3681,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_31
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f224,f380,f64])).

fof(f3823,plain,
    ( spl5_672
    | spl5_45
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3682,f379,f304,f3821])).

fof(f3821,plain,
    ( spl5_672
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_672])])).

fof(f3682,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_45
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f305,f380,f64])).

fof(f3816,plain,
    ( spl5_670
    | ~ spl5_58
    | spl5_201 ),
    inference(avatar_split_clause,[],[f3683,f1240,f379,f3814])).

fof(f3814,plain,
    ( spl5_670
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_670])])).

fof(f3683,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_58
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f380,f64])).

fof(f3809,plain,
    ( spl5_668
    | ~ spl5_58
    | spl5_67 ),
    inference(avatar_split_clause,[],[f3684,f410,f379,f3807])).

fof(f3807,plain,
    ( spl5_668
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_668])])).

fof(f3684,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_58
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f380,f64])).

fof(f3802,plain,
    ( spl5_666
    | ~ spl5_58
    | spl5_225 ),
    inference(avatar_split_clause,[],[f3685,f1400,f379,f3800])).

fof(f3800,plain,
    ( spl5_666
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_666])])).

fof(f3685,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_58
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f1401,f380,f64])).

fof(f3795,plain,
    ( spl5_664
    | ~ spl5_58
    | spl5_223 ),
    inference(avatar_split_clause,[],[f3686,f1393,f379,f3793])).

fof(f3793,plain,
    ( spl5_664
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_664])])).

fof(f3686,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_58
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f1394,f380,f64])).

fof(f3788,plain,
    ( spl5_662
    | spl5_27
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3687,f379,f211,f3786])).

fof(f3786,plain,
    ( spl5_662
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_662])])).

fof(f3687,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_27
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f212,f380,f64])).

fof(f3781,plain,
    ( spl5_660
    | spl5_29
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3688,f379,f220,f3779])).

fof(f3779,plain,
    ( spl5_660
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_660])])).

fof(f3688,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_29
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f221,f380,f64])).

fof(f3774,plain,
    ( spl5_658
    | ~ spl5_58
    | spl5_137 ),
    inference(avatar_split_clause,[],[f3689,f816,f379,f3772])).

fof(f3772,plain,
    ( spl5_658
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_658])])).

fof(f3689,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_58
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f380,f64])).

fof(f3767,plain,
    ( spl5_656
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3690,f379,f106,f3757])).

fof(f3690,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f107,f380,f70])).

fof(f3766,plain,
    ( spl5_656
    | ~ spl5_24
    | ~ spl5_58
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3765,f2490,f379,f198,f3757])).

fof(f3765,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_58
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3691,f2491])).

fof(f3691,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f199,f380,f70])).

fof(f3764,plain,
    ( spl5_656
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3763,f3100,f379,f354,f3757])).

fof(f3763,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3692,f3101])).

fof(f3692,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f355,f380,f70])).

fof(f3762,plain,
    ( spl5_656
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3694,f379,f106,f3757])).

fof(f3694,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f107,f380,f70])).

fof(f3761,plain,
    ( spl5_656
    | ~ spl5_24
    | ~ spl5_58
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3760,f2490,f379,f198,f3757])).

fof(f3760,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_58
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3695,f2491])).

fof(f3695,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_24
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f199,f380,f70])).

fof(f3759,plain,
    ( spl5_656
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3752,f3100,f379,f354,f3757])).

fof(f3752,plain,
    ( k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3696,f3101])).

fof(f3696,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_54
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f355,f380,f70])).

fof(f3751,plain,
    ( ~ spl5_655
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3699,f379,f153,f3749])).

fof(f3749,plain,
    ( spl5_655
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_655])])).

fof(f3699,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f154,f380,f79])).

fof(f3744,plain,
    ( ~ spl5_653
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3700,f379,f320,f3742])).

fof(f3742,plain,
    ( spl5_653
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_653])])).

fof(f3700,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f321,f380,f79])).

fof(f3737,plain,
    ( ~ spl5_651
    | ~ spl5_38
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3701,f379,f277,f3735])).

fof(f3735,plain,
    ( spl5_651
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_651])])).

fof(f3701,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_38
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f278,f380,f79])).

fof(f3730,plain,
    ( ~ spl5_649
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3704,f379,f153,f3728])).

fof(f3728,plain,
    ( spl5_649
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_649])])).

fof(f3704,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_14
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f154,f380,f169])).

fof(f3723,plain,
    ( ~ spl5_647
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3705,f379,f320,f3721])).

fof(f3721,plain,
    ( spl5_647
  <=> ~ r1_tarski(sK1,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_647])])).

fof(f3705,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f321,f380,f169])).

fof(f3716,plain,
    ( ~ spl5_645
    | ~ spl5_38
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f3706,f379,f277,f3714])).

fof(f3714,plain,
    ( spl5_645
  <=> ~ r1_tarski(sK0,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_645])])).

fof(f3706,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_38
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f278,f380,f169])).

fof(f3665,plain,
    ( spl5_514
    | ~ spl5_530
    | ~ spl5_542 ),
    inference(avatar_split_clause,[],[f3664,f3146,f3100,f3012])).

fof(f3012,plain,
    ( spl5_514
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_514])])).

fof(f3146,plain,
    ( spl5_542
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_542])])).

fof(f3664,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_542 ),
    inference(forward_demodulation,[],[f3147,f3101])).

fof(f3147,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_542 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f3663,plain,
    ( spl5_624
    | ~ spl5_8
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3662,f1403,f115,f3588])).

fof(f3588,plain,
    ( spl5_624
  <=> k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_624])])).

fof(f1403,plain,
    ( spl5_224
  <=> v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f3662,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_224 ),
    inference(forward_demodulation,[],[f3511,f116])).

fof(f3511,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = k1_xboole_0
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f1404,f59])).

fof(f1404,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_224 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f3661,plain,
    ( spl5_642
    | spl5_21
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3512,f1403,f182,f3659])).

fof(f3659,plain,
    ( spl5_642
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_642])])).

fof(f3512,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_21
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f183,f1404,f64])).

fof(f3654,plain,
    ( spl5_640
    | spl5_31
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3513,f1403,f223,f3652])).

fof(f3652,plain,
    ( spl5_640
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_640])])).

fof(f3513,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_31
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f224,f1404,f64])).

fof(f3647,plain,
    ( spl5_638
    | spl5_45
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3514,f1403,f304,f3645])).

fof(f3645,plain,
    ( spl5_638
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_638])])).

fof(f3514,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_45
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f305,f1404,f64])).

fof(f3640,plain,
    ( spl5_636
    | spl5_201
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3515,f1403,f1240,f3638])).

fof(f3638,plain,
    ( spl5_636
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_636])])).

fof(f3515,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_201
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f1241,f1404,f64])).

fof(f3633,plain,
    ( spl5_634
    | spl5_67
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3516,f1403,f410,f3631])).

fof(f3631,plain,
    ( spl5_634
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_634])])).

fof(f3516,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_67
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f411,f1404,f64])).

fof(f3626,plain,
    ( spl5_632
    | spl5_223
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3517,f1403,f1393,f3624])).

fof(f3624,plain,
    ( spl5_632
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_632])])).

fof(f3517,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_223
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f1394,f1404,f64])).

fof(f3619,plain,
    ( spl5_630
    | spl5_27
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3518,f1403,f211,f3617])).

fof(f3518,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_27
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f212,f1404,f64])).

fof(f3612,plain,
    ( spl5_628
    | spl5_29
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3519,f1403,f220,f3610])).

fof(f3519,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_29
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f221,f1404,f64])).

fof(f3605,plain,
    ( spl5_626
    | spl5_137
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3520,f1403,f816,f3603])).

fof(f3603,plain,
    ( spl5_626
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_626])])).

fof(f3520,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_137
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f817,f1404,f64])).

fof(f3598,plain,
    ( spl5_624
    | ~ spl5_6
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3521,f1403,f106,f3588])).

fof(f3521,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f107,f1404,f70])).

fof(f3597,plain,
    ( spl5_624
    | ~ spl5_24
    | ~ spl5_224
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3596,f2490,f1403,f198,f3588])).

fof(f3596,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_224
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3522,f2491])).

fof(f3522,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_24
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f199,f1404,f70])).

fof(f3595,plain,
    ( spl5_624
    | ~ spl5_54
    | ~ spl5_224
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3594,f3100,f1403,f354,f3588])).

fof(f3594,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_224
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3523,f3101])).

fof(f3523,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f355,f1404,f70])).

fof(f3593,plain,
    ( spl5_624
    | ~ spl5_6
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3525,f1403,f106,f3588])).

fof(f3525,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f107,f1404,f70])).

fof(f3592,plain,
    ( spl5_624
    | ~ spl5_24
    | ~ spl5_224
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3591,f2490,f1403,f198,f3588])).

fof(f3591,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_224
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3526,f2491])).

fof(f3526,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_24
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f199,f1404,f70])).

fof(f3590,plain,
    ( spl5_624
    | ~ spl5_54
    | ~ spl5_224
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3583,f3100,f1403,f354,f3588])).

fof(f3583,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_224
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3527,f3101])).

fof(f3527,plain,
    ( k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f355,f1404,f70])).

fof(f3582,plain,
    ( ~ spl5_623
    | ~ spl5_14
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3530,f1403,f153,f3580])).

fof(f3580,plain,
    ( spl5_623
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_623])])).

fof(f3530,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_14
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f154,f1404,f79])).

fof(f3575,plain,
    ( ~ spl5_621
    | ~ spl5_46
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3531,f1403,f320,f3573])).

fof(f3573,plain,
    ( spl5_621
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_621])])).

fof(f3531,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_46
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f321,f1404,f79])).

fof(f3568,plain,
    ( ~ spl5_619
    | ~ spl5_38
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3532,f1403,f277,f3566])).

fof(f3566,plain,
    ( spl5_619
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_619])])).

fof(f3532,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_38
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f278,f1404,f79])).

fof(f3561,plain,
    ( ~ spl5_617
    | ~ spl5_14
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3535,f1403,f153,f3559])).

fof(f3559,plain,
    ( spl5_617
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_617])])).

fof(f3535,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f154,f1404,f169])).

fof(f3554,plain,
    ( ~ spl5_615
    | ~ spl5_46
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3536,f1403,f320,f3552])).

fof(f3552,plain,
    ( spl5_615
  <=> ~ r1_tarski(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_615])])).

fof(f3536,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_46
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f321,f1404,f169])).

fof(f3547,plain,
    ( ~ spl5_613
    | ~ spl5_38
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f3537,f1403,f277,f3545])).

fof(f3545,plain,
    ( spl5_613
  <=> ~ r1_tarski(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_613])])).

fof(f3537,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_38
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f278,f1404,f169])).

fof(f3499,plain,
    ( spl5_508
    | ~ spl5_530
    | ~ spl5_540 ),
    inference(avatar_split_clause,[],[f3498,f3139,f3100,f2977])).

fof(f2977,plain,
    ( spl5_508
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_508])])).

fof(f3139,plain,
    ( spl5_540
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_540])])).

fof(f3498,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_540 ),
    inference(forward_demodulation,[],[f3140,f3101])).

fof(f3140,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_540 ),
    inference(avatar_component_clause,[],[f3139])).

fof(f3497,plain,
    ( spl5_594
    | ~ spl5_8
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3496,f1396,f115,f3429])).

fof(f3429,plain,
    ( spl5_594
  <=> k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_594])])).

fof(f1396,plain,
    ( spl5_222
  <=> v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f3496,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_222 ),
    inference(forward_demodulation,[],[f3353,f116])).

fof(f3353,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = k1_xboole_0
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f1397,f59])).

fof(f1397,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_222 ),
    inference(avatar_component_clause,[],[f1396])).

fof(f3495,plain,
    ( spl5_610
    | spl5_21
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3354,f1396,f182,f3493])).

fof(f3493,plain,
    ( spl5_610
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_610])])).

fof(f3354,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_21
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f183,f1397,f64])).

fof(f3488,plain,
    ( spl5_608
    | spl5_31
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3355,f1396,f223,f3486])).

fof(f3486,plain,
    ( spl5_608
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_608])])).

fof(f3355,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_31
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f224,f1397,f64])).

fof(f3481,plain,
    ( spl5_606
    | spl5_45
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3356,f1396,f304,f3479])).

fof(f3479,plain,
    ( spl5_606
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_606])])).

fof(f3356,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_45
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f305,f1397,f64])).

fof(f3474,plain,
    ( spl5_604
    | spl5_201
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3357,f1396,f1240,f3472])).

fof(f3472,plain,
    ( spl5_604
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_604])])).

fof(f3357,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_201
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f1241,f1397,f64])).

fof(f3467,plain,
    ( spl5_602
    | spl5_67
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3358,f1396,f410,f3465])).

fof(f3465,plain,
    ( spl5_602
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_602])])).

fof(f3358,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_67
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f411,f1397,f64])).

fof(f3460,plain,
    ( spl5_600
    | spl5_27
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3359,f1396,f211,f3458])).

fof(f3359,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_27
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f212,f1397,f64])).

fof(f3453,plain,
    ( spl5_598
    | spl5_29
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3360,f1396,f220,f3451])).

fof(f3360,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_29
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f221,f1397,f64])).

fof(f3446,plain,
    ( spl5_596
    | spl5_137
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3361,f1396,f816,f3444])).

fof(f3444,plain,
    ( spl5_596
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_596])])).

fof(f3361,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_137
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f817,f1397,f64])).

fof(f3439,plain,
    ( spl5_594
    | ~ spl5_6
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3362,f1396,f106,f3429])).

fof(f3362,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f107,f1397,f70])).

fof(f3438,plain,
    ( spl5_594
    | ~ spl5_24
    | ~ spl5_222
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3437,f2490,f1396,f198,f3429])).

fof(f3437,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_222
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3363,f2491])).

fof(f3363,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_24
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f199,f1397,f70])).

fof(f3436,plain,
    ( spl5_594
    | ~ spl5_54
    | ~ spl5_222
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3435,f3100,f1396,f354,f3429])).

fof(f3435,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_222
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3364,f3101])).

fof(f3364,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f355,f1397,f70])).

fof(f3434,plain,
    ( spl5_594
    | ~ spl5_6
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3366,f1396,f106,f3429])).

fof(f3366,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f107,f1397,f70])).

fof(f3433,plain,
    ( spl5_594
    | ~ spl5_24
    | ~ spl5_222
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3432,f2490,f1396,f198,f3429])).

fof(f3432,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_222
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3367,f2491])).

fof(f3367,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_24
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f199,f1397,f70])).

fof(f3431,plain,
    ( spl5_594
    | ~ spl5_54
    | ~ spl5_222
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3424,f3100,f1396,f354,f3429])).

fof(f3424,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = o_0_0_xboole_0
    | ~ spl5_54
    | ~ spl5_222
    | ~ spl5_530 ),
    inference(forward_demodulation,[],[f3368,f3101])).

fof(f3368,plain,
    ( k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)) = k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_54
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f355,f1397,f70])).

fof(f3423,plain,
    ( ~ spl5_593
    | ~ spl5_14
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3371,f1396,f153,f3421])).

fof(f3421,plain,
    ( spl5_593
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_593])])).

fof(f3371,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_14
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f154,f1397,f79])).

fof(f3416,plain,
    ( ~ spl5_591
    | ~ spl5_46
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3372,f1396,f320,f3414])).

fof(f3414,plain,
    ( spl5_591
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_591])])).

fof(f3372,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_46
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f321,f1397,f79])).

fof(f3409,plain,
    ( ~ spl5_589
    | ~ spl5_38
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3373,f1396,f277,f3407])).

fof(f3407,plain,
    ( spl5_589
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_589])])).

fof(f3373,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_38
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f278,f1397,f79])).

fof(f3402,plain,
    ( ~ spl5_587
    | ~ spl5_14
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3376,f1396,f153,f3400])).

fof(f3400,plain,
    ( spl5_587
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_587])])).

fof(f3376,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f154,f1397,f169])).

fof(f3395,plain,
    ( ~ spl5_585
    | ~ spl5_46
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3377,f1396,f320,f3393])).

fof(f3393,plain,
    ( spl5_585
  <=> ~ r1_tarski(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_585])])).

fof(f3377,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_46
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f321,f1397,f169])).

fof(f3388,plain,
    ( ~ spl5_583
    | ~ spl5_38
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f3378,f1396,f277,f3386])).

fof(f3386,plain,
    ( spl5_583
  <=> ~ r1_tarski(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_583])])).

fof(f3378,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_38
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f278,f1397,f169])).

fof(f3340,plain,
    ( spl5_432
    | ~ spl5_448
    | ~ spl5_456 ),
    inference(avatar_split_clause,[],[f3339,f2728,f2696,f2607])).

fof(f2607,plain,
    ( spl5_432
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_432])])).

fof(f3339,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_448
    | ~ spl5_456 ),
    inference(forward_demodulation,[],[f2729,f2697])).

fof(f3338,plain,
    ( spl5_432
    | ~ spl5_530
    | ~ spl5_548 ),
    inference(avatar_split_clause,[],[f3337,f3167,f3100,f2607])).

fof(f3167,plain,
    ( spl5_548
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_548])])).

fof(f3337,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_530
    | ~ spl5_548 ),
    inference(forward_demodulation,[],[f3168,f3101])).

fof(f3168,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_548 ),
    inference(avatar_component_clause,[],[f3167])).

fof(f3336,plain,
    ( spl5_566
    | ~ spl5_8
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3335,f307,f115,f3275])).

fof(f3334,plain,
    ( spl5_580
    | spl5_21
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3201,f307,f182,f3332])).

fof(f3327,plain,
    ( spl5_578
    | spl5_31
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3202,f307,f223,f3325])).

fof(f3325,plain,
    ( spl5_578
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_578])])).

fof(f3202,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_31
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f224,f308,f64])).

fof(f3320,plain,
    ( spl5_576
    | ~ spl5_44
    | spl5_201 ),
    inference(avatar_split_clause,[],[f3203,f1240,f307,f3318])).

fof(f3318,plain,
    ( spl5_576
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_576])])).

fof(f3203,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_44
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f308,f64])).

fof(f3313,plain,
    ( spl5_574
    | ~ spl5_44
    | spl5_67 ),
    inference(avatar_split_clause,[],[f3204,f410,f307,f3311])).

fof(f3311,plain,
    ( spl5_574
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_574])])).

fof(f3204,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_44
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f308,f64])).

fof(f3306,plain,
    ( spl5_572
    | spl5_27
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3205,f307,f211,f3304])).

fof(f3304,plain,
    ( spl5_572
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_572])])).

fof(f3205,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_27
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f212,f308,f64])).

fof(f3299,plain,
    ( spl5_570
    | spl5_29
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3206,f307,f220,f3297])).

fof(f3297,plain,
    ( spl5_570
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_570])])).

fof(f3206,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_29
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f221,f308,f64])).

fof(f3292,plain,
    ( spl5_568
    | ~ spl5_44
    | spl5_137 ),
    inference(avatar_split_clause,[],[f3207,f816,f307,f3290])).

fof(f3285,plain,
    ( spl5_566
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3208,f307,f106,f3275])).

fof(f3284,plain,
    ( spl5_566
    | ~ spl5_24
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3283,f2490,f307,f198,f3275])).

fof(f3282,plain,
    ( spl5_566
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3281,f3100,f354,f307,f3275])).

fof(f3280,plain,
    ( spl5_566
    | ~ spl5_6
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3212,f307,f106,f3275])).

fof(f3279,plain,
    ( spl5_566
    | ~ spl5_24
    | ~ spl5_44
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3278,f2490,f307,f198,f3275])).

fof(f3277,plain,
    ( spl5_566
    | ~ spl5_44
    | ~ spl5_54
    | ~ spl5_530 ),
    inference(avatar_split_clause,[],[f3270,f3100,f354,f307,f3275])).

fof(f3269,plain,
    ( ~ spl5_565
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3217,f307,f153,f3267])).

fof(f3267,plain,
    ( spl5_565
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_565])])).

fof(f3217,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f154,f308,f79])).

fof(f3262,plain,
    ( ~ spl5_563
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f3218,f320,f307,f3260])).

fof(f3260,plain,
    ( spl5_563
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_563])])).

fof(f3218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f321,f308,f79])).

fof(f3255,plain,
    ( ~ spl5_561
    | ~ spl5_38
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3219,f307,f277,f3253])).

fof(f3253,plain,
    ( spl5_561
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_561])])).

fof(f3219,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_38
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f278,f308,f79])).

fof(f3248,plain,
    ( ~ spl5_559
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3222,f307,f153,f3246])).

fof(f3246,plain,
    ( spl5_559
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_559])])).

fof(f3222,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_14
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f154,f308,f169])).

fof(f3241,plain,
    ( ~ spl5_557
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f3223,f320,f307,f3239])).

fof(f3239,plain,
    ( spl5_557
  <=> ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_557])])).

fof(f3223,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f321,f308,f169])).

fof(f3234,plain,
    ( ~ spl5_555
    | ~ spl5_38
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f3224,f307,f277,f3232])).

fof(f3232,plain,
    ( spl5_555
  <=> ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_555])])).

fof(f3224,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_38
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f278,f308,f169])).

fof(f3185,plain,
    ( spl5_530
    | ~ spl5_8
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3184,f354,f115,f3100])).

fof(f3184,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f3023,f116])).

fof(f3023,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = k1_xboole_0
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f355,f59])).

fof(f3183,plain,
    ( spl5_552
    | spl5_21
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3024,f354,f182,f3181])).

fof(f3181,plain,
    ( spl5_552
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_552])])).

fof(f3024,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f183,f355,f64])).

fof(f3176,plain,
    ( spl5_550
    | spl5_31
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3025,f354,f223,f3174])).

fof(f3174,plain,
    ( spl5_550
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_550])])).

fof(f3025,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f224,f355,f64])).

fof(f3169,plain,
    ( spl5_548
    | spl5_45
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3026,f354,f304,f3167])).

fof(f3026,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_45
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f305,f355,f64])).

fof(f3162,plain,
    ( spl5_546
    | ~ spl5_54
    | spl5_201 ),
    inference(avatar_split_clause,[],[f3027,f1240,f354,f3160])).

fof(f3160,plain,
    ( spl5_546
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_546])])).

fof(f3027,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f355,f64])).

fof(f3155,plain,
    ( spl5_544
    | ~ spl5_54
    | spl5_67 ),
    inference(avatar_split_clause,[],[f3028,f410,f354,f3153])).

fof(f3153,plain,
    ( spl5_544
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_544])])).

fof(f3028,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f355,f64])).

fof(f3148,plain,
    ( spl5_542
    | ~ spl5_54
    | spl5_225 ),
    inference(avatar_split_clause,[],[f3029,f1400,f354,f3146])).

fof(f3029,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f1401,f355,f64])).

fof(f3141,plain,
    ( spl5_540
    | ~ spl5_54
    | spl5_223 ),
    inference(avatar_split_clause,[],[f3030,f1393,f354,f3139])).

fof(f3030,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f1394,f355,f64])).

fof(f3134,plain,
    ( spl5_538
    | spl5_27
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3031,f354,f211,f3132])).

fof(f3132,plain,
    ( spl5_538
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_538])])).

fof(f3031,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_27
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f212,f355,f64])).

fof(f3127,plain,
    ( spl5_536
    | spl5_29
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3032,f354,f220,f3125])).

fof(f3125,plain,
    ( spl5_536
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_536])])).

fof(f3032,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_29
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f221,f355,f64])).

fof(f3120,plain,
    ( spl5_534
    | ~ spl5_54
    | spl5_137 ),
    inference(avatar_split_clause,[],[f3033,f816,f354,f3118])).

fof(f3033,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_54
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f355,f64])).

fof(f3113,plain,
    ( spl5_532
    | ~ spl5_54
    | spl5_117 ),
    inference(avatar_split_clause,[],[f3034,f667,f354,f3111])).

fof(f3106,plain,
    ( spl5_530
    | ~ spl5_6
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3035,f354,f106,f3100])).

fof(f3035,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f107,f355,f70])).

fof(f3105,plain,
    ( spl5_530
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3104,f2490,f354,f198,f3100])).

fof(f3104,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3036,f2491])).

fof(f3103,plain,
    ( spl5_530
    | ~ spl5_6
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3038,f354,f106,f3100])).

fof(f3038,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f107,f355,f70])).

fof(f3102,plain,
    ( spl5_530
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3095,f2490,f354,f198,f3100])).

fof(f3095,plain,
    ( k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_24
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f3039,f2491])).

fof(f3094,plain,
    ( ~ spl5_529
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3042,f354,f153,f3092])).

fof(f3092,plain,
    ( spl5_529
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_529])])).

fof(f3042,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f154,f355,f79])).

fof(f3087,plain,
    ( ~ spl5_527
    | ~ spl5_46
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3043,f354,f320,f3085])).

fof(f3043,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_46
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f321,f355,f79])).

fof(f3080,plain,
    ( ~ spl5_525
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3044,f354,f277,f3078])).

fof(f3044,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)))
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f278,f355,f79])).

fof(f3073,plain,
    ( ~ spl5_523
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3047,f354,f153,f3071])).

fof(f3071,plain,
    ( spl5_523
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_523])])).

fof(f3047,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f154,f355,f169])).

fof(f3066,plain,
    ( ~ spl5_521
    | ~ spl5_46
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3048,f354,f320,f3064])).

fof(f3064,plain,
    ( spl5_521
  <=> ~ r1_tarski(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_521])])).

fof(f3048,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_46
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f321,f355,f169])).

fof(f3059,plain,
    ( ~ spl5_519
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f3049,f354,f277,f3057])).

fof(f3057,plain,
    ( spl5_519
  <=> ~ r1_tarski(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_519])])).

fof(f3049,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_38
    | ~ spl5_54 ),
    inference(unit_resulting_resolution,[],[f278,f355,f169])).

fof(f3022,plain,
    ( spl5_516
    | spl5_225 ),
    inference(avatar_split_clause,[],[f2995,f1400,f3020])).

fof(f3020,plain,
    ( spl5_516
  <=> r2_hidden(sK3(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_516])])).

fof(f2995,plain,
    ( r2_hidden(sK3(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))),k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f60,f1401,f63])).

fof(f3015,plain,
    ( spl5_514
    | ~ spl5_6
    | spl5_225 ),
    inference(avatar_split_clause,[],[f2996,f1400,f106,f3012])).

fof(f2996,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f107,f1401,f64])).

fof(f3014,plain,
    ( spl5_514
    | ~ spl5_24
    | spl5_225
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f3007,f2490,f1400,f198,f3012])).

fof(f3007,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_225
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2997,f2491])).

fof(f3006,plain,
    ( ~ spl5_513
    | spl5_225 ),
    inference(avatar_split_clause,[],[f2998,f1400,f3004])).

fof(f3004,plain,
    ( spl5_513
  <=> ~ r2_hidden(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_513])])).

fof(f2998,plain,
    ( ~ r2_hidden(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_225 ),
    inference(unit_resulting_resolution,[],[f60,f1401,f143])).

fof(f2987,plain,
    ( spl5_510
    | spl5_223 ),
    inference(avatar_split_clause,[],[f2960,f1393,f2985])).

fof(f2985,plain,
    ( spl5_510
  <=> r2_hidden(sK3(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_510])])).

fof(f2960,plain,
    ( r2_hidden(sK3(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))),k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f60,f1394,f63])).

fof(f2980,plain,
    ( spl5_508
    | ~ spl5_6
    | spl5_223 ),
    inference(avatar_split_clause,[],[f2961,f1393,f106,f2977])).

fof(f2961,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f107,f1394,f64])).

fof(f2979,plain,
    ( spl5_508
    | ~ spl5_24
    | spl5_223
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f2972,f2490,f1393,f198,f2977])).

fof(f2972,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_223
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2962,f2491])).

fof(f2971,plain,
    ( ~ spl5_507
    | spl5_223 ),
    inference(avatar_split_clause,[],[f2963,f1393,f2969])).

fof(f2969,plain,
    ( spl5_507
  <=> ~ r2_hidden(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_507])])).

fof(f2963,plain,
    ( ~ r2_hidden(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)),sK3(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1))))
    | ~ spl5_223 ),
    inference(unit_resulting_resolution,[],[f60,f1394,f143])).

fof(f2941,plain,
    ( spl5_304
    | ~ spl5_344
    | ~ spl5_352 ),
    inference(avatar_split_clause,[],[f2940,f2177,f2148,f1923])).

fof(f1923,plain,
    ( spl5_304
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_304])])).

fof(f2940,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_344
    | ~ spl5_352 ),
    inference(forward_demodulation,[],[f2178,f2149])).

fof(f2939,plain,
    ( spl5_304
    | ~ spl5_408
    | ~ spl5_418 ),
    inference(avatar_split_clause,[],[f2938,f2526,f2490,f1923])).

fof(f2526,plain,
    ( spl5_418
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_418])])).

fof(f2938,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_408
    | ~ spl5_418 ),
    inference(forward_demodulation,[],[f2527,f2491])).

fof(f2527,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_418 ),
    inference(avatar_component_clause,[],[f2526])).

fof(f2937,plain,
    ( spl5_504
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f2890,f823,f153,f2935])).

fof(f2935,plain,
    ( spl5_504
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_504])])).

fof(f2890,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK2)
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f154,f824,f65])).

fof(f2930,plain,
    ( spl5_502
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f2888,f823,f153,f2928])).

fof(f2928,plain,
    ( spl5_502
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_502])])).

fof(f2888,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK2)
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f154,f824,f167])).

fof(f2923,plain,
    ( ~ spl5_501
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f2887,f823,f153,f2921])).

fof(f2921,plain,
    ( spl5_501
  <=> ~ r2_hidden(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_501])])).

fof(f2887,plain,
    ( ~ r2_hidden(sK2,sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f154,f824,f168])).

fof(f2916,plain,
    ( ~ spl5_499
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(avatar_split_clause,[],[f2909,f1987,f823,f153,f2914])).

fof(f2914,plain,
    ( spl5_499
  <=> ~ r2_hidden(sK2,sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_499])])).

fof(f1987,plain,
    ( spl5_316
  <=> k1_funct_2(sK0,sK1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_316])])).

fof(f2909,plain,
    ( ~ r2_hidden(sK2,sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(forward_demodulation,[],[f2887,f1988])).

fof(f1988,plain,
    ( k1_funct_2(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_316 ),
    inference(avatar_component_clause,[],[f1987])).

fof(f2908,plain,
    ( spl5_496
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(avatar_split_clause,[],[f2901,f1987,f823,f153,f2906])).

fof(f2906,plain,
    ( spl5_496
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_496])])).

fof(f2901,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK2)
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(forward_demodulation,[],[f2888,f1988])).

fof(f2900,plain,
    ( spl5_494
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(avatar_split_clause,[],[f2893,f1987,f823,f153,f2898])).

fof(f2898,plain,
    ( spl5_494
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_494])])).

fof(f2893,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK2)
    | ~ spl5_14
    | ~ spl5_138
    | ~ spl5_316 ),
    inference(forward_demodulation,[],[f2890,f1988])).

fof(f2892,plain,
    ( spl5_154
    | ~ spl5_138 ),
    inference(avatar_split_clause,[],[f2891,f823,f950])).

fof(f950,plain,
    ( spl5_154
  <=> m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f2891,plain,
    ( m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl5_138 ),
    inference(unit_resulting_resolution,[],[f824,f69])).

fof(f2886,plain,
    ( spl5_492
    | ~ spl5_2
    | ~ spl5_4
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2810,f826,f99,f92,f2884])).

fof(f2884,plain,
    ( spl5_492
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_492])])).

fof(f2810,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f100,f93,f827,f270])).

fof(f2879,plain,
    ( spl5_490
    | ~ spl5_2
    | ~ spl5_4
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2811,f826,f99,f92,f2877])).

fof(f2877,plain,
    ( spl5_490
  <=> v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_490])])).

fof(f2811,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f100,f93,f827,f242])).

fof(f2872,plain,
    ( spl5_488
    | ~ spl5_2
    | ~ spl5_4
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2812,f826,f99,f92,f2870])).

fof(f2870,plain,
    ( spl5_488
  <=> v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_488])])).

fof(f2812,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f100,f93,f827,f206])).

fof(f2865,plain,
    ( spl5_486
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2813,f826,f2863])).

fof(f2863,plain,
    ( spl5_486
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_486])])).

fof(f2813,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f827,f66])).

fof(f2858,plain,
    ( ~ spl5_477
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2814,f826,f2827])).

fof(f2827,plain,
    ( spl5_477
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_477])])).

fof(f2814,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK2)
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f827,f67])).

fof(f2857,plain,
    ( spl5_484
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2816,f826,f2855])).

fof(f2855,plain,
    ( spl5_484
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_484])])).

fof(f2816,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f827,f146])).

fof(f2850,plain,
    ( ~ spl5_483
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2817,f826,f2848])).

fof(f2848,plain,
    ( spl5_483
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_483])])).

fof(f2817,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),sK2))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f827,f147])).

fof(f2843,plain,
    ( ~ spl5_481
    | spl5_137
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2819,f826,f816,f2841])).

fof(f2841,plain,
    ( spl5_481
  <=> ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_481])])).

fof(f2819,plain,
    ( ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK2)
    | ~ spl5_137
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f817,f827,f158])).

fof(f2836,plain,
    ( ~ spl5_479
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2820,f826,f2834])).

fof(f2834,plain,
    ( spl5_479
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK3(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_479])])).

fof(f2820,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK3(k1_zfmisc_1(sK2)))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f121,f827,f170])).

fof(f2829,plain,
    ( ~ spl5_477
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2821,f826,f2827])).

fof(f2821,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),sK2),sK2)
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f159,f827,f170])).

fof(f2809,plain,
    ( spl5_474
    | ~ spl5_2
    | ~ spl5_4
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2756,f523,f99,f92,f2807])).

fof(f2807,plain,
    ( spl5_474
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_474])])).

fof(f2756,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f100,f93,f524,f270])).

fof(f2802,plain,
    ( spl5_472
    | ~ spl5_2
    | ~ spl5_4
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2757,f523,f99,f92,f2800])).

fof(f2800,plain,
    ( spl5_472
  <=> v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_472])])).

fof(f2757,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f100,f93,f524,f242])).

fof(f2795,plain,
    ( spl5_470
    | ~ spl5_2
    | ~ spl5_4
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2758,f523,f99,f92,f2793])).

fof(f2793,plain,
    ( spl5_470
  <=> v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_470])])).

fof(f2758,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f100,f93,f524,f206])).

fof(f2788,plain,
    ( spl5_468
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2759,f523,f2786])).

fof(f2786,plain,
    ( spl5_468
  <=> r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_468])])).

fof(f2759,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f524,f66])).

fof(f2781,plain,
    ( spl5_466
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2762,f523,f2779])).

fof(f2779,plain,
    ( spl5_466
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_466])])).

fof(f2762,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f524,f146])).

fof(f2774,plain,
    ( ~ spl5_465
    | spl5_87 ),
    inference(avatar_split_clause,[],[f2763,f523,f2772])).

fof(f2772,plain,
    ( spl5_465
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_465])])).

fof(f2763,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f524,f147])).

fof(f2753,plain,
    ( spl5_448
    | ~ spl5_8
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2752,f670,f115,f2696])).

fof(f670,plain,
    ( spl5_116
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f2752,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_8
    | ~ spl5_116 ),
    inference(forward_demodulation,[],[f2623,f116])).

fof(f2623,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f671,f59])).

fof(f671,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl5_116 ),
    inference(avatar_component_clause,[],[f670])).

fof(f2751,plain,
    ( spl5_462
    | spl5_21
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2624,f670,f182,f2749])).

fof(f2749,plain,
    ( spl5_462
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_462])])).

fof(f2624,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK3(sK0)))
    | ~ spl5_21
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f183,f671,f64])).

fof(f2744,plain,
    ( spl5_460
    | spl5_31
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2625,f670,f223,f2742])).

fof(f2742,plain,
    ( spl5_460
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_460])])).

fof(f2625,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),sK3(sK0)))
    | ~ spl5_31
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f224,f671,f64])).

fof(f2737,plain,
    ( spl5_458
    | ~ spl5_116
    | spl5_201 ),
    inference(avatar_split_clause,[],[f2626,f1240,f670,f2735])).

fof(f2735,plain,
    ( spl5_458
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_458])])).

fof(f2626,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK3(sK0)))
    | ~ spl5_116
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f671,f64])).

fof(f2730,plain,
    ( spl5_456
    | spl5_45
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2627,f670,f304,f2728])).

fof(f2627,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),sK3(sK0)))
    | ~ spl5_45
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f305,f671,f64])).

fof(f2723,plain,
    ( spl5_454
    | spl5_27
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2628,f670,f211,f2721])).

fof(f2628,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK3(sK0)))
    | ~ spl5_27
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f212,f671,f64])).

fof(f2716,plain,
    ( spl5_452
    | spl5_29
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2629,f670,f220,f2714])).

fof(f2629,plain,
    ( v1_xboole_0(k1_funct_2(sK1,sK3(sK0)))
    | ~ spl5_29
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f221,f671,f64])).

fof(f2709,plain,
    ( spl5_450
    | ~ spl5_116
    | spl5_137 ),
    inference(avatar_split_clause,[],[f2630,f816,f670,f2707])).

fof(f2707,plain,
    ( spl5_450
  <=> v1_xboole_0(k1_funct_2(sK2,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_450])])).

fof(f2630,plain,
    ( v1_xboole_0(k1_funct_2(sK2,sK3(sK0)))
    | ~ spl5_116
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f671,f64])).

fof(f2702,plain,
    ( spl5_448
    | ~ spl5_6
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2631,f670,f106,f2696])).

fof(f2631,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_6
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f107,f671,f70])).

fof(f2701,plain,
    ( spl5_448
    | ~ spl5_24
    | ~ spl5_116
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f2700,f2490,f670,f198,f2696])).

fof(f2700,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_24
    | ~ spl5_116
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2632,f2491])).

fof(f2632,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = sK3(sK0)
    | ~ spl5_24
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f199,f671,f70])).

fof(f2699,plain,
    ( spl5_448
    | ~ spl5_6
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2634,f670,f106,f2696])).

fof(f2634,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_6
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f107,f671,f70])).

fof(f2698,plain,
    ( spl5_448
    | ~ spl5_24
    | ~ spl5_116
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f2691,f2490,f670,f198,f2696])).

fof(f2691,plain,
    ( o_0_0_xboole_0 = sK3(sK0)
    | ~ spl5_24
    | ~ spl5_116
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2635,f2491])).

fof(f2635,plain,
    ( k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0) = sK3(sK0)
    | ~ spl5_24
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f199,f671,f70])).

fof(f2690,plain,
    ( ~ spl5_447
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2638,f670,f153,f2688])).

fof(f2688,plain,
    ( spl5_447
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_447])])).

fof(f2638,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK3(sK0)))
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f154,f671,f79])).

fof(f2683,plain,
    ( ~ spl5_445
    | ~ spl5_46
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2639,f670,f320,f2681])).

fof(f2681,plain,
    ( spl5_445
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_445])])).

fof(f2639,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK3(sK0)))
    | ~ spl5_46
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f321,f671,f79])).

fof(f2676,plain,
    ( ~ spl5_443
    | ~ spl5_38
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2640,f670,f277,f2674])).

fof(f2674,plain,
    ( spl5_443
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_443])])).

fof(f2640,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK3(sK0)))
    | ~ spl5_38
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f278,f671,f79])).

fof(f2669,plain,
    ( ~ spl5_441
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2643,f670,f153,f2667])).

fof(f2667,plain,
    ( spl5_441
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_441])])).

fof(f2643,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK3(sK0))
    | ~ spl5_14
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f154,f671,f169])).

fof(f2662,plain,
    ( ~ spl5_439
    | ~ spl5_46
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2644,f670,f320,f2660])).

fof(f2660,plain,
    ( spl5_439
  <=> ~ r1_tarski(sK1,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_439])])).

fof(f2644,plain,
    ( ~ r1_tarski(sK1,sK3(sK0))
    | ~ spl5_46
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f321,f671,f169])).

fof(f2655,plain,
    ( ~ spl5_437
    | ~ spl5_38
    | ~ spl5_116 ),
    inference(avatar_split_clause,[],[f2645,f670,f277,f2653])).

fof(f2653,plain,
    ( spl5_437
  <=> ~ r1_tarski(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_437])])).

fof(f2645,plain,
    ( ~ r1_tarski(sK0,sK3(sK0))
    | ~ spl5_38
    | ~ spl5_116 ),
    inference(unit_resulting_resolution,[],[f278,f671,f169])).

fof(f2617,plain,
    ( spl5_434
    | spl5_45 ),
    inference(avatar_split_clause,[],[f2590,f304,f2615])).

fof(f2615,plain,
    ( spl5_434
  <=> r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_434])])).

fof(f2590,plain,
    ( r2_hidden(sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)),k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f60,f305,f63])).

fof(f2610,plain,
    ( spl5_432
    | ~ spl5_6
    | spl5_45 ),
    inference(avatar_split_clause,[],[f2591,f304,f106,f2607])).

fof(f2591,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f107,f305,f64])).

fof(f2609,plain,
    ( spl5_432
    | ~ spl5_24
    | spl5_45
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f2602,f2490,f304,f198,f2607])).

fof(f2602,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_45
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f2592,f2491])).

fof(f2592,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f199,f305,f64])).

fof(f2601,plain,
    ( ~ spl5_431
    | spl5_45 ),
    inference(avatar_split_clause,[],[f2593,f304,f2599])).

fof(f2599,plain,
    ( spl5_431
  <=> ~ r2_hidden(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_431])])).

fof(f2593,plain,
    ( ~ r2_hidden(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0),sK3(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0)))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f60,f305,f143])).

fof(f2578,plain,
    ( ~ spl5_429
    | spl5_205
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f2571,f2148,f1267,f2576])).

fof(f2576,plain,
    ( spl5_429
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_429])])).

fof(f1267,plain,
    ( spl5_205
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f2571,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_205
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f1268,f2149])).

fof(f1268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_205 ),
    inference(avatar_component_clause,[],[f1267])).

fof(f2570,plain,
    ( ~ spl5_427
    | spl5_207
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f2563,f2148,f1274,f2568])).

fof(f1274,plain,
    ( spl5_207
  <=> ~ r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f2563,plain,
    ( ~ r1_tarski(sK2,o_0_0_xboole_0)
    | ~ spl5_207
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f1275,f2149])).

fof(f1275,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_207 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f2551,plain,
    ( spl5_408
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2550,f198,f115,f2490])).

fof(f2549,plain,
    ( spl5_424
    | spl5_21
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2420,f198,f182,f2547])).

fof(f2542,plain,
    ( spl5_422
    | ~ spl5_24
    | spl5_129 ),
    inference(avatar_split_clause,[],[f2421,f776,f198,f2540])).

fof(f2535,plain,
    ( spl5_420
    | ~ spl5_24
    | spl5_31 ),
    inference(avatar_split_clause,[],[f2422,f223,f198,f2533])).

fof(f2533,plain,
    ( spl5_420
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_420])])).

fof(f2422,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f224,f199,f64])).

fof(f2528,plain,
    ( spl5_418
    | ~ spl5_24
    | spl5_67 ),
    inference(avatar_split_clause,[],[f2423,f410,f198,f2526])).

fof(f2423,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f411,f199,f64])).

fof(f2521,plain,
    ( spl5_416
    | ~ spl5_24
    | spl5_201 ),
    inference(avatar_split_clause,[],[f2424,f1240,f198,f2519])).

fof(f2519,plain,
    ( spl5_416
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_416])])).

fof(f2424,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1241,f199,f64])).

fof(f2514,plain,
    ( spl5_414
    | ~ spl5_24
    | spl5_27 ),
    inference(avatar_split_clause,[],[f2425,f211,f198,f2512])).

fof(f2512,plain,
    ( spl5_414
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_414])])).

fof(f2425,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f212,f199,f64])).

fof(f2507,plain,
    ( spl5_412
    | ~ spl5_24
    | spl5_29 ),
    inference(avatar_split_clause,[],[f2426,f220,f198,f2505])).

fof(f2505,plain,
    ( spl5_412
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_412])])).

fof(f2426,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f221,f199,f64])).

fof(f2500,plain,
    ( spl5_410
    | ~ spl5_24
    | spl5_137 ),
    inference(avatar_split_clause,[],[f2427,f816,f198,f2498])).

fof(f2493,plain,
    ( spl5_408
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2428,f198,f106,f2490])).

fof(f2492,plain,
    ( spl5_408
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2430,f198,f106,f2490])).

fof(f2485,plain,
    ( ~ spl5_407
    | ~ spl5_14
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2433,f198,f153,f2483])).

fof(f2483,plain,
    ( spl5_407
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_407])])).

fof(f2433,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f154,f199,f79])).

fof(f2478,plain,
    ( ~ spl5_405
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f2434,f320,f198,f2476])).

fof(f2434,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f321,f199,f79])).

fof(f2471,plain,
    ( ~ spl5_403
    | ~ spl5_24
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f2435,f277,f198,f2469])).

fof(f2435,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)))
    | ~ spl5_24
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f199,f79])).

fof(f2464,plain,
    ( ~ spl5_401
    | ~ spl5_14
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2438,f198,f153,f2462])).

fof(f2462,plain,
    ( spl5_401
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_401])])).

fof(f2438,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f154,f199,f169])).

fof(f2457,plain,
    ( ~ spl5_399
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f2439,f320,f198,f2455])).

fof(f2455,plain,
    ( spl5_399
  <=> ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_399])])).

fof(f2439,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f321,f199,f169])).

fof(f2450,plain,
    ( ~ spl5_397
    | ~ spl5_24
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f2440,f277,f198,f2448])).

fof(f2448,plain,
    ( spl5_397
  <=> ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_397])])).

fof(f2440,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_24
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f199,f169])).

fof(f2418,plain,
    ( ~ spl5_6
    | spl5_279 ),
    inference(avatar_contradiction_clause,[],[f2412])).

fof(f2412,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_279 ),
    inference(unit_resulting_resolution,[],[f107,f1729,f148])).

fof(f1729,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_279 ),
    inference(avatar_component_clause,[],[f1728])).

fof(f1728,plain,
    ( spl5_279
  <=> ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_279])])).

fof(f2417,plain,
    ( ~ spl5_6
    | spl5_279 ),
    inference(avatar_contradiction_clause,[],[f2406])).

fof(f2406,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_279 ),
    inference(unit_resulting_resolution,[],[f118,f1729,f66])).

fof(f2404,plain,
    ( ~ spl5_6
    | spl5_265 ),
    inference(avatar_contradiction_clause,[],[f2397])).

fof(f2397,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_265 ),
    inference(unit_resulting_resolution,[],[f107,f1632,f148])).

fof(f1632,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_265 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f1631,plain,
    ( spl5_265
  <=> ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_265])])).

fof(f2403,plain,
    ( ~ spl5_6
    | spl5_265 ),
    inference(avatar_contradiction_clause,[],[f2391])).

fof(f2391,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_265 ),
    inference(unit_resulting_resolution,[],[f118,f1632,f66])).

fof(f2387,plain,
    ( ~ spl5_393
    | spl5_394
    | spl5_199 ),
    inference(avatar_split_clause,[],[f2367,f1229,f2385,f2379])).

fof(f2379,plain,
    ( spl5_393
  <=> ~ m1_subset_1(sK2,k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_393])])).

fof(f2385,plain,
    ( spl5_394
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_394])])).

fof(f2367,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ m1_subset_1(sK2,k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_199 ),
    inference(resolution,[],[f1230,f63])).

fof(f2374,plain,
    ( ~ spl5_391
    | spl5_199 ),
    inference(avatar_split_clause,[],[f2362,f1229,f2372])).

fof(f2372,plain,
    ( spl5_391
  <=> ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_391])])).

fof(f2362,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1))))
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f121,f1230,f65])).

fof(f2356,plain,
    ( spl5_388
    | spl5_117 ),
    inference(avatar_split_clause,[],[f2332,f667,f2354])).

fof(f2349,plain,
    ( spl5_386
    | ~ spl5_6
    | spl5_117 ),
    inference(avatar_split_clause,[],[f2333,f667,f106,f2347])).

fof(f2342,plain,
    ( ~ spl5_385
    | spl5_117 ),
    inference(avatar_split_clause,[],[f2335,f667,f2340])).

fof(f2340,plain,
    ( spl5_385
  <=> ~ r2_hidden(sK3(sK0),sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_385])])).

fof(f2335,plain,
    ( ~ r2_hidden(sK3(sK0),sK3(sK3(sK0)))
    | ~ spl5_117 ),
    inference(unit_resulting_resolution,[],[f60,f668,f143])).

fof(f2326,plain,
    ( spl5_286
    | ~ spl5_8
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2325,f1237,f115,f1758])).

fof(f1758,plain,
    ( spl5_286
  <=> k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_286])])).

fof(f1237,plain,
    ( spl5_200
  <=> v1_xboole_0(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f2325,plain,
    ( k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_200 ),
    inference(forward_demodulation,[],[f2226,f116])).

fof(f2226,plain,
    ( k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) = k1_xboole_0
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f1238,f59])).

fof(f1238,plain,
    ( v1_xboole_0(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_200 ),
    inference(avatar_component_clause,[],[f1237])).

fof(f2324,plain,
    ( spl5_382
    | spl5_21
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2227,f1237,f182,f2322])).

fof(f2322,plain,
    ( spl5_382
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_382])])).

fof(f2227,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f183,f1238,f64])).

fof(f2317,plain,
    ( spl5_276
    | spl5_129
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2228,f1237,f776,f1720])).

fof(f1720,plain,
    ( spl5_276
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_276])])).

fof(f2228,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_129
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f777,f1238,f64])).

fof(f2316,plain,
    ( spl5_380
    | spl5_31
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2229,f1237,f223,f2314])).

fof(f2314,plain,
    ( spl5_380
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_380])])).

fof(f2229,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f224,f1238,f64])).

fof(f2309,plain,
    ( spl5_378
    | spl5_67
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2230,f1237,f410,f2307])).

fof(f2307,plain,
    ( spl5_378
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_378])])).

fof(f2230,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_67
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f411,f1238,f64])).

fof(f2302,plain,
    ( spl5_376
    | spl5_27
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2231,f1237,f211,f2300])).

fof(f2300,plain,
    ( spl5_376
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_376])])).

fof(f2231,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_27
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f212,f1238,f64])).

fof(f2295,plain,
    ( spl5_274
    | spl5_29
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2232,f1237,f220,f1709])).

fof(f1709,plain,
    ( spl5_274
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_274])])).

fof(f2232,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_29
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f221,f1238,f64])).

fof(f2294,plain,
    ( spl5_272
    | spl5_137
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2233,f1237,f816,f1704])).

fof(f1704,plain,
    ( spl5_272
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_272])])).

fof(f2233,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_137
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f817,f1238,f64])).

fof(f2293,plain,
    ( spl5_286
    | ~ spl5_6
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2234,f1237,f106,f1758])).

fof(f2234,plain,
    ( k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f107,f1238,f70])).

fof(f2292,plain,
    ( spl5_286
    | ~ spl5_6
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2236,f1237,f106,f1758])).

fof(f2236,plain,
    ( k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f107,f1238,f70])).

fof(f2291,plain,
    ( ~ spl5_375
    | ~ spl5_14
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2239,f1237,f153,f2289])).

fof(f2289,plain,
    ( spl5_375
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_375])])).

fof(f2239,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f154,f1238,f79])).

fof(f2284,plain,
    ( ~ spl5_373
    | ~ spl5_46
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2240,f1237,f320,f2282])).

fof(f2282,plain,
    ( spl5_373
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_373])])).

fof(f2240,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_46
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f321,f1238,f79])).

fof(f2277,plain,
    ( ~ spl5_371
    | ~ spl5_38
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2241,f1237,f277,f2275])).

fof(f2275,plain,
    ( spl5_371
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_371])])).

fof(f2241,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_38
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f278,f1238,f79])).

fof(f2270,plain,
    ( ~ spl5_369
    | ~ spl5_14
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2244,f1237,f153,f2268])).

fof(f2268,plain,
    ( spl5_369
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_369])])).

fof(f2244,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f154,f1238,f169])).

fof(f2263,plain,
    ( ~ spl5_367
    | ~ spl5_46
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2245,f1237,f320,f2261])).

fof(f2261,plain,
    ( spl5_367
  <=> ~ r1_tarski(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_367])])).

fof(f2245,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_46
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f321,f1238,f169])).

fof(f2256,plain,
    ( ~ spl5_365
    | ~ spl5_38
    | ~ spl5_200 ),
    inference(avatar_split_clause,[],[f2246,f1237,f277,f2254])).

fof(f2254,plain,
    ( spl5_365
  <=> ~ r1_tarski(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_365])])).

fof(f2246,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_38
    | ~ spl5_200 ),
    inference(unit_resulting_resolution,[],[f278,f1238,f169])).

fof(f2225,plain,
    ( spl5_362
    | spl5_201 ),
    inference(avatar_split_clause,[],[f2201,f1240,f2223])).

fof(f2223,plain,
    ( spl5_362
  <=> r2_hidden(sK3(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_362])])).

fof(f2201,plain,
    ( r2_hidden(sK3(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f60,f1241,f63])).

fof(f2218,plain,
    ( spl5_360
    | ~ spl5_6
    | spl5_201 ),
    inference(avatar_split_clause,[],[f2202,f1240,f106,f2216])).

fof(f2216,plain,
    ( spl5_360
  <=> v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_360])])).

fof(f2202,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f107,f1241,f64])).

fof(f2211,plain,
    ( ~ spl5_359
    | spl5_201 ),
    inference(avatar_split_clause,[],[f2203,f1240,f2209])).

fof(f2209,plain,
    ( spl5_359
  <=> ~ r2_hidden(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_359])])).

fof(f2203,plain,
    ( ~ r2_hidden(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0),sK3(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f60,f1241,f143])).

fof(f2195,plain,
    ( spl5_344
    | ~ spl5_8
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2194,f779,f115,f2148])).

fof(f779,plain,
    ( spl5_128
  <=> v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f2194,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK1) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_128 ),
    inference(forward_demodulation,[],[f2079,f116])).

fof(f2079,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK1) = k1_xboole_0
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f780,f59])).

fof(f780,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_128 ),
    inference(avatar_component_clause,[],[f779])).

fof(f2193,plain,
    ( spl5_356
    | spl5_21
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2080,f779,f182,f2191])).

fof(f2191,plain,
    ( spl5_356
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_356])])).

fof(f2080,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_21
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f183,f780,f64])).

fof(f2186,plain,
    ( spl5_354
    | spl5_31
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2081,f779,f223,f2184])).

fof(f2184,plain,
    ( spl5_354
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_354])])).

fof(f2081,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_31
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f224,f780,f64])).

fof(f2179,plain,
    ( spl5_352
    | spl5_67
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2082,f779,f410,f2177])).

fof(f2082,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_67
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f411,f780,f64])).

fof(f2172,plain,
    ( spl5_350
    | spl5_27
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2083,f779,f211,f2170])).

fof(f2170,plain,
    ( spl5_350
  <=> v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_350])])).

fof(f2083,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_27
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f212,f780,f64])).

fof(f2165,plain,
    ( spl5_348
    | spl5_29
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2084,f779,f220,f2163])).

fof(f2163,plain,
    ( spl5_348
  <=> v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_348])])).

fof(f2084,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_29
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f221,f780,f64])).

fof(f2158,plain,
    ( spl5_346
    | ~ spl5_128
    | spl5_137 ),
    inference(avatar_split_clause,[],[f2085,f816,f779,f2156])).

fof(f2156,plain,
    ( spl5_346
  <=> v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_346])])).

fof(f2085,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_128
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f780,f64])).

fof(f2151,plain,
    ( spl5_344
    | ~ spl5_6
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2086,f779,f106,f2148])).

fof(f2086,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f107,f780,f70])).

fof(f2150,plain,
    ( spl5_344
    | ~ spl5_6
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2088,f779,f106,f2148])).

fof(f2088,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f107,f780,f70])).

fof(f2143,plain,
    ( ~ spl5_343
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2091,f779,f153,f2141])).

fof(f2141,plain,
    ( spl5_343
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_343])])).

fof(f2091,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f154,f780,f79])).

fof(f2136,plain,
    ( ~ spl5_341
    | ~ spl5_46
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2092,f779,f320,f2134])).

fof(f2134,plain,
    ( spl5_341
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_341])])).

fof(f2092,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_46
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f321,f780,f79])).

fof(f2129,plain,
    ( ~ spl5_339
    | ~ spl5_38
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2093,f779,f277,f2127])).

fof(f2127,plain,
    ( spl5_339
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_339])])).

fof(f2093,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_38
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f278,f780,f79])).

fof(f2122,plain,
    ( ~ spl5_337
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2096,f779,f153,f2120])).

fof(f2120,plain,
    ( spl5_337
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_337])])).

fof(f2096,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_14
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f154,f780,f169])).

fof(f2115,plain,
    ( ~ spl5_335
    | ~ spl5_46
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2097,f779,f320,f2113])).

fof(f2113,plain,
    ( spl5_335
  <=> ~ r1_tarski(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_335])])).

fof(f2097,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_46
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f321,f780,f169])).

fof(f2108,plain,
    ( ~ spl5_333
    | ~ spl5_38
    | ~ spl5_128 ),
    inference(avatar_split_clause,[],[f2098,f779,f277,f2106])).

fof(f2106,plain,
    ( spl5_333
  <=> ~ r1_tarski(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_333])])).

fof(f2098,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_38
    | ~ spl5_128 ),
    inference(unit_resulting_resolution,[],[f278,f780,f169])).

fof(f2078,plain,
    ( spl5_330
    | spl5_129 ),
    inference(avatar_split_clause,[],[f2061,f776,f2076])).

fof(f2071,plain,
    ( spl5_294
    | ~ spl5_6
    | spl5_129 ),
    inference(avatar_split_clause,[],[f2062,f776,f106,f1803])).

fof(f1803,plain,
    ( spl5_294
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_294])])).

fof(f2062,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f107,f777,f64])).

fof(f2070,plain,
    ( ~ spl5_329
    | spl5_129 ),
    inference(avatar_split_clause,[],[f2063,f776,f2068])).

fof(f2068,plain,
    ( spl5_329
  <=> ~ r2_hidden(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_329])])).

fof(f2063,plain,
    ( ~ r2_hidden(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK3(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f60,f777,f143])).

fof(f2027,plain,
    ( spl5_316
    | ~ spl5_8
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2026,f413,f115,f1987])).

fof(f413,plain,
    ( spl5_66
  <=> v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f2026,plain,
    ( k1_funct_2(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f1933,f116])).

fof(f1933,plain,
    ( k1_funct_2(sK0,sK1) = k1_xboole_0
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f414,f59])).

fof(f414,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f413])).

fof(f2025,plain,
    ( spl5_326
    | spl5_21
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1934,f413,f182,f2023])).

fof(f2023,plain,
    ( spl5_326
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_326])])).

fof(f1934,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,sK1)))
    | ~ spl5_21
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f183,f414,f64])).

fof(f2018,plain,
    ( spl5_324
    | spl5_31
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1935,f413,f223,f2016])).

fof(f2016,plain,
    ( spl5_324
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_324])])).

fof(f1935,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_31
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f224,f414,f64])).

fof(f2011,plain,
    ( spl5_322
    | spl5_27
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1936,f413,f211,f2009])).

fof(f2009,plain,
    ( spl5_322
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_322])])).

fof(f1936,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,sK1)))
    | ~ spl5_27
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f212,f414,f64])).

fof(f2004,plain,
    ( spl5_320
    | spl5_29
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1937,f413,f220,f2002])).

fof(f2002,plain,
    ( spl5_320
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_320])])).

fof(f1937,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,sK1)))
    | ~ spl5_29
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f221,f414,f64])).

fof(f1997,plain,
    ( spl5_318
    | ~ spl5_66
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1938,f816,f413,f1995])).

fof(f1995,plain,
    ( spl5_318
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_318])])).

fof(f1938,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,sK1)))
    | ~ spl5_66
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f414,f64])).

fof(f1990,plain,
    ( spl5_316
    | ~ spl5_6
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1939,f413,f106,f1987])).

fof(f1939,plain,
    ( k1_funct_2(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f107,f414,f70])).

fof(f1989,plain,
    ( spl5_316
    | ~ spl5_6
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1941,f413,f106,f1987])).

fof(f1941,plain,
    ( k1_funct_2(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f107,f414,f70])).

fof(f1982,plain,
    ( ~ spl5_315
    | ~ spl5_46
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1945,f413,f320,f1980])).

fof(f1980,plain,
    ( spl5_315
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_315])])).

fof(f1945,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_46
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f321,f414,f79])).

fof(f1975,plain,
    ( ~ spl5_313
    | ~ spl5_38
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1946,f413,f277,f1973])).

fof(f1973,plain,
    ( spl5_313
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_313])])).

fof(f1946,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_38
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f278,f414,f79])).

fof(f1968,plain,
    ( ~ spl5_311
    | ~ spl5_46
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1950,f413,f320,f1966])).

fof(f1966,plain,
    ( spl5_311
  <=> ~ r1_tarski(sK1,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_311])])).

fof(f1950,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK0,sK1))
    | ~ spl5_46
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f321,f414,f169])).

fof(f1961,plain,
    ( ~ spl5_309
    | ~ spl5_38
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f1951,f413,f277,f1959])).

fof(f1959,plain,
    ( spl5_309
  <=> ~ r1_tarski(sK0,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_309])])).

fof(f1951,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK0,sK1))
    | ~ spl5_38
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f278,f414,f169])).

fof(f1932,plain,
    ( spl5_306
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1905,f410,f1930])).

fof(f1930,plain,
    ( spl5_306
  <=> r2_hidden(sK3(k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_306])])).

fof(f1905,plain,
    ( r2_hidden(sK3(k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f60,f411,f63])).

fof(f1925,plain,
    ( spl5_304
    | ~ spl5_6
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1908,f410,f106,f1923])).

fof(f1908,plain,
    ( v1_xboole_0(k1_funct_2(k1_funct_2(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f107,f411,f64])).

fof(f1918,plain,
    ( ~ spl5_303
    | spl5_67 ),
    inference(avatar_split_clause,[],[f1909,f410,f1916])).

fof(f1916,plain,
    ( spl5_303
  <=> ~ r2_hidden(k1_funct_2(sK0,sK1),sK3(k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_303])])).

fof(f1909,plain,
    ( ~ r2_hidden(k1_funct_2(sK0,sK1),sK3(k1_funct_2(sK0,sK1)))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f60,f411,f143])).

fof(f1880,plain,
    ( ~ spl5_301
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31
    | spl5_263 ),
    inference(avatar_split_clause,[],[f1855,f1625,f223,f99,f92,f1878])).

fof(f1878,plain,
    ( spl5_301
  <=> ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_301])])).

fof(f1855,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f100,f224,f93,f1626,f205])).

fof(f1873,plain,
    ( ~ spl5_299
    | ~ spl5_2
    | ~ spl5_4
    | spl5_263 ),
    inference(avatar_split_clause,[],[f1856,f1625,f99,f92,f1871])).

fof(f1871,plain,
    ( spl5_299
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_299])])).

fof(f1856,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f100,f121,f93,f1626,f204])).

fof(f1866,plain,
    ( ~ spl5_297
    | ~ spl5_2
    | ~ spl5_4
    | spl5_263 ),
    inference(avatar_split_clause,[],[f1857,f1625,f99,f92,f1863])).

fof(f1863,plain,
    ( spl5_297
  <=> ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_297])])).

fof(f1857,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f100,f159,f93,f1626,f204])).

fof(f1865,plain,
    ( ~ spl5_297
    | ~ spl5_2
    | ~ spl5_4
    | spl5_263 ),
    inference(avatar_split_clause,[],[f1858,f1625,f99,f92,f1863])).

fof(f1858,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_263 ),
    inference(unit_resulting_resolution,[],[f100,f93,f1626,f75])).

fof(f1835,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f554,f277,f211])).

fof(f554,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f71])).

fof(f1834,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f699,f277,f211])).

fof(f699,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f159,f278,f169])).

fof(f1833,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f558,f277,f211])).

fof(f558,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f278,f71])).

fof(f1832,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1114,f277,f211])).

fof(f1114,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f159,f278,f169])).

fof(f1831,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1107,f277,f211])).

fof(f1107,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f71])).

fof(f1830,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1117,f277,f211])).

fof(f1117,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f278,f71])).

fof(f1829,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1441,f277,f211])).

fof(f1441,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f159,f278,f169])).

fof(f1828,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1444,f277,f211])).

fof(f1444,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(resolution,[],[f278,f71])).

fof(f1827,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1434,f277,f211])).

fof(f1434,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f71])).

fof(f1820,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f417,f296,f106,f211])).

fof(f296,plain,
    ( spl5_43
  <=> o_0_0_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f417,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f297,plain,
    ( o_0_0_xboole_0 != sK0
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f296])).

fof(f1819,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f416,f296,f106,f211])).

fof(f416,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f1818,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1100,f296,f106,f211])).

fof(f1100,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f1817,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1099,f296,f106,f211])).

fof(f1099,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f1816,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1427,f296,f106,f211])).

fof(f1427,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f1815,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1426,f296,f106,f211])).

fof(f1426,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_6
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f107,f297,f70])).

fof(f1814,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f711,f570,f211])).

fof(f570,plain,
    ( spl5_95
  <=> ~ r1_tarski(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f711,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_95 ),
    inference(unit_resulting_resolution,[],[f571,f148])).

fof(f571,plain,
    ( ~ r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f570])).

fof(f1813,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f715,f570,f211])).

fof(f715,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_95 ),
    inference(resolution,[],[f571,f148])).

fof(f1812,plain,
    ( ~ spl5_95
    | spl5_243
    | ~ spl5_252 ),
    inference(avatar_split_clause,[],[f1811,f1581,f1544,f570])).

fof(f1544,plain,
    ( spl5_243
  <=> ~ r1_tarski(sK0,k1_funct_2(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_243])])).

fof(f1581,plain,
    ( spl5_252
  <=> k1_funct_2(sK1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_252])])).

fof(f1811,plain,
    ( ~ r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_243
    | ~ spl5_252 ),
    inference(forward_demodulation,[],[f1545,f1582])).

fof(f1582,plain,
    ( k1_funct_2(sK1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_252 ),
    inference(avatar_component_clause,[],[f1581])).

fof(f1545,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_243 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1810,plain,
    ( spl5_40
    | ~ spl5_252
    | ~ spl5_256 ),
    inference(avatar_split_clause,[],[f1809,f1596,f1581,f284])).

fof(f284,plain,
    ( spl5_40
  <=> v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f1596,plain,
    ( spl5_256
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_256])])).

fof(f1809,plain,
    ( v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_252
    | ~ spl5_256 ),
    inference(forward_demodulation,[],[f1597,f1582])).

fof(f1597,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_256 ),
    inference(avatar_component_clause,[],[f1596])).

fof(f1808,plain,
    ( ~ spl5_295
    | ~ spl5_252
    | spl5_281 ),
    inference(avatar_split_clause,[],[f1801,f1733,f1581,f1806])).

fof(f1806,plain,
    ( spl5_295
  <=> ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_295])])).

fof(f1801,plain,
    ( ~ v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),o_0_0_xboole_0))
    | ~ spl5_252
    | ~ spl5_281 ),
    inference(forward_demodulation,[],[f1734,f1582])).

fof(f1787,plain,
    ( ~ spl5_293
    | ~ spl5_42
    | spl5_123 ),
    inference(avatar_split_clause,[],[f1780,f724,f299,f1785])).

fof(f1785,plain,
    ( spl5_293
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_293])])).

fof(f724,plain,
    ( spl5_123
  <=> ~ m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f1780,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl5_42
    | ~ spl5_123 ),
    inference(forward_demodulation,[],[f725,f300])).

fof(f725,plain,
    ( ~ m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f724])).

fof(f1779,plain,
    ( ~ spl5_291
    | ~ spl5_42
    | spl5_161 ),
    inference(avatar_split_clause,[],[f1772,f972,f299,f1777])).

fof(f1777,plain,
    ( spl5_291
  <=> ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_291])])).

fof(f972,plain,
    ( spl5_161
  <=> ~ v1_xboole_0(k1_funct_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f1772,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,sK2))
    | ~ spl5_42
    | ~ spl5_161 ),
    inference(forward_demodulation,[],[f973,f300])).

fof(f973,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,sK2))
    | ~ spl5_161 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1771,plain,
    ( ~ spl5_289
    | ~ spl5_42
    | spl5_177 ),
    inference(avatar_split_clause,[],[f1764,f1153,f299,f1769])).

fof(f1769,plain,
    ( spl5_289
  <=> ~ r1_tarski(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_289])])).

fof(f1153,plain,
    ( spl5_177
  <=> ~ r1_tarski(sK0,k1_funct_2(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1764,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_42
    | ~ spl5_177 ),
    inference(forward_demodulation,[],[f1154,f300])).

fof(f1154,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_177 ),
    inference(avatar_component_clause,[],[f1153])).

fof(f1763,plain,
    ( ~ spl5_287
    | ~ spl5_42
    | spl5_185 ),
    inference(avatar_split_clause,[],[f1756,f1178,f299,f1761])).

fof(f1761,plain,
    ( spl5_287
  <=> k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_287])])).

fof(f1178,plain,
    ( spl5_185
  <=> k1_funct_2(sK0,o_0_0_xboole_0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f1756,plain,
    ( k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl5_42
    | ~ spl5_185 ),
    inference(forward_demodulation,[],[f1179,f300])).

fof(f1179,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) != o_0_0_xboole_0
    | ~ spl5_185 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f1755,plain,
    ( ~ spl5_285
    | ~ spl5_42
    | spl5_191 ),
    inference(avatar_split_clause,[],[f1748,f1200,f299,f1753])).

fof(f1200,plain,
    ( spl5_191
  <=> ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f1748,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_191 ),
    inference(forward_demodulation,[],[f1201,f300])).

fof(f1201,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_191 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1747,plain,
    ( ~ spl5_283
    | ~ spl5_42
    | spl5_193 ),
    inference(avatar_split_clause,[],[f1740,f1207,f299,f1745])).

fof(f1745,plain,
    ( spl5_283
  <=> ~ v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_283])])).

fof(f1207,plain,
    ( spl5_193
  <=> ~ v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f1740,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_193 ),
    inference(forward_demodulation,[],[f1208,f300])).

fof(f1208,plain,
    ( ~ v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_193 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1738,plain,
    ( spl5_280
    | ~ spl5_42
    | ~ spl5_260 ),
    inference(avatar_split_clause,[],[f1731,f1611,f299,f1736])).

fof(f1730,plain,
    ( ~ spl5_279
    | ~ spl5_42
    | spl5_265 ),
    inference(avatar_split_clause,[],[f1723,f1631,f299,f1728])).

fof(f1723,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl5_42
    | ~ spl5_265 ),
    inference(forward_demodulation,[],[f1632,f300])).

fof(f1722,plain,
    ( spl5_276
    | ~ spl5_42
    | ~ spl5_194 ),
    inference(avatar_split_clause,[],[f1715,f1217,f299,f1720])).

fof(f1217,plain,
    ( spl5_194
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f1715,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_194 ),
    inference(forward_demodulation,[],[f1218,f300])).

fof(f1218,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_194 ),
    inference(avatar_component_clause,[],[f1217])).

fof(f1714,plain,
    ( ~ spl5_275
    | ~ spl5_42
    | spl5_189 ),
    inference(avatar_split_clause,[],[f1707,f1193,f299,f1712])).

fof(f1712,plain,
    ( spl5_275
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_275])])).

fof(f1193,plain,
    ( spl5_189
  <=> ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).

fof(f1707,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_189 ),
    inference(forward_demodulation,[],[f1194,f300])).

fof(f1194,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_189 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1706,plain,
    ( spl5_272
    | ~ spl5_42
    | ~ spl5_186 ),
    inference(avatar_split_clause,[],[f1699,f1189,f299,f1704])).

fof(f1189,plain,
    ( spl5_186
  <=> v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f1699,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl5_42
    | ~ spl5_186 ),
    inference(forward_demodulation,[],[f1190,f300])).

fof(f1190,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_186 ),
    inference(avatar_component_clause,[],[f1189])).

fof(f1698,plain,
    ( spl5_270
    | ~ spl5_42
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1691,f982,f299,f1696])).

fof(f1696,plain,
    ( spl5_270
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_270])])).

fof(f982,plain,
    ( spl5_162
  <=> v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1691,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(o_0_0_xboole_0,sK1),sK2))
    | ~ spl5_42
    | ~ spl5_162 ),
    inference(forward_demodulation,[],[f983,f300])).

fof(f983,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_162 ),
    inference(avatar_component_clause,[],[f982])).

fof(f1686,plain,
    ( spl5_210
    | ~ spl5_14
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1252,f299,f153,f1291])).

fof(f1291,plain,
    ( spl5_210
  <=> r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1252,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_14
    | ~ spl5_42 ),
    inference(superposition,[],[f154,f300])).

fof(f1685,plain,
    ( spl5_206
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1250,f299,f128,f1277])).

fof(f1684,plain,
    ( spl5_204
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1249,f299,f92,f1270])).

fof(f1683,plain,
    ( spl5_128
    | spl5_130
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f774,f299,f92,f782,f779])).

fof(f782,plain,
    ( spl5_130
  <=> ! [X3] :
        ( ~ r2_hidden(sK4(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1)),sK2)
        | r1_tarski(X3,k2_zfmisc_1(o_0_0_xboole_0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f1672,plain,
    ( spl5_268
    | ~ spl5_2
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1671,f960,f299,f92,f1653])).

fof(f1653,plain,
    ( spl5_268
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_268])])).

fof(f1671,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_2
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1249,f961])).

fof(f1669,plain,
    ( spl5_266
    | ~ spl5_14
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1668,f960,f299,f153,f1644])).

fof(f1644,plain,
    ( spl5_266
  <=> r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_266])])).

fof(f1668,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_42
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1252,f961])).

fof(f1663,plain,
    ( ~ spl5_49
    | ~ spl5_156
    | spl5_159 ),
    inference(avatar_split_clause,[],[f1662,f965,f960,f324])).

fof(f1661,plain,
    ( spl5_94
    | ~ spl5_176
    | ~ spl5_184 ),
    inference(avatar_split_clause,[],[f1660,f1181,f1150,f567])).

fof(f1150,plain,
    ( spl5_176
  <=> r1_tarski(sK0,k1_funct_2(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f1181,plain,
    ( spl5_184
  <=> k1_funct_2(sK0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f1660,plain,
    ( r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_176
    | ~ spl5_184 ),
    inference(forward_demodulation,[],[f1151,f1182])).

fof(f1182,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_184 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1151,plain,
    ( r1_tarski(sK0,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_176 ),
    inference(avatar_component_clause,[],[f1150])).

fof(f1657,plain,
    ( ~ spl5_49
    | ~ spl5_184
    | spl5_189 ),
    inference(avatar_split_clause,[],[f1656,f1193,f1181,f324])).

fof(f1656,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_184
    | ~ spl5_189 ),
    inference(forward_demodulation,[],[f1194,f1182])).

fof(f1655,plain,
    ( spl5_268
    | ~ spl5_156
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f1648,f1270,f960,f1653])).

fof(f1648,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,sK1)))
    | ~ spl5_156
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f1271,f961])).

fof(f1646,plain,
    ( spl5_266
    | ~ spl5_156
    | ~ spl5_210 ),
    inference(avatar_split_clause,[],[f1639,f1291,f960,f1644])).

fof(f1639,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,o_0_0_xboole_0))
    | ~ spl5_156
    | ~ spl5_210 ),
    inference(forward_demodulation,[],[f1292,f961])).

fof(f1292,plain,
    ( r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_210 ),
    inference(avatar_component_clause,[],[f1291])).

fof(f1638,plain,
    ( ~ spl5_29
    | ~ spl5_6
    | spl5_37 ),
    inference(avatar_split_clause,[],[f331,f260,f106,f220])).

fof(f260,plain,
    ( spl5_37
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f331,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f107,f261,f70])).

fof(f261,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f260])).

fof(f1637,plain,
    ( ~ spl5_29
    | ~ spl5_6
    | spl5_37 ),
    inference(avatar_split_clause,[],[f330,f260,f106,f220])).

fof(f330,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f107,f261,f70])).

fof(f1636,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_263
    | ~ spl5_265
    | spl5_31
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1635,f960,f223,f1631,f1625,f220,f214])).

fof(f1633,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_263
    | ~ spl5_265
    | spl5_31
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1620,f960,f223,f1631,f1625,f220,f214])).

fof(f1618,plain,
    ( ~ spl5_29
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1462,f320,f220])).

fof(f1462,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f159,f321,f169])).

fof(f1617,plain,
    ( ~ spl5_29
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1455,f320,f220])).

fof(f1455,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f321,f71])).

fof(f1616,plain,
    ( ~ spl5_29
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1465,f320,f220])).

fof(f1465,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_46 ),
    inference(resolution,[],[f321,f71])).

fof(f1615,plain,
    ( spl5_252
    | ~ spl5_8
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1614,f327,f115,f1581])).

fof(f327,plain,
    ( spl5_48
  <=> v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1614,plain,
    ( k1_funct_2(sK1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f1512,f116])).

fof(f1512,plain,
    ( k1_funct_2(sK1,o_0_0_xboole_0) = k1_xboole_0
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f328,f59])).

fof(f328,plain,
    ( v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f327])).

fof(f1613,plain,
    ( spl5_260
    | spl5_21
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1513,f327,f182,f1611])).

fof(f1513,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f183,f328,f64])).

fof(f1606,plain,
    ( spl5_258
    | spl5_31
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1599,f960,f327,f223,f1604])).

fof(f1604,plain,
    ( spl5_258
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_258])])).

fof(f1599,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1514,f961])).

fof(f1514,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f224,f328,f64])).

fof(f1598,plain,
    ( spl5_256
    | spl5_27
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1515,f327,f211,f1596])).

fof(f1515,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_27
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f212,f328,f64])).

fof(f1591,plain,
    ( spl5_254
    | spl5_29
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1516,f327,f220,f1589])).

fof(f1589,plain,
    ( spl5_254
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).

fof(f1516,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_29
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f221,f328,f64])).

fof(f1584,plain,
    ( spl5_252
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1517,f327,f106,f1581])).

fof(f1517,plain,
    ( k1_funct_2(sK1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f107,f328,f70])).

fof(f1583,plain,
    ( spl5_252
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1519,f327,f106,f1581])).

fof(f1519,plain,
    ( k1_funct_2(sK1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f107,f328,f70])).

fof(f1576,plain,
    ( ~ spl5_251
    | ~ spl5_14
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1569,f960,f327,f153,f1574])).

fof(f1574,plain,
    ( spl5_251
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_251])])).

fof(f1569,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1522,f961])).

fof(f1522,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f154,f328,f79])).

fof(f1568,plain,
    ( ~ spl5_249
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1523,f327,f277,f1566])).

fof(f1566,plain,
    ( spl5_249
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_249])])).

fof(f1523,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f278,f328,f79])).

fof(f1561,plain,
    ( ~ spl5_247
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1524,f327,f320,f1559])).

fof(f1559,plain,
    ( spl5_247
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_247])])).

fof(f1524,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_funct_2(sK1,o_0_0_xboole_0)))
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f321,f328,f79])).

fof(f1554,plain,
    ( ~ spl5_245
    | ~ spl5_14
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1547,f960,f327,f153,f1552])).

fof(f1552,plain,
    ( spl5_245
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_245])])).

fof(f1547,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_48
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1527,f961])).

fof(f1527,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f154,f328,f169])).

fof(f1546,plain,
    ( ~ spl5_243
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1528,f327,f277,f1544])).

fof(f1528,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f278,f328,f169])).

fof(f1539,plain,
    ( ~ spl5_241
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1529,f327,f320,f1537])).

fof(f1537,plain,
    ( spl5_241
  <=> ~ r1_tarski(sK1,k1_funct_2(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_241])])).

fof(f1529,plain,
    ( ~ r1_tarski(sK1,k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f321,f328,f169])).

fof(f1511,plain,
    ( spl5_236
    | ~ spl5_239
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1466,f320,f1509,f1503])).

fof(f1503,plain,
    ( spl5_236
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_236])])).

fof(f1509,plain,
    ( spl5_239
  <=> ~ m1_subset_1(sK1,sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).

fof(f1466,plain,
    ( ~ m1_subset_1(sK1,sK3(sK1))
    | v1_xboole_0(sK3(sK1))
    | ~ spl5_46 ),
    inference(resolution,[],[f321,f143])).

fof(f1498,plain,
    ( ~ spl5_229
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1453,f320,f106,f1474])).

fof(f1453,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f118,f321,f65])).

fof(f1497,plain,
    ( ~ spl5_235
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1454,f320,f106,f1495])).

fof(f1495,plain,
    ( spl5_235
  <=> ~ r1_tarski(sK1,sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).

fof(f1454,plain,
    ( ~ r1_tarski(sK1,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f171,f321,f65])).

fof(f1490,plain,
    ( ~ spl5_233
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1456,f320,f106,f1488])).

fof(f1456,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f107,f321,f79])).

fof(f1483,plain,
    ( ~ spl5_231
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1459,f320,f1481])).

fof(f1481,plain,
    ( spl5_231
  <=> ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).

fof(f1459,plain,
    ( ~ r2_hidden(sK1,sK3(k1_zfmisc_1(sK3(sK1))))
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f121,f321,f168])).

fof(f1476,plain,
    ( ~ spl5_229
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1461,f320,f106,f1474])).

fof(f1461,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f107,f321,f169])).

fof(f1419,plain,
    ( spl5_24
    | ~ spl5_156
    | ~ spl5_162 ),
    inference(avatar_split_clause,[],[f1418,f982,f960,f198])).

fof(f1418,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_156
    | ~ spl5_162 ),
    inference(forward_demodulation,[],[f983,f961])).

fof(f1417,plain,
    ( spl5_24
    | ~ spl5_184
    | ~ spl5_194 ),
    inference(avatar_split_clause,[],[f1416,f1217,f1181,f198])).

fof(f1416,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_184
    | ~ spl5_194 ),
    inference(forward_demodulation,[],[f1218,f1182])).

fof(f1415,plain,
    ( spl5_220
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1414,f179,f115,f1388])).

fof(f1414,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f1348,f116])).

fof(f1348,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f180,f59])).

fof(f180,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f1413,plain,
    ( spl5_226
    | ~ spl5_20
    | spl5_31
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1406,f960,f223,f179,f1411])).

fof(f1406,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_20
    | ~ spl5_31
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1349,f961])).

fof(f1349,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_20
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f224,f180,f64])).

fof(f1405,plain,
    ( spl5_224
    | ~ spl5_20
    | spl5_27 ),
    inference(avatar_split_clause,[],[f1350,f211,f179,f1403])).

fof(f1350,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_20
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f212,f180,f64])).

fof(f1398,plain,
    ( spl5_222
    | ~ spl5_20
    | spl5_29 ),
    inference(avatar_split_clause,[],[f1351,f220,f179,f1396])).

fof(f1351,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_20
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f221,f180,f64])).

fof(f1391,plain,
    ( spl5_220
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1352,f179,f106,f1388])).

fof(f1352,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f107,f180,f70])).

fof(f1390,plain,
    ( spl5_220
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1354,f179,f106,f1388])).

fof(f1354,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f107,f180,f70])).

fof(f1383,plain,
    ( ~ spl5_219
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1376,f960,f179,f153,f1381])).

fof(f1376,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1357,f961])).

fof(f1357,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_14
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f154,f180,f79])).

fof(f1374,plain,
    ( ~ spl5_217
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_156 ),
    inference(avatar_split_clause,[],[f1367,f960,f179,f153,f1372])).

fof(f1367,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,o_0_0_xboole_0),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_14
    | ~ spl5_20
    | ~ spl5_156 ),
    inference(forward_demodulation,[],[f1361,f961])).

fof(f1361,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_14
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f154,f180,f169])).

fof(f1332,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f554,f277,f211])).

fof(f1331,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f699,f277,f211])).

fof(f1330,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f558,f277,f211])).

fof(f1329,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1114,f277,f211])).

fof(f1328,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1107,f277,f211])).

fof(f1327,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1117,f277,f211])).

fof(f1321,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f417,f296,f106,f211])).

fof(f1320,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f416,f296,f106,f211])).

fof(f1319,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1100,f296,f106,f211])).

fof(f1318,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1099,f296,f106,f211])).

fof(f1317,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f711,f570,f211])).

fof(f1316,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f715,f570,f211])).

fof(f1309,plain,
    ( spl5_20
    | spl5_132
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f837,f92,f786,f179])).

fof(f837,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_zfmisc_1(sK0,sK1)),sK2)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f201,f158])).

fof(f1308,plain,
    ( spl5_20
    | spl5_132
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f996,f92,f786,f179])).

fof(f996,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k2_zfmisc_1(sK0,sK1)),sK2)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f201,f158])).

fof(f1307,plain,
    ( ~ spl5_215
    | spl5_31
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1256,f299,f223,f1305])).

fof(f1305,plain,
    ( spl5_215
  <=> ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f1256,plain,
    ( ~ v1_xboole_0(k5_partfun1(o_0_0_xboole_0,sK1,sK2))
    | ~ spl5_31
    | ~ spl5_42 ),
    inference(superposition,[],[f224,f300])).

fof(f1300,plain,
    ( ~ spl5_213
    | spl5_17
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1253,f299,f164,f1298])).

fof(f1298,plain,
    ( spl5_213
  <=> ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f1253,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)),k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_17
    | ~ spl5_42 ),
    inference(superposition,[],[f165,f300])).

fof(f1293,plain,
    ( spl5_210
    | ~ spl5_14
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1252,f299,f153,f1291])).

fof(f1286,plain,
    ( ~ spl5_209
    | spl5_13
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1251,f299,f135,f1284])).

fof(f1284,plain,
    ( spl5_209
  <=> ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f1251,plain,
    ( ~ m1_subset_1(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_zfmisc_1(k1_funct_2(o_0_0_xboole_0,sK1)))
    | ~ spl5_13
    | ~ spl5_42 ),
    inference(superposition,[],[f136,f300])).

fof(f1279,plain,
    ( spl5_206
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1250,f299,f128,f1277])).

fof(f1272,plain,
    ( spl5_204
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1249,f299,f92,f1270])).

fof(f1265,plain,
    ( ~ spl5_203
    | spl5_1
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1248,f299,f85,f1263])).

fof(f1263,plain,
    ( spl5_203
  <=> ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f1248,plain,
    ( ~ r1_tarski(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ spl5_1
    | ~ spl5_42 ),
    inference(superposition,[],[f86,f300])).

fof(f1242,plain,
    ( ~ spl5_201
    | spl5_41
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1235,f299,f281,f1240])).

fof(f1235,plain,
    ( ~ v1_xboole_0(k1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_41
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f282,f300])).

fof(f282,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f281])).

fof(f1234,plain,
    ( ~ spl5_27
    | ~ spl5_5
    | ~ spl5_197
    | spl5_198
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f886,f115,f92,f1232,f1226,f96,f211])).

fof(f1232,plain,
    ( spl5_198
  <=> r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f886,plain,
    ( r2_hidden(sK2,k1_funct_2(o_0_0_xboole_0,sK1))
    | ~ v1_funct_2(sK2,o_0_0_xboole_0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK0)
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f239,f93])).

fof(f1221,plain,
    ( spl5_184
    | ~ spl5_8
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1220,f284,f115,f1181])).

fof(f1220,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f1129,f116])).

fof(f1129,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) = k1_xboole_0
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f285,f59])).

fof(f285,plain,
    ( v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f284])).

fof(f1219,plain,
    ( spl5_194
    | spl5_21
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1130,f284,f182,f1217])).

fof(f1130,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_21
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f183,f285,f64])).

fof(f1212,plain,
    ( spl5_192
    | spl5_31
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1131,f284,f223,f1210])).

fof(f1210,plain,
    ( spl5_192
  <=> v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f1131,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_31
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f224,f285,f64])).

fof(f1205,plain,
    ( spl5_190
    | spl5_27
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1132,f284,f211,f1203])).

fof(f1203,plain,
    ( spl5_190
  <=> v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f1132,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f212,f285,f64])).

fof(f1198,plain,
    ( spl5_188
    | spl5_29
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1133,f284,f220,f1196])).

fof(f1196,plain,
    ( spl5_188
  <=> v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1133,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_29
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f221,f285,f64])).

fof(f1191,plain,
    ( spl5_186
    | ~ spl5_40
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1134,f816,f284,f1189])).

fof(f1134,plain,
    ( v1_xboole_0(k1_funct_2(sK2,k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_40
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f817,f285,f64])).

fof(f1184,plain,
    ( spl5_184
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1135,f284,f106,f1181])).

fof(f1135,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f107,f285,f70])).

fof(f1183,plain,
    ( spl5_184
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1137,f284,f106,f1181])).

fof(f1137,plain,
    ( k1_funct_2(sK0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f107,f285,f70])).

fof(f1176,plain,
    ( ~ spl5_183
    | ~ spl5_14
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1140,f284,f153,f1174])).

fof(f1174,plain,
    ( spl5_183
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f1140,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_14
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f154,f285,f79])).

fof(f1169,plain,
    ( ~ spl5_181
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1141,f284,f277,f1167])).

fof(f1167,plain,
    ( spl5_181
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1141,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_funct_2(sK0,o_0_0_xboole_0)))
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f278,f285,f79])).

fof(f1162,plain,
    ( ~ spl5_179
    | ~ spl5_14
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1144,f284,f153,f1160])).

fof(f1160,plain,
    ( spl5_179
  <=> ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f1144,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_14
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f154,f285,f169])).

fof(f1155,plain,
    ( ~ spl5_177
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1145,f284,f277,f1153])).

fof(f1145,plain,
    ( ~ r1_tarski(sK0,k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_38
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f278,f285,f169])).

fof(f1128,plain,
    ( ~ spl5_175
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1111,f277,f1126])).

fof(f1126,plain,
    ( spl5_175
  <=> ~ r2_hidden(sK0,sK3(k1_zfmisc_1(sK3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f1111,plain,
    ( ~ r2_hidden(sK0,sK3(k1_zfmisc_1(sK3(sK0))))
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f121,f278,f168])).

fof(f1067,plain,
    ( spl5_172
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1050,f223,f99,f92,f1065])).

fof(f1050,plain,
    ( m1_subset_1(sK3(k5_partfun1(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f100,f60,f224,f93,f269])).

fof(f1041,plain,
    ( spl5_30
    | ~ spl5_5
    | spl5_170
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1021,f92,f1039,f96,f226])).

fof(f226,plain,
    ( spl5_30
  <=> v1_xboole_0(k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1039,plain,
    ( spl5_170
  <=> ! [X4] :
        ( v1_funct_2(X4,sK0,sK1)
        | ~ m1_subset_1(X4,k5_partfun1(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f1021,plain,
    ( ! [X4] :
        ( v1_funct_2(X4,sK0,sK1)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
        | ~ m1_subset_1(X4,k5_partfun1(sK0,sK1,sK2)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f241,f93])).

fof(f1037,plain,
    ( ~ spl5_169
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31
    | spl5_33 ),
    inference(avatar_split_clause,[],[f1018,f251,f223,f99,f92,f1035])).

fof(f1018,plain,
    ( ~ m1_subset_1(sK2,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f100,f252,f224,f93,f241])).

fof(f1030,plain,
    ( spl5_166
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1019,f223,f99,f92,f1028])).

fof(f1019,plain,
    ( v1_funct_2(sK3(k5_partfun1(sK0,sK1,sK2)),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f100,f60,f224,f93,f241])).

fof(f1010,plain,
    ( ~ spl5_165
    | ~ spl5_2
    | ~ spl5_4
    | spl5_33 ),
    inference(avatar_split_clause,[],[f998,f251,f99,f92,f1008])).

fof(f998,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k5_partfun1(sK0,sK1,sK2))))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f100,f252,f121,f93,f240])).

fof(f986,plain,
    ( spl5_156
    | ~ spl5_8
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f985,f819,f115,f960])).

fof(f985,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_8
    | ~ spl5_136 ),
    inference(forward_demodulation,[],[f933,f116])).

fof(f933,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f820,f59])).

fof(f820,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_136 ),
    inference(avatar_component_clause,[],[f819])).

fof(f984,plain,
    ( spl5_162
    | spl5_21
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f934,f819,f182,f982])).

fof(f934,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl5_21
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f183,f820,f64])).

fof(f977,plain,
    ( spl5_160
    | spl5_27
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f935,f819,f211,f975])).

fof(f975,plain,
    ( spl5_160
  <=> v1_xboole_0(k1_funct_2(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f935,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK2))
    | ~ spl5_27
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f212,f820,f64])).

fof(f970,plain,
    ( spl5_158
    | spl5_29
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f936,f819,f220,f968])).

fof(f968,plain,
    ( spl5_158
  <=> v1_xboole_0(k1_funct_2(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f936,plain,
    ( v1_xboole_0(k1_funct_2(sK1,sK2))
    | ~ spl5_29
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f221,f820,f64])).

fof(f963,plain,
    ( spl5_156
    | ~ spl5_6
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f937,f819,f106,f960])).

fof(f937,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_6
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f107,f820,f70])).

fof(f962,plain,
    ( spl5_156
    | ~ spl5_6
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f939,f819,f106,f960])).

fof(f939,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl5_6
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f107,f820,f70])).

fof(f955,plain,
    ( ~ spl5_155
    | ~ spl5_14
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f942,f819,f153,f953])).

fof(f942,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(sK2))
    | ~ spl5_14
    | ~ spl5_136 ),
    inference(unit_resulting_resolution,[],[f154,f820,f79])).

fof(f928,plain,
    ( ~ spl5_31
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f452,f153,f223])).

fof(f452,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f71])).

fof(f927,plain,
    ( ~ spl5_31
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f459,f153,f223])).

fof(f459,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f71])).

fof(f926,plain,
    ( ~ spl5_31
    | spl5_1 ),
    inference(avatar_split_clause,[],[f583,f85,f223])).

fof(f583,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f86,f148])).

fof(f925,plain,
    ( ~ spl5_31
    | spl5_1 ),
    inference(avatar_split_clause,[],[f584,f85,f223])).

fof(f584,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f148,f86])).

fof(f924,plain,
    ( ~ spl5_31
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f697,f153,f223])).

fof(f697,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f159,f154,f169])).

fof(f923,plain,
    ( spl5_30
    | ~ spl5_5
    | spl5_152
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f910,f92,f921,f96,f226])).

fof(f921,plain,
    ( spl5_152
  <=> ! [X4] :
        ( v1_funct_1(X4)
        | ~ m1_subset_1(X4,k5_partfun1(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f910,plain,
    ( ! [X4] :
        ( v1_funct_1(X4)
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
        | ~ m1_subset_1(X4,k5_partfun1(sK0,sK1,sK2)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f205,f93])).

fof(f919,plain,
    ( spl5_150
    | ~ spl5_2
    | ~ spl5_4
    | spl5_31 ),
    inference(avatar_split_clause,[],[f908,f223,f99,f92,f917])).

fof(f908,plain,
    ( v1_funct_1(sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f100,f60,f224,f93,f205])).

fof(f907,plain,
    ( ~ spl5_149
    | ~ spl5_81
    | ~ spl5_83
    | spl5_36
    | ~ spl5_8
    | spl5_17 ),
    inference(avatar_split_clause,[],[f891,f164,f115,f263,f490,f483,f905])).

fof(f891,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ r1_tarski(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(resolution,[],[f267,f165])).

fof(f861,plain,
    ( ~ spl5_147
    | spl5_137 ),
    inference(avatar_split_clause,[],[f838,f816,f859])).

fof(f859,plain,
    ( spl5_147
  <=> ~ r2_hidden(sK2,sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f838,plain,
    ( ~ r2_hidden(sK2,sK3(sK2))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f60,f817,f143])).

fof(f854,plain,
    ( spl5_144
    | ~ spl5_6
    | spl5_137 ),
    inference(avatar_split_clause,[],[f839,f816,f106,f852])).

fof(f839,plain,
    ( v1_xboole_0(k1_funct_2(sK2,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f107,f817,f64])).

fof(f847,plain,
    ( spl5_142
    | spl5_137 ),
    inference(avatar_split_clause,[],[f840,f816,f845])).

fof(f845,plain,
    ( spl5_142
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f840,plain,
    ( r2_hidden(sK3(sK2),sK2)
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f60,f817,f63])).

fof(f832,plain,
    ( spl5_140
    | spl5_136
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f813,f176,f819,f830])).

fof(f830,plain,
    ( spl5_140
  <=> ! [X2] : ~ m1_subset_1(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f176,plain,
    ( spl5_18
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f813,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK2)
        | ~ m1_subset_1(X2,sK2) )
    | ~ spl5_18 ),
    inference(resolution,[],[f177,f63])).

fof(f177,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f828,plain,
    ( ~ spl5_139
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f807,f176,f153,f826])).

fof(f807,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK2)
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f154,f177,f65])).

fof(f821,plain,
    ( spl5_136
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f810,f176,f819])).

fof(f810,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f60,f177,f63])).

fof(f802,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f554,f277,f211])).

fof(f801,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f699,f277,f211])).

fof(f800,plain,
    ( ~ spl5_27
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f558,f277,f211])).

fof(f799,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f417,f296,f106,f211])).

fof(f798,plain,
    ( ~ spl5_27
    | ~ spl5_6
    | spl5_43 ),
    inference(avatar_split_clause,[],[f416,f296,f106,f211])).

fof(f797,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f711,f570,f211])).

fof(f796,plain,
    ( ~ spl5_27
    | spl5_95 ),
    inference(avatar_split_clause,[],[f715,f570,f211])).

fof(f795,plain,
    ( ~ spl5_135
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f753,f153,f793])).

fof(f793,plain,
    ( spl5_135
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f753,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f121,f154,f168])).

fof(f788,plain,
    ( spl5_132
    | spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f770,f92,f179,f786])).

fof(f784,plain,
    ( spl5_128
    | spl5_130
    | ~ spl5_2
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f774,f299,f92,f782,f779])).

fof(f765,plain,
    ( ~ spl5_127
    | ~ spl5_14
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f758,f299,f153,f763])).

fof(f763,plain,
    ( spl5_127
  <=> ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK3(k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f758,plain,
    ( ~ r2_hidden(k5_partfun1(o_0_0_xboole_0,sK1,sK2),sK3(k1_zfmisc_1(sK4(k5_partfun1(o_0_0_xboole_0,sK1,sK2),k1_funct_2(o_0_0_xboole_0,sK1)))))
    | ~ spl5_14
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f753,f300])).

fof(f736,plain,
    ( ~ spl5_125
    | spl5_95 ),
    inference(avatar_split_clause,[],[f709,f570,f734])).

fof(f734,plain,
    ( spl5_125
  <=> ~ r2_hidden(sK0,sK4(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f709,plain,
    ( ~ r2_hidden(sK0,sK4(sK0,o_0_0_xboole_0))
    | ~ spl5_95 ),
    inference(unit_resulting_resolution,[],[f571,f147])).

fof(f729,plain,
    ( spl5_122
    | spl5_95 ),
    inference(avatar_split_clause,[],[f710,f570,f727])).

fof(f727,plain,
    ( spl5_122
  <=> m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f710,plain,
    ( m1_subset_1(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl5_95 ),
    inference(unit_resulting_resolution,[],[f571,f146])).

fof(f722,plain,
    ( spl5_120
    | spl5_95 ),
    inference(avatar_split_clause,[],[f713,f570,f720])).

fof(f720,plain,
    ( spl5_120
  <=> r2_hidden(sK4(sK0,o_0_0_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f713,plain,
    ( r2_hidden(sK4(sK0,o_0_0_xboole_0),sK0)
    | ~ spl5_95 ),
    inference(unit_resulting_resolution,[],[f571,f66])).

fof(f678,plain,
    ( spl5_116
    | ~ spl5_119
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f631,f277,f676,f670])).

fof(f676,plain,
    ( spl5_119
  <=> ~ m1_subset_1(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f631,plain,
    ( ~ m1_subset_1(sK0,sK3(sK0))
    | v1_xboole_0(sK3(sK0))
    | ~ spl5_38 ),
    inference(resolution,[],[f143,f278])).

fof(f665,plain,
    ( spl5_112
    | ~ spl5_115
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f630,f153,f663,f657])).

fof(f663,plain,
    ( spl5_115
  <=> ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f630,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | v1_xboole_0(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_14 ),
    inference(resolution,[],[f143,f154])).

fof(f652,plain,
    ( ~ spl5_111
    | spl5_21 ),
    inference(avatar_split_clause,[],[f623,f182,f650])).

fof(f623,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f183,f60,f143])).

fof(f645,plain,
    ( ~ spl5_109
    | spl5_31 ),
    inference(avatar_split_clause,[],[f624,f223,f643])).

fof(f624,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f224,f60,f143])).

fof(f638,plain,
    ( ~ spl5_107
    | spl5_29 ),
    inference(avatar_split_clause,[],[f626,f220,f636])).

fof(f626,plain,
    ( ~ r2_hidden(sK1,sK3(sK1))
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f221,f60,f143])).

fof(f618,plain,
    ( spl5_104
    | spl5_98
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f592,f106,f598,f616])).

fof(f616,plain,
    ( spl5_104
  <=> ! [X2] : ~ m1_subset_1(X2,sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f598,plain,
    ( spl5_98
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f592,plain,
    ( ! [X2] :
        ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X2,sK3(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f171,f63])).

fof(f614,plain,
    ( ~ spl5_103
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f585,f153,f106,f612])).

fof(f585,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f171,f65])).

fof(f607,plain,
    ( ~ spl5_101
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f586,f277,f106,f605])).

fof(f605,plain,
    ( spl5_101
  <=> ~ r1_tarski(sK0,sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f586,plain,
    ( ~ r1_tarski(sK0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f171,f65])).

fof(f600,plain,
    ( spl5_98
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f589,f106,f598])).

fof(f589,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f60,f171,f63])).

fof(f581,plain,
    ( ~ spl5_97
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f557,f277,f577])).

fof(f577,plain,
    ( spl5_97
  <=> ~ r2_hidden(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f557,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl5_38 ),
    inference(resolution,[],[f278,f61])).

fof(f580,plain,
    ( ~ spl5_97
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f549,f277,f577])).

fof(f549,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f61])).

fof(f579,plain,
    ( ~ spl5_97
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f550,f277,f577])).

fof(f550,plain,
    ( ~ r2_hidden(sK0,sK3(sK0))
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f278,f61])).

fof(f572,plain,
    ( ~ spl5_95
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f553,f277,f106,f570])).

fof(f553,plain,
    ( ~ r1_tarski(sK0,o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f118,f278,f65])).

fof(f565,plain,
    ( ~ spl5_93
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f555,f277,f106,f563])).

fof(f555,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f107,f278,f79])).

fof(f548,plain,
    ( ~ spl5_91
    | spl5_35 ),
    inference(avatar_split_clause,[],[f531,f254,f546])).

fof(f531,plain,
    ( ~ r2_hidden(sK2,sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f255,f121,f65])).

fof(f541,plain,
    ( ~ spl5_89
    | spl5_17 ),
    inference(avatar_split_clause,[],[f532,f164,f539])).

fof(f539,plain,
    ( spl5_89
  <=> ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f532,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK3(k1_zfmisc_1(k1_funct_2(sK0,sK1))))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f165,f121,f65])).

fof(f525,plain,
    ( ~ spl5_87
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f513,f153,f106,f523])).

fof(f513,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f118,f65])).

fof(f507,plain,
    ( ~ spl5_79
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f458,f153,f478])).

fof(f478,plain,
    ( spl5_79
  <=> ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f458,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f61])).

fof(f506,plain,
    ( spl5_76
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f457,f153,f471])).

fof(f471,plain,
    ( spl5_76
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f457,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f62])).

fof(f505,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_80
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f456,f153,f486,f89,f96])).

fof(f89,plain,
    ( spl5_3
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f456,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f75])).

fof(f504,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_82
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f455,f153,f493,f89,f96])).

fof(f455,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f76])).

fof(f503,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_84
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f454,f153,f500,f89,f96])).

fof(f500,plain,
    ( spl5_84
  <=> m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f454,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f154,f77])).

fof(f502,plain,
    ( spl5_84
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f445,f153,f99,f92,f500])).

fof(f445,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f100,f93,f154,f77])).

fof(f495,plain,
    ( spl5_82
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f446,f153,f99,f92,f493])).

fof(f446,plain,
    ( v1_funct_2(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f100,f93,f154,f76])).

fof(f488,plain,
    ( spl5_80
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f447,f153,f99,f92,f486])).

fof(f447,plain,
    ( v1_funct_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f100,f93,f154,f75])).

fof(f481,plain,
    ( ~ spl5_79
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f448,f153,f478])).

fof(f448,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f61])).

fof(f480,plain,
    ( ~ spl5_79
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f449,f153,f478])).

fof(f449,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f61])).

fof(f473,plain,
    ( spl5_76
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f450,f153,f471])).

fof(f450,plain,
    ( m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f154,f62])).

fof(f466,plain,
    ( ~ spl5_75
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f453,f153,f106,f464])).

fof(f453,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f107,f154,f79])).

fof(f444,plain,
    ( ~ spl5_73
    | spl5_66
    | spl5_17 ),
    inference(avatar_split_clause,[],[f437,f164,f413,f442])).

fof(f437,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl5_17 ),
    inference(resolution,[],[f165,f63])).

fof(f435,plain,
    ( ~ spl5_71
    | spl5_13 ),
    inference(avatar_split_clause,[],[f419,f135,f433])).

fof(f419,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),sK3(k1_zfmisc_1(k1_zfmisc_1(k1_funct_2(sK0,sK1)))))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f60,f136,f78])).

fof(f428,plain,
    ( ~ spl5_69
    | spl5_13 ),
    inference(avatar_split_clause,[],[f420,f135,f426])).

fof(f420,plain,
    ( ~ r2_hidden(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f136,f62])).

fof(f415,plain,
    ( ~ spl5_65
    | spl5_66
    | spl5_35 ),
    inference(avatar_split_clause,[],[f402,f254,f413,f407])).

fof(f402,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_funct_2(sK0,sK1))
    | ~ spl5_35 ),
    inference(resolution,[],[f255,f63])).

fof(f397,plain,
    ( spl5_56
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f396,f226,f115,f371])).

fof(f371,plain,
    ( spl5_56
  <=> k5_partfun1(sK0,sK1,sK2) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f396,plain,
    ( k5_partfun1(sK0,sK1,sK2) = o_0_0_xboole_0
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f357,f116])).

fof(f357,plain,
    ( k5_partfun1(sK0,sK1,sK2) = k1_xboole_0
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f227,f59])).

fof(f227,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f395,plain,
    ( spl5_62
    | spl5_21
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f358,f226,f182,f393])).

fof(f358,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_21
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f183,f227,f64])).

fof(f388,plain,
    ( spl5_60
    | spl5_27
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f359,f226,f211,f386])).

fof(f359,plain,
    ( v1_xboole_0(k1_funct_2(sK0,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_27
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f212,f227,f64])).

fof(f381,plain,
    ( spl5_58
    | spl5_29
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f360,f226,f220,f379])).

fof(f360,plain,
    ( v1_xboole_0(k1_funct_2(sK1,k5_partfun1(sK0,sK1,sK2)))
    | ~ spl5_29
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f221,f227,f64])).

fof(f374,plain,
    ( spl5_56
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f361,f226,f106,f371])).

fof(f361,plain,
    ( k5_partfun1(sK0,sK1,sK2) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f107,f227,f70])).

fof(f373,plain,
    ( spl5_56
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f363,f226,f106,f371])).

fof(f363,plain,
    ( k5_partfun1(sK0,sK1,sK2) = o_0_0_xboole_0
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f107,f227,f70])).

fof(f356,plain,
    ( spl5_54
    | ~ spl5_6
    | spl5_31 ),
    inference(avatar_split_clause,[],[f341,f223,f106,f354])).

fof(f341,plain,
    ( v1_xboole_0(k1_funct_2(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f107,f224,f64])).

fof(f349,plain,
    ( spl5_52
    | spl5_31 ),
    inference(avatar_split_clause,[],[f342,f223,f347])).

fof(f342,plain,
    ( r2_hidden(sK3(k5_partfun1(sK0,sK1,sK2)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_31 ),
    inference(unit_resulting_resolution,[],[f60,f224,f63])).

fof(f339,plain,
    ( ~ spl5_51
    | ~ spl5_2
    | ~ spl5_4
    | spl5_33 ),
    inference(avatar_split_clause,[],[f332,f251,f99,f92,f337])).

fof(f332,plain,
    ( ~ r2_hidden(sK2,k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f100,f93,f252,f76])).

fof(f329,plain,
    ( spl5_48
    | ~ spl5_6
    | spl5_29 ),
    inference(avatar_split_clause,[],[f314,f220,f106,f327])).

fof(f314,plain,
    ( v1_xboole_0(k1_funct_2(sK1,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f107,f221,f64])).

fof(f322,plain,
    ( spl5_46
    | spl5_29 ),
    inference(avatar_split_clause,[],[f315,f220,f320])).

fof(f315,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f60,f221,f63])).

fof(f311,plain,
    ( spl5_42
    | ~ spl5_8
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f310,f214,f115,f299])).

fof(f310,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_8
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f287,f116])).

fof(f287,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f215,f59])).

fof(f215,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f309,plain,
    ( spl5_44
    | spl5_21
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f288,f214,f182,f307])).

fof(f288,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),sK0))
    | ~ spl5_21
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f183,f215,f64])).

fof(f302,plain,
    ( spl5_42
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f289,f214,f106,f299])).

fof(f289,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f107,f215,f70])).

fof(f301,plain,
    ( spl5_42
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f291,f214,f106,f299])).

fof(f291,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f107,f215,f70])).

fof(f286,plain,
    ( spl5_40
    | ~ spl5_6
    | spl5_27 ),
    inference(avatar_split_clause,[],[f271,f211,f106,f284])).

fof(f271,plain,
    ( v1_xboole_0(k1_funct_2(sK0,o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f107,f212,f64])).

fof(f279,plain,
    ( spl5_38
    | spl5_27 ),
    inference(avatar_split_clause,[],[f272,f211,f277])).

fof(f272,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f60,f212,f63])).

fof(f265,plain,
    ( ~ spl5_5
    | ~ spl5_33
    | spl5_34
    | spl5_36
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f246,f115,f92,f263,f257,f251,f96])).

fof(f257,plain,
    ( spl5_34
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f246,plain,
    ( o_0_0_xboole_0 = sK1
    | r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f243,f116])).

fof(f243,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f93])).

fof(f228,plain,
    ( spl5_26
    | ~ spl5_29
    | ~ spl5_5
    | spl5_30
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f207,f92,f226,f96,f220,f214])).

fof(f207,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f72,f93])).

fof(f200,plain,
    ( spl5_24
    | ~ spl5_6
    | spl5_21 ),
    inference(avatar_split_clause,[],[f185,f182,f106,f198])).

fof(f185,plain,
    ( v1_xboole_0(k1_funct_2(k2_zfmisc_1(sK0,sK1),o_0_0_xboole_0))
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f107,f183,f64])).

fof(f193,plain,
    ( spl5_22
    | spl5_21 ),
    inference(avatar_split_clause,[],[f186,f182,f191])).

fof(f184,plain,
    ( spl5_18
    | ~ spl5_21
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f172,f92,f182,f176])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f79,f93])).

fof(f166,plain,
    ( ~ spl5_17
    | spl5_1 ),
    inference(avatar_split_clause,[],[f156,f85,f164])).

fof(f156,plain,
    ( ~ r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f86,f67])).

fof(f155,plain,
    ( spl5_14
    | spl5_1 ),
    inference(avatar_split_clause,[],[f145,f85,f153])).

fof(f145,plain,
    ( r2_hidden(sK4(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)),k5_partfun1(sK0,sK1,sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f86,f66])).

fof(f138,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f122,f92,f128])).

fof(f122,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f93])).

fof(f137,plain,
    ( ~ spl5_13
    | spl5_1 ),
    inference(avatar_split_clause,[],[f119,f85,f135])).

fof(f119,plain,
    ( ~ m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k1_funct_2(sK0,sK1)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f86,f68])).

fof(f130,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f120,f92,f128])).

fof(f120,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f93,f68])).

fof(f117,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f109,f106,f115])).

fof(f109,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f107,f59])).

fof(f108,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f58,f106])).

fof(f58,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',dt_o_0_0_xboole_0)).

fof(f101,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f55,f99])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => r1_tarski(k5_partfun1(X0,X1,X2),k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t159_funct_2.p',t159_funct_2)).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f56,f92])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f57,f85])).

fof(f57,plain,(
    ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------

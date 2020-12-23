%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t8_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:11 EDT 2019

% Result     : Theorem 2.09s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       : 2892 (13746 expanded)
%              Number of leaves         :  834 (5873 expanded)
%              Depth                    :   22
%              Number of atoms          : 8350 (37465 expanded)
%              Number of equality atoms :   34 ( 231 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f151,f158,f165,f172,f179,f186,f193,f200,f207,f217,f227,f241,f248,f257,f265,f274,f281,f298,f312,f320,f329,f343,f365,f372,f381,f389,f396,f408,f415,f432,f440,f448,f463,f512,f528,f535,f547,f608,f632,f659,f666,f673,f680,f698,f706,f716,f723,f737,f744,f751,f768,f776,f785,f792,f799,f812,f821,f833,f841,f858,f869,f881,f894,f902,f910,f917,f939,f946,f953,f960,f977,f992,f999,f1012,f1023,f1030,f1045,f1052,f1071,f1081,f1091,f1108,f1123,f1130,f1143,f1154,f1161,f1173,f1180,f1193,f1200,f1207,f1217,f1229,f1236,f1243,f1250,f1260,f1263,f1265,f1342,f1397,f1409,f1479,f1486,f1493,f1500,f1521,f1528,f1538,f1589,f1596,f1603,f1620,f1646,f1653,f1660,f1667,f1674,f1681,f1688,f1749,f1756,f1763,f1781,f1794,f1815,f1831,f1838,f1885,f1892,f1908,f1915,f1927,f1934,f1949,f1964,f1971,f1978,f1985,f1992,f1999,f2006,f2013,f2053,f2063,f2113,f2125,f2132,f2148,f2169,f2205,f2212,f2219,f2226,f2250,f2262,f2269,f2276,f2283,f2290,f2319,f2339,f2346,f2357,f2382,f2389,f2396,f2415,f2428,f2435,f2442,f2453,f2464,f2472,f2479,f2486,f2493,f2512,f2519,f2541,f2548,f2568,f2575,f2591,f2598,f2605,f2612,f2619,f2626,f2633,f2640,f2653,f2674,f2681,f2743,f2745,f2793,f2816,f2826,f2828,f2842,f2849,f2856,f2872,f2935,f2942,f2959,f2966,f2973,f2986,f3022,f3029,f3078,f3085,f3092,f3129,f3172,f3179,f3186,f3195,f3202,f3209,f3216,f3267,f3274,f3288,f3298,f3306,f3322,f3340,f3347,f3381,f3388,f3410,f3420,f3427,f3434,f3463,f3472,f3505,f3512,f3539,f3546,f3564,f3591,f3601,f3615,f3622,f3629,f3636,f3643,f3653,f3660,f3667,f3677,f3714,f3739,f3747,f3765,f3772,f3790,f3799,f3806,f3824,f3863,f3870,f3877,f3904,f3911,f3918,f3928,f3935,f3942,f3949,f3956,f3965,f4000,f4007,f4033,f4035,f4037,f4044,f4051,f4083,f4090,f4100,f4107,f4133,f4141,f4148,f4161,f4186,f4193,f4211,f4218,f4225,f4243,f4250,f4257,f4264,f4284,f4291,f4298,f4320,f4329,f4336,f4353,f4360,f4367,f4396,f4420,f4427,f4445,f4454,f4497,f4522,f4529,f4547,f4578,f4596,f4603,f4610,f4617,f4638,f4645,f4652,f4675,f4690,f4697,f4704,f4714,f4721,f4728,f4745,f4752,f4759,f4766,f4782,f4789,f4796,f4809,f4816,f4823,f4835,f4842,f4849,f4856,f4863,f4870,f4883,f4890,f4919,f4926,f4944,f4951,f4958,f4976,f4983,f4990,f4997,f5004,f5026,f5033,f5040,f5065,f5072,f5087,f5094,f5101,f5111,f5118,f5125,f5147,f5172,f5179,f5226,f5236,f5243,f5262,f5269,f5280,f5288,f5311,f5320,f5327,f5360,f5367,f5386,f5397,f5404,f5427,f5434,f5454,f5464,f5471,f5499,f5507,f5514,f5532,f5539,f5546,f5557,f5569,f5576,f5590,f5597,f5643,f5697,f5704,f5728,f5753,f5760,f5779,f5786,f5812,f5823,f5832,f5839,f5846,f5864,f5871,f5878,f5885,f5892,f5901,f6123,f6130,f6137,f6144,f6151,f6158,f6165,f6172,f6179,f6220,f6258,f6265,f6272,f6305,f6339,f6350,f6368,f6375,f6388,f6395,f6402,f6421,f6483,f6490,f6497,f6519,f6560,f6567,f6588,f6599,f6606,f6613,f6620,f6627,f6642,f6653,f6660,f6667,f6674,f6681,f6688,f6695,f6713,f6728,f6735,f6742,f6749,f6756,f6763,f6770,f6777,f6784,f6791,f6798,f6805,f6812,f6819,f6826,f6833,f6840,f6847,f6854,f6875,f6882,f6889,f6896,f6903,f6910,f6917,f6924,f6931,f6938,f6945,f6952,f6973,f6983,f6995,f7008,f7158,f7168,f7329,f7340,f7347,f7354,f7361,f7372,f7379,f7386,f7393,f7400,f7410,f7417,f7424,f7431,f7444,f7495,f7502,f7528,f7535,f7542,f7549,f7562,f7598,f7605,f7661,f7668,f7709,f7716,f7723,f7727,f7734,f7741,f7748,f7755,f7762,f7773,f7810,f7848,f7855,f7864,f7871,f7878,f7891,f7927,f7934,f8002,f8030,f8037,f8044,f8051,f8058,f8068,f8075,f8136,f8296,f8307,f8318,f8328,f8335,f8368,f8375,f8384,f8399,f8408,f8415,f8428,f8486,f8493,f8500,f8507,f8514,f8575,f8582,f8589,f8596,f8603,f8610,f8650,f8657,f8664,f8668,f8697,f8726,f8733,f8740,f8747,f8754,f8761,f8768,f8775,f8782,f8858,f8865,f8892,f9088,f9285,f9292,f9299,f9306,f9317,f9324,f9474,f9541,f9548,f9555,f9562,f9569,f9577,f9584,f9591,f9598,f9605,f9612,f9619,f9626,f9633,f9640,f9647,f9675,f9682,f9689,f9696,f9703,f9713,f9720,f9727,f9734,f9741,f9780,f9787,f9794,f9801,f9808,f9850,f9857,f9864,f9871,f9995,f10042,f10069,f10076,f10134,f10141,f10167,f10178,f10185,f10192,f10199,f10260,f10276,f10480,f10487,f10523,f10530,f10537,f10550,f10560,f10571,f10578,f10585,f10589,f10596,f10623,f10660,f10670,f10699,f10706,f10716,f10740,f10767,f10774,f10839,f10846,f10860,f10876,f10888,f10895,f10902,f10909,f10916,f10964,f10971,f10982,f11006,f11036,f11047,f11057,f11064,f11116,f11167,f11174,f11203,f11210,f11239,f11246,f11253,f11280,f11287,f11304,f11311,f11318,f11325,f11384,f11394,f11526,f11533,f11607,f11614,f11621,f11632,f11636,f11649,f11657,f11664,f11706,f11713,f11764,f11777,f11799,f11806,f11844,f11862,f11869,f11885,f11892,f11899,f11931,f11938,f11945,f11952,f11961,f11968,f11975,f12020,f12027,f12056,f12073,f12080,f12087,f12117,f12124,f12131,f12138,f12145,f12159,f12166,f12173,f12180,f12187,f12195,f12202,f12209,f12216,f12223,f12294,f12298,f12300,f12302,f12304,f12464,f12471,f12487])).

fof(f12487,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | spl9_115
    | spl9_131
    | ~ spl9_140
    | spl9_143
    | ~ spl9_328
    | ~ spl9_380
    | ~ spl9_1534
    | ~ spl9_1536 ),
    inference(avatar_contradiction_clause,[],[f12486])).

fof(f12486,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_140
    | ~ spl9_143
    | ~ spl9_328
    | ~ spl9_380
    | ~ spl9_1534
    | ~ spl9_1536 ),
    inference(subsumption_resolution,[],[f12485,f12480])).

fof(f12480,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_115
    | ~ spl9_131
    | ~ spl9_140
    | ~ spl9_143
    | ~ spl9_328
    | ~ spl9_380
    | ~ spl9_1534 ),
    inference(subsumption_resolution,[],[f12479,f12346])).

fof(f12346,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_328 ),
    inference(forward_demodulation,[],[f12327,f882])).

fof(f882,plain,
    ( k9_eqrel_1(sK0,sK1,sK2) = k11_relat_1(sK1,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f150,f157,f164,f192,f185,f226,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => k9_eqrel_1(X0,X1,X2) = k11_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',redefinition_k9_eqrel_1)).

fof(f226,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl9_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f185,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_10
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f192,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl9_12
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f164,plain,
    ( v8_relat_2(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl9_4
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f157,plain,
    ( v3_relat_2(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_2
  <=> v3_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl9_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f12327,plain,
    ( m1_subset_1(k9_eqrel_1(sK0,sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_328 ),
    inference(unit_resulting_resolution,[],[f192,f3257])).

fof(f3257,plain,
    ( ! [X0] :
        ( m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_328 ),
    inference(subsumption_resolution,[],[f3256,f976])).

fof(f976,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_143 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl9_143
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f3256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_115
    | ~ spl9_328 ),
    inference(subsumption_resolution,[],[f3255,f820])).

fof(f820,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl9_115 ),
    inference(avatar_component_clause,[],[f819])).

fof(f819,plain,
    ( spl9_115
  <=> ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f3255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_328 ),
    inference(subsumption_resolution,[],[f3248,f2388])).

fof(f2388,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_328 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2387,plain,
    ( spl9_328
  <=> m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_328])])).

fof(f3248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m1_subset_1(k9_eqrel_1(sK0,sK1,X0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | v1_xboole_0(k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(resolution,[],[f2332,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',redefinition_m2_subset_1)).

fof(f2332,plain,
    ( ! [X0] :
        ( m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f2331,f150])).

fof(f2331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f2328,f226])).

fof(f2328,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ m1_subset_1(X0,sK0)
        | m2_subset_1(k9_eqrel_1(sK0,sK1,X0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
        | v1_xboole_0(sK0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(resolution,[],[f1038,f185])).

fof(f1038,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ m1_subset_1(X0,X1)
        | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
        | v1_xboole_0(X1) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1035,f157])).

fof(f1035,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ v1_partfun1(sK1,X1)
        | m2_subset_1(k9_eqrel_1(X1,sK1,X0),k1_zfmisc_1(X1),k8_eqrel_1(X1,sK1))
        | ~ v3_relat_2(sK1)
        | v1_xboole_0(X1) )
    | ~ spl9_4 ),
    inference(resolution,[],[f138,f164])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & ~ v1_xboole_0(X0) )
     => m2_subset_1(k9_eqrel_1(X0,X1,X2),k1_zfmisc_1(X0),k8_eqrel_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_k9_eqrel_1)).

fof(f12479,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_131
    | ~ spl9_140
    | ~ spl9_380
    | ~ spl9_1534 ),
    inference(subsumption_resolution,[],[f12478,f380])).

fof(f380,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl9_48
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f12478,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_131
    | ~ spl9_140
    | ~ spl9_380
    | ~ spl9_1534 ),
    inference(subsumption_resolution,[],[f12477,f12473])).

fof(f12473,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_1534 ),
    inference(forward_demodulation,[],[f12472,f882])).

fof(f12472,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_1534 ),
    inference(unit_resulting_resolution,[],[f150,f164,f157,f185,f192,f199,f226,f12463,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r2_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r2_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r2_binop_1(X0,X2,X3)
                   => r2_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t7_filter_1)).

fof(f12463,plain,
    ( r2_binop_1(sK0,sK2,sK3)
    | ~ spl9_1534 ),
    inference(avatar_component_clause,[],[f12462])).

fof(f12462,plain,
    ( spl9_1534
  <=> r2_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1534])])).

fof(f199,plain,
    ( m2_filter_1(sK3,sK0,sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl9_14
  <=> m2_filter_1(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f12477,plain,
    ( ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_131
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(subsumption_resolution,[],[f12476,f959])).

fof(f959,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl9_140 ),
    inference(avatar_component_clause,[],[f958])).

fof(f958,plain,
    ( spl9_140
  <=> v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f12476,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_131
    | ~ spl9_380 ),
    inference(subsumption_resolution,[],[f12474,f2652])).

fof(f2652,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl9_380 ),
    inference(avatar_component_clause,[],[f2651])).

fof(f2651,plain,
    ( spl9_380
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_380])])).

fof(f12474,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,sK2),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_131 ),
    inference(resolution,[],[f909,f4093])).

fof(f4093,plain,
    ( ! [X0,X1] :
        ( r3_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,k8_eqrel_1(sK0,sK1)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f4092,f150])).

fof(f4092,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | v1_xboole_0(sK0)
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | r3_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X1,k8_eqrel_1(sK0,sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f4091,f226])).

fof(f4091,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(sK0,sK0),sK0)
        | v1_xboole_0(sK0)
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | r3_binop_1(k8_eqrel_1(sK0,sK1),X1,k3_filter_1(sK0,sK1,X0))
        | ~ m1_subset_1(X1,k8_eqrel_1(sK0,sK1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(resolution,[],[f2359,f185])).

fof(f2359,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(sK1,X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | ~ r1_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | r3_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | ~ m1_subset_1(X2,k8_eqrel_1(X1,sK1)) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2358,f157])).

fof(f2358,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        | ~ v3_relat_2(sK1)
        | ~ v1_partfun1(sK1,X1)
        | v1_xboole_0(X1)
        | ~ r2_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | ~ r1_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | r3_binop_1(k8_eqrel_1(X1,sK1),X2,k3_filter_1(X1,sK1,X0))
        | ~ m1_subset_1(X2,k8_eqrel_1(X1,sK1)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f1166,f164])).

fof(f1166,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v8_relat_2(X2)
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r2_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r1_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | r3_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X3,k8_eqrel_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f1165,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_k3_filter_1)).

fof(f1165,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r2_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r1_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
      | r3_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X3,k8_eqrel_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f1164,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X0,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v8_relat_2(X2)
      | ~ v3_relat_2(X2)
      | ~ v1_partfun1(X2,X1)
      | v1_xboole_0(X1)
      | ~ r2_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ r1_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(k3_filter_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X1,X2),k8_eqrel_1(X1,X2)),k8_eqrel_1(X1,X2))))
      | r3_binop_1(k8_eqrel_1(X1,X2),X3,k3_filter_1(X1,X2,X0))
      | ~ v1_funct_1(k3_filter_1(X1,X2,X0))
      | ~ m1_subset_1(X3,k8_eqrel_1(X1,X2)) ) ),
    inference(resolution,[],[f140,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | r3_binop_1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_binop_1(X0,X1,X2)
              | ~ r2_binop_1(X0,X1,X2)
              | ~ r1_binop_1(X0,X1,X2) )
            & ( ( r2_binop_1(X0,X1,X2)
                & r1_binop_1(X0,X1,X2) )
              | ~ r3_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r3_binop_1(X0,X1,X2)
          <=> ( r2_binop_1(X0,X1,X2)
              & r1_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',d7_binop_1)).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f909,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_131 ),
    inference(avatar_component_clause,[],[f908])).

fof(f908,plain,
    ( spl9_131
  <=> ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f12485,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_1536 ),
    inference(forward_demodulation,[],[f12483,f882])).

fof(f12483,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_1536 ),
    inference(unit_resulting_resolution,[],[f150,f164,f157,f185,f192,f199,f226,f12470,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r1_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r1_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r1_binop_1(X0,X2,X3)
                   => r1_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t6_filter_1)).

fof(f12470,plain,
    ( r1_binop_1(sK0,sK2,sK3)
    | ~ spl9_1536 ),
    inference(avatar_component_clause,[],[f12469])).

fof(f12469,plain,
    ( spl9_1536
  <=> r1_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1536])])).

fof(f12471,plain,
    ( spl9_1536
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f12422,f2651,f958,f379,f205,f191,f12469])).

fof(f205,plain,
    ( spl9_16
  <=> r3_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f12422,plain,
    ( r1_binop_1(sK0,sK2,sK3)
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f380,f192,f959,f2652,f206,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r1_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f206,plain,
    ( r3_binop_1(sK0,sK2,sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f205])).

fof(f12464,plain,
    ( spl9_1534
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f12421,f2651,f958,f379,f205,f191,f12462])).

fof(f12421,plain,
    ( r2_binop_1(sK0,sK2,sK3)
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f380,f192,f959,f2652,f206,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_binop_1(X0,X1,X2)
      | ~ r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f12304,plain,
    ( spl9_287
    | ~ spl9_302 ),
    inference(avatar_contradiction_clause,[],[f12303])).

fof(f12303,plain,
    ( $false
    | ~ spl9_287
    | ~ spl9_302 ),
    inference(subsumption_resolution,[],[f2240,f2059])).

fof(f2059,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_287 ),
    inference(avatar_component_clause,[],[f2058])).

fof(f2058,plain,
    ( spl9_287
  <=> ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_287])])).

fof(f2240,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_302 ),
    inference(resolution,[],[f2218,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t1_subset)).

fof(f2218,plain,
    ( r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_302 ),
    inference(avatar_component_clause,[],[f2217])).

fof(f2217,plain,
    ( spl9_302
  <=> r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_302])])).

fof(f12302,plain,
    ( spl9_287
    | ~ spl9_302 ),
    inference(avatar_contradiction_clause,[],[f12301])).

fof(f12301,plain,
    ( $false
    | ~ spl9_287
    | ~ spl9_302 ),
    inference(subsumption_resolution,[],[f2235,f2059])).

fof(f2235,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_302 ),
    inference(unit_resulting_resolution,[],[f2218,f117])).

fof(f12300,plain,
    ( spl9_287
    | ~ spl9_328
    | ~ spl9_584 ),
    inference(avatar_contradiction_clause,[],[f12299])).

fof(f12299,plain,
    ( $false
    | ~ spl9_287
    | ~ spl9_328
    | ~ spl9_584 ),
    inference(subsumption_resolution,[],[f2059,f4404])).

fof(f4404,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_328
    | ~ spl9_584 ),
    inference(unit_resulting_resolution,[],[f2388,f4210,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
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
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t4_subset)).

fof(f4210,plain,
    ( r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_584 ),
    inference(avatar_component_clause,[],[f4209])).

fof(f4209,plain,
    ( spl9_584
  <=> r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_584])])).

fof(f12298,plain,
    ( spl9_337
    | ~ spl9_584 ),
    inference(avatar_contradiction_clause,[],[f12297])).

fof(f12297,plain,
    ( $false
    | ~ spl9_337
    | ~ spl9_584 ),
    inference(subsumption_resolution,[],[f2431,f4411])).

fof(f4411,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_584 ),
    inference(resolution,[],[f4210,f117])).

fof(f2431,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_337 ),
    inference(avatar_component_clause,[],[f2430])).

fof(f2430,plain,
    ( spl9_337
  <=> ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).

fof(f12294,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | spl9_233
    | ~ spl9_242
    | ~ spl9_336
    | ~ spl9_380
    | ~ spl9_398
    | ~ spl9_400 ),
    inference(avatar_contradiction_clause,[],[f12293])).

fof(f12293,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_233
    | ~ spl9_242
    | ~ spl9_336
    | ~ spl9_380
    | ~ spl9_398
    | ~ spl9_400 ),
    inference(subsumption_resolution,[],[f12292,f2434])).

fof(f2434,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_336 ),
    inference(avatar_component_clause,[],[f2433])).

fof(f2433,plain,
    ( spl9_336
  <=> m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_336])])).

fof(f12292,plain,
    ( ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_233
    | ~ spl9_242
    | ~ spl9_380
    | ~ spl9_398
    | ~ spl9_400 ),
    inference(subsumption_resolution,[],[f12291,f380])).

fof(f12291,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_233
    | ~ spl9_242
    | ~ spl9_380
    | ~ spl9_398
    | ~ spl9_400 ),
    inference(subsumption_resolution,[],[f12290,f2944])).

fof(f2944,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_398 ),
    inference(forward_demodulation,[],[f2943,f1762])).

fof(f1762,plain,
    ( k9_eqrel_1(sK0,sK1,o_0_0_xboole_0) = k11_relat_1(sK1,o_0_0_xboole_0)
    | ~ spl9_242 ),
    inference(avatar_component_clause,[],[f1761])).

fof(f1761,plain,
    ( spl9_242
  <=> k9_eqrel_1(sK0,sK1,o_0_0_xboole_0) = k11_relat_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f2943,plain,
    ( r1_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_398 ),
    inference(unit_resulting_resolution,[],[f150,f164,f157,f185,f607,f199,f226,f2934,f112])).

fof(f2934,plain,
    ( r1_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_398 ),
    inference(avatar_component_clause,[],[f2933])).

fof(f2933,plain,
    ( spl9_398
  <=> r1_binop_1(sK0,o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_398])])).

fof(f607,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f606])).

fof(f606,plain,
    ( spl9_76
  <=> m1_subset_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f12290,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_233
    | ~ spl9_242
    | ~ spl9_380
    | ~ spl9_400 ),
    inference(subsumption_resolution,[],[f12289,f2952])).

fof(f2952,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_400 ),
    inference(forward_demodulation,[],[f2950,f1762])).

fof(f2950,plain,
    ( r2_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_400 ),
    inference(unit_resulting_resolution,[],[f150,f164,f157,f185,f607,f199,f226,f2941,f111])).

fof(f2941,plain,
    ( r2_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_400 ),
    inference(avatar_component_clause,[],[f2940])).

fof(f2940,plain,
    ( spl9_400
  <=> r2_binop_1(sK0,o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_400])])).

fof(f12289,plain,
    ( ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_140
    | ~ spl9_233
    | ~ spl9_380 ),
    inference(subsumption_resolution,[],[f12288,f959])).

fof(f12288,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_233
    | ~ spl9_380 ),
    inference(subsumption_resolution,[],[f12287,f2652])).

fof(f12287,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_233 ),
    inference(resolution,[],[f4093,f1673])).

fof(f1673,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_233 ),
    inference(avatar_component_clause,[],[f1672])).

fof(f1672,plain,
    ( spl9_233
  <=> ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_233])])).

fof(f12223,plain,
    ( ~ spl9_1533
    | spl9_221
    | ~ spl9_244
    | spl9_409
    | spl9_411
    | ~ spl9_1454 ),
    inference(avatar_split_clause,[],[f11743,f11704,f2981,f2978,f1776,f1601,f12221])).

fof(f12221,plain,
    ( spl9_1533
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1533])])).

fof(f1601,plain,
    ( spl9_221
  <=> ~ v1_xboole_0(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_221])])).

fof(f1776,plain,
    ( spl9_244
  <=> m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f2978,plain,
    ( spl9_409
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_409])])).

fof(f2981,plain,
    ( spl9_411
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_411])])).

fof(f11704,plain,
    ( spl9_1454
  <=> r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1454])])).

fof(f11743,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_221
    | ~ spl9_244
    | ~ spl9_409
    | ~ spl9_411
    | ~ spl9_1454 ),
    inference(unit_resulting_resolution,[],[f2982,f2979,f1602,f1777,f11705,f3684])).

fof(f3684,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_eqrel_1(X3,X1)
      | v1_xboole_0(X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ r2_hidden(X0,X3)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2183,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_m1_eqrel_1)).

fof(f2183,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | v1_xboole_0(X8)
      | v1_xboole_0(X9)
      | m1_subset_1(X7,X9)
      | ~ m1_subset_1(X7,X8)
      | ~ r2_hidden(X8,X10) ) ),
    inference(resolution,[],[f759,f142])).

fof(f759,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X3,X4)
      | v1_xboole_0(X4)
      | v1_xboole_0(X5)
      | m1_subset_1(X3,X5) ) ),
    inference(duplicate_literal_removal,[],[f758])).

fof(f758,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | v1_xboole_0(X4)
      | v1_xboole_0(X5)
      | m1_subset_1(X3,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | v1_xboole_0(X4)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f125,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_m2_subset_1)).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f11705,plain,
    ( r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1454 ),
    inference(avatar_component_clause,[],[f11704])).

fof(f1777,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_244 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f1602,plain,
    ( ~ v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl9_221 ),
    inference(avatar_component_clause,[],[f1601])).

fof(f2979,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_409 ),
    inference(avatar_component_clause,[],[f2978])).

fof(f2982,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_411 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f12216,plain,
    ( ~ spl9_1531
    | spl9_223
    | spl9_333
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11510,f11386,f2413,f1615,f12214])).

fof(f12214,plain,
    ( spl9_1531
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1531])])).

fof(f1615,plain,
    ( spl9_223
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_223])])).

fof(f2413,plain,
    ( spl9_333
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_333])])).

fof(f11386,plain,
    ( spl9_1431
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1431])])).

fof(f11510,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_223
    | ~ spl9_333
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f1616,f2414,f258,f11387,f3689])).

fof(f3689,plain,(
    ! [X21,X19,X20] :
      ( ~ r2_hidden(X19,sK4(X20))
      | v1_xboole_0(X20)
      | m1_subset_1(X21,X20)
      | ~ m1_subset_1(X21,X19)
      | v1_xboole_0(X19) ) ),
    inference(resolution,[],[f2183,f258])).

fof(f11387,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1431 ),
    inference(avatar_component_clause,[],[f11386])).

fof(f258,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f114,f118])).

fof(f114,plain,(
    ! [X0] : m1_eqrel_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] : m1_eqrel_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] : m1_eqrel_1(X1,X0)
     => m1_eqrel_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_eqrel_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',existence_m1_eqrel_1)).

fof(f2414,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_333 ),
    inference(avatar_component_clause,[],[f2413])).

fof(f1616,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_223 ),
    inference(avatar_component_clause,[],[f1615])).

fof(f12209,plain,
    ( ~ spl9_1529
    | spl9_223
    | spl9_333
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11468,f11386,f2413,f1615,f12207])).

fof(f12207,plain,
    ( spl9_1529
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1529])])).

fof(f11468,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_223
    | ~ spl9_333
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f1616,f2414,f258,f11387,f759])).

fof(f12202,plain,
    ( ~ spl9_1527
    | spl9_1421
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11423,f11386,f11302,f12200])).

fof(f12200,plain,
    ( spl9_1527
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK4(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1527])])).

fof(f11302,plain,
    ( spl9_1421
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1421])])).

fof(f11423,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK4(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_1421
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f11303,f115,f11387,f3494])).

fof(f3494,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK4(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f3486,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t5_subset)).

fof(f3486,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(sK4(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK4(X0)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f2189,f142])).

fof(f2189,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,sK4(X22))
      | v1_xboole_0(sK4(X22))
      | v1_xboole_0(k1_zfmisc_1(X22))
      | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ),
    inference(resolution,[],[f759,f258])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',existence_m1_subset_1)).

fof(f11303,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1421 ),
    inference(avatar_component_clause,[],[f11302])).

fof(f12195,plain,
    ( ~ spl9_1525
    | spl9_221
    | spl9_1297
    | spl9_1427 ),
    inference(avatar_split_clause,[],[f11376,f11323,f10031,f1601,f12193])).

fof(f12193,plain,
    ( spl9_1525
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(sK4(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1525])])).

fof(f10031,plain,
    ( spl9_1297
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1297])])).

fof(f11323,plain,
    ( spl9_1427
  <=> ~ m1_subset_1(sK5(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1427])])).

fof(f11376,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(sK4(o_0_0_xboole_0)))))
    | ~ spl9_221
    | ~ spl9_1297
    | ~ spl9_1427 ),
    inference(unit_resulting_resolution,[],[f10032,f115,f1602,f11324,f3690])).

fof(f3690,plain,(
    ! [X24,X23,X22] :
      ( ~ r2_hidden(X22,sK5(k1_zfmisc_1(k1_zfmisc_1(X23))))
      | v1_xboole_0(X23)
      | m1_subset_1(X24,X23)
      | ~ m1_subset_1(X24,X22)
      | v1_xboole_0(X22) ) ),
    inference(resolution,[],[f2183,f115])).

fof(f11324,plain,
    ( ~ m1_subset_1(sK5(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_1427 ),
    inference(avatar_component_clause,[],[f11323])).

fof(f10032,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_1297 ),
    inference(avatar_component_clause,[],[f10031])).

fof(f12187,plain,
    ( ~ spl9_1523
    | spl9_221
    | ~ spl9_1304
    | spl9_1427 ),
    inference(avatar_split_clause,[],[f11372,f11323,f10132,f1601,f12185])).

fof(f12185,plain,
    ( spl9_1523
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1523])])).

fof(f10132,plain,
    ( spl9_1304
  <=> r2_hidden(sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1304])])).

fof(f11372,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))))
    | ~ spl9_221
    | ~ spl9_1304
    | ~ spl9_1427 ),
    inference(unit_resulting_resolution,[],[f10133,f1602,f11324,f3532])).

fof(f3532,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK5(k1_zfmisc_1(X0))))
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(subsumption_resolution,[],[f3525,f143])).

fof(f3525,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK5(k1_zfmisc_1(X0))))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f2192,f142])).

fof(f2192,plain,(
    ! [X26,X25] :
      ( ~ m1_subset_1(X25,sK5(k1_zfmisc_1(X26)))
      | v1_xboole_0(sK5(k1_zfmisc_1(X26)))
      | v1_xboole_0(X26)
      | m1_subset_1(X25,X26) ) ),
    inference(resolution,[],[f759,f115])).

fof(f10133,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl9_1304 ),
    inference(avatar_component_clause,[],[f10132])).

fof(f12180,plain,
    ( ~ spl9_1521
    | spl9_223
    | ~ spl9_1304
    | spl9_1419 ),
    inference(avatar_split_clause,[],[f11340,f11285,f10132,f1615,f12178])).

fof(f12178,plain,
    ( spl9_1521
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1521])])).

fof(f11285,plain,
    ( spl9_1419
  <=> ~ m1_subset_1(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1419])])).

fof(f11340,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_223
    | ~ spl9_1304
    | ~ spl9_1419 ),
    inference(unit_resulting_resolution,[],[f10133,f1616,f11286,f3532])).

fof(f11286,plain,
    ( ~ m1_subset_1(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1419 ),
    inference(avatar_component_clause,[],[f11285])).

fof(f12173,plain,
    ( ~ spl9_1519
    | spl9_221
    | spl9_223
    | spl9_1419 ),
    inference(avatar_split_clause,[],[f11332,f11285,f1615,f1601,f12171])).

fof(f12171,plain,
    ( spl9_1519
  <=> ~ m2_subset_1(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1519])])).

fof(f11332,plain,
    ( ~ m2_subset_1(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_1419 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f11286,f123])).

fof(f12166,plain,
    ( ~ spl9_1517
    | spl9_223
    | spl9_1419 ),
    inference(avatar_split_clause,[],[f11327,f11285,f1615,f12164])).

fof(f12164,plain,
    ( spl9_1517
  <=> ~ r2_hidden(sK5(sK3),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1517])])).

fof(f11327,plain,
    ( ~ r2_hidden(sK5(sK3),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_223
    | ~ spl9_1419 ),
    inference(unit_resulting_resolution,[],[f1616,f115,f11286,f3494])).

fof(f12159,plain,
    ( ~ spl9_1515
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(avatar_split_clause,[],[f10952,f10893,f170,f12157])).

fof(f12157,plain,
    ( spl9_1515
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1515])])).

fof(f170,plain,
    ( spl9_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f10893,plain,
    ( spl9_1374
  <=> r2_hidden(sK5(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1374])])).

fof(f10952,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(unit_resulting_resolution,[],[f10894,f3160])).

fof(f3160,plain,
    ( ! [X15,X16] :
        ( ~ r2_hidden(X16,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X15,X16) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f115])).

fof(f1510,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X1,X2) )
    | ~ spl9_6 ),
    inference(resolution,[],[f355,f142])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f143,f171])).

fof(f171,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f170])).

fof(f10894,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
    | ~ spl9_1374 ),
    inference(avatar_component_clause,[],[f10893])).

fof(f12145,plain,
    ( ~ spl9_1513
    | ~ spl9_6
    | spl9_1371 ),
    inference(avatar_split_clause,[],[f10939,f10874,f170,f12143])).

fof(f12143,plain,
    ( spl9_1513
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1513])])).

fof(f10874,plain,
    ( spl9_1371
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1371])])).

fof(f10939,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK3)))))
    | ~ spl9_6
    | ~ spl9_1371 ),
    inference(unit_resulting_resolution,[],[f10875,f232])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m1_eqrel_1(o_0_0_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f110,f171])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',cc1_eqrel_1)).

fof(f10875,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK3)))))
    | ~ spl9_1371 ),
    inference(avatar_component_clause,[],[f10874])).

fof(f12138,plain,
    ( ~ spl9_1511
    | spl9_1371 ),
    inference(avatar_split_clause,[],[f10921,f10874,f12136])).

fof(f12136,plain,
    ( spl9_1511
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1511])])).

fof(f10921,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK3))))))
    | ~ spl9_1371 ),
    inference(unit_resulting_resolution,[],[f114,f10875,f110])).

fof(f12131,plain,
    ( ~ spl9_1509
    | spl9_221
    | spl9_223
    | spl9_1353 ),
    inference(avatar_split_clause,[],[f10721,f10697,f1615,f1601,f12129])).

fof(f12129,plain,
    ( spl9_1509
  <=> ~ m2_subset_1(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1509])])).

fof(f10697,plain,
    ( spl9_1353
  <=> ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1353])])).

fof(f10721,plain,
    ( ~ m2_subset_1(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_1353 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f10698,f123])).

fof(f10698,plain,
    ( ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1353 ),
    inference(avatar_component_clause,[],[f10697])).

fof(f12124,plain,
    ( ~ spl9_1507
    | spl9_223
    | spl9_1353 ),
    inference(avatar_split_clause,[],[f10717,f10697,f1615,f12122])).

fof(f12122,plain,
    ( spl9_1507
  <=> ~ r2_hidden(sK4(sK3),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1507])])).

fof(f10717,plain,
    ( ~ r2_hidden(sK4(sK3),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_223
    | ~ spl9_1353 ),
    inference(unit_resulting_resolution,[],[f1616,f115,f10698,f3494])).

fof(f12117,plain,
    ( ~ spl9_1505
    | spl9_223
    | spl9_451
    | spl9_723
    | ~ spl9_1152 ),
    inference(avatar_split_clause,[],[f9912,f8491,f5024,f3314,f1615,f12115])).

fof(f12115,plain,
    ( spl9_1505
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1505])])).

fof(f3314,plain,
    ( spl9_451
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_451])])).

fof(f5024,plain,
    ( spl9_723
  <=> ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_723])])).

fof(f8491,plain,
    ( spl9_1152
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1152])])).

fof(f9912,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_223
    | ~ spl9_451
    | ~ spl9_723
    | ~ spl9_1152 ),
    inference(unit_resulting_resolution,[],[f3315,f8492,f115,f5025,f1616,f3684])).

fof(f5025,plain,
    ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_723 ),
    inference(avatar_component_clause,[],[f5024])).

fof(f8492,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_1152 ),
    inference(avatar_component_clause,[],[f8491])).

fof(f3315,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_451 ),
    inference(avatar_component_clause,[],[f3314])).

fof(f12087,plain,
    ( ~ spl9_1503
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11268,f11237,f170,f12085])).

fof(f12085,plain,
    ( spl9_1503
  <=> ~ r2_hidden(sK5(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1503])])).

fof(f11237,plain,
    ( spl9_1410
  <=> r2_hidden(sK5(sK5(sK3)),sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1410])])).

fof(f11268,plain,
    ( ~ r2_hidden(sK5(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f11238,f3160])).

fof(f11238,plain,
    ( r2_hidden(sK5(sK5(sK3)),sK5(sK3))
    | ~ spl9_1410 ),
    inference(avatar_component_clause,[],[f11237])).

fof(f12080,plain,
    ( ~ spl9_1501
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11266,f11237,f10132,f170,f12078])).

fof(f12078,plain,
    ( spl9_1501
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1501])])).

fof(f11266,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f10133,f115,f11238,f3156])).

fof(f3156,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X4,X5)
        | ~ r2_hidden(X3,X4)
        | ~ r2_hidden(X5,X6) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f142])).

fof(f12073,plain,
    ( ~ spl9_1499
    | spl9_231
    | ~ spl9_396
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10634,f10621,f2870,f1665,f12071])).

fof(f12071,plain,
    ( spl9_1499
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1499])])).

fof(f1665,plain,
    ( spl9_231
  <=> ~ v1_funct_1(sK7(o_0_0_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_231])])).

fof(f2870,plain,
    ( spl9_396
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_396])])).

fof(f10621,plain,
    ( spl9_1347
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1347])])).

fof(f10634,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK3),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f10622,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_m2_filter_1)).

fof(f10622,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl9_1347 ),
    inference(avatar_component_clause,[],[f10621])).

fof(f2871,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_396 ),
    inference(avatar_component_clause,[],[f2870])).

fof(f1666,plain,
    ( ~ v1_funct_1(sK7(o_0_0_xboole_0,sK1))
    | ~ spl9_231 ),
    inference(avatar_component_clause,[],[f1665])).

fof(f12056,plain,
    ( ~ spl9_1497
    | ~ spl9_40
    | spl9_231
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10633,f10621,f1665,f327,f12054])).

fof(f12054,plain,
    ( spl9_1497
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1497])])).

fof(f327,plain,
    ( spl9_40
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f10633,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK3),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f10622,f127])).

fof(f328,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f327])).

fof(f12027,plain,
    ( ~ spl9_1495
    | ~ spl9_6
    | spl9_1463 ),
    inference(avatar_split_clause,[],[f11830,f11797,f170,f12025])).

fof(f12025,plain,
    ( spl9_1495
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1495])])).

fof(f11797,plain,
    ( spl9_1463
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1463])])).

fof(f11830,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_6
    | ~ spl9_1463 ),
    inference(unit_resulting_resolution,[],[f11798,f232])).

fof(f11798,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_1463 ),
    inference(avatar_component_clause,[],[f11797])).

fof(f12020,plain,
    ( ~ spl9_1493
    | spl9_1463 ),
    inference(avatar_split_clause,[],[f11812,f11797,f12018])).

fof(f12018,plain,
    ( spl9_1493
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1493])])).

fof(f11812,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | ~ spl9_1463 ),
    inference(unit_resulting_resolution,[],[f114,f11798,f110])).

fof(f11975,plain,
    ( ~ spl9_1491
    | spl9_231
    | ~ spl9_396
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11124,f11105,f2870,f1665,f11973])).

fof(f11973,plain,
    ( spl9_1491
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1491])])).

fof(f11105,plain,
    ( spl9_1399
  <=> ~ v1_xboole_0(sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1399])])).

fof(f11124,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK3),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f11106,f127])).

fof(f11106,plain,
    ( ~ v1_xboole_0(sK5(sK3))
    | ~ spl9_1399 ),
    inference(avatar_component_clause,[],[f11105])).

fof(f11968,plain,
    ( ~ spl9_1489
    | ~ spl9_40
    | spl9_231
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11123,f11105,f1665,f327,f11966])).

fof(f11966,plain,
    ( spl9_1489
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1489])])).

fof(f11123,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK3),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f11106,f127])).

fof(f11961,plain,
    ( ~ spl9_1487
    | ~ spl9_6
    | spl9_1341 ),
    inference(avatar_split_clause,[],[f10826,f10583,f170,f11959])).

fof(f11959,plain,
    ( spl9_1487
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1487])])).

fof(f10583,plain,
    ( spl9_1341
  <=> ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1341])])).

fof(f10826,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | ~ spl9_6
    | ~ spl9_1341 ),
    inference(unit_resulting_resolution,[],[f10584,f232])).

fof(f10584,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | ~ spl9_1341 ),
    inference(avatar_component_clause,[],[f10583])).

fof(f11952,plain,
    ( ~ spl9_1485
    | spl9_1341 ),
    inference(avatar_split_clause,[],[f10805,f10583,f11950])).

fof(f11950,plain,
    ( spl9_1485
  <=> ~ v1_xboole_0(sK4(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1485])])).

fof(f10805,plain,
    ( ~ v1_xboole_0(sK4(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl9_1341 ),
    inference(unit_resulting_resolution,[],[f114,f10584,f110])).

fof(f11945,plain,
    ( ~ spl9_1483
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10609,f10569,f170,f11943])).

fof(f11943,plain,
    ( spl9_1483
  <=> ~ r2_hidden(sK4(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1483])])).

fof(f10569,plain,
    ( spl9_1336
  <=> r2_hidden(sK5(sK4(sK3)),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1336])])).

fof(f10609,plain,
    ( ~ r2_hidden(sK4(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f10570,f3160])).

fof(f10570,plain,
    ( r2_hidden(sK5(sK4(sK3)),sK4(sK3))
    | ~ spl9_1336 ),
    inference(avatar_component_clause,[],[f10569])).

fof(f11938,plain,
    ( ~ spl9_1481
    | spl9_231
    | ~ spl9_396
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10081,f10067,f2870,f1665,f11936])).

fof(f11936,plain,
    ( spl9_1481
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1481])])).

fof(f10067,plain,
    ( spl9_1301
  <=> ~ v1_xboole_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1301])])).

fof(f10081,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK3),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f10068,f127])).

fof(f10068,plain,
    ( ~ v1_xboole_0(sK4(sK3))
    | ~ spl9_1301 ),
    inference(avatar_component_clause,[],[f10067])).

fof(f11931,plain,
    ( ~ spl9_1479
    | ~ spl9_40
    | spl9_231
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10080,f10067,f1665,f327,f11929])).

fof(f11929,plain,
    ( spl9_1479
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1479])])).

fof(f10080,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK3),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f10068,f127])).

fof(f11899,plain,
    ( ~ spl9_1477
    | spl9_221
    | ~ spl9_244
    | spl9_875
    | spl9_877
    | ~ spl9_1454 ),
    inference(avatar_split_clause,[],[f11744,f11704,f6300,f6297,f1776,f1601,f11897])).

fof(f11897,plain,
    ( spl9_1477
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1477])])).

fof(f6297,plain,
    ( spl9_875
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_875])])).

fof(f6300,plain,
    ( spl9_877
  <=> ~ v1_xboole_0(sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_877])])).

fof(f11744,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK5(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_244
    | ~ spl9_875
    | ~ spl9_877
    | ~ spl9_1454 ),
    inference(unit_resulting_resolution,[],[f6301,f6298,f1602,f1777,f11705,f3684])).

fof(f6298,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0))
    | ~ spl9_875 ),
    inference(avatar_component_clause,[],[f6297])).

fof(f6301,plain,
    ( ~ v1_xboole_0(sK5(o_0_0_xboole_0))
    | ~ spl9_877 ),
    inference(avatar_component_clause,[],[f6300])).

fof(f11892,plain,
    ( ~ spl9_1475
    | ~ spl9_6
    | spl9_1407 ),
    inference(avatar_split_clause,[],[f11230,f11201,f170,f11890])).

fof(f11890,plain,
    ( spl9_1475
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1475])])).

fof(f11201,plain,
    ( spl9_1407
  <=> ~ v1_xboole_0(sK4(sK4(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1407])])).

fof(f11230,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK3))))
    | ~ spl9_6
    | ~ spl9_1407 ),
    inference(unit_resulting_resolution,[],[f11202,f232])).

fof(f11202,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK3))))
    | ~ spl9_1407 ),
    inference(avatar_component_clause,[],[f11201])).

fof(f11885,plain,
    ( ~ spl9_1473
    | spl9_1407 ),
    inference(avatar_split_clause,[],[f11212,f11201,f11883])).

fof(f11883,plain,
    ( spl9_1473
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1473])])).

fof(f11212,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK3)))))
    | ~ spl9_1407 ),
    inference(unit_resulting_resolution,[],[f114,f11202,f110])).

fof(f11869,plain,
    ( ~ spl9_1471
    | spl9_1415 ),
    inference(avatar_split_clause,[],[f11835,f11251,f11867])).

fof(f11867,plain,
    ( spl9_1471
  <=> ~ r2_hidden(sK3,sK4(sK5(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1471])])).

fof(f11251,plain,
    ( spl9_1415
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1415])])).

fof(f11835,plain,
    ( ~ r2_hidden(sK3,sK4(sK5(sK5(sK3))))
    | ~ spl9_1415 ),
    inference(unit_resulting_resolution,[],[f258,f11252,f142])).

fof(f11252,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(sK5(sK3))))
    | ~ spl9_1415 ),
    inference(avatar_component_clause,[],[f11251])).

fof(f11862,plain,
    ( ~ spl9_1469
    | spl9_1415 ),
    inference(avatar_split_clause,[],[f11834,f11251,f11860])).

fof(f11860,plain,
    ( spl9_1469
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK5(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1469])])).

fof(f11834,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK5(sK5(sK3))))
    | ~ spl9_1415 ),
    inference(unit_resulting_resolution,[],[f11252,f117])).

fof(f11844,plain,
    ( ~ spl9_1467
    | spl9_1461 ),
    inference(avatar_split_clause,[],[f11786,f11775,f11842])).

fof(f11842,plain,
    ( spl9_1467
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1467])])).

fof(f11775,plain,
    ( spl9_1461
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1461])])).

fof(f11786,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1461 ),
    inference(unit_resulting_resolution,[],[f11776,f117])).

fof(f11776,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1461 ),
    inference(avatar_component_clause,[],[f11775])).

fof(f11806,plain,
    ( ~ spl9_1465
    | ~ spl9_6
    | spl9_1435 ),
    inference(avatar_split_clause,[],[f11553,f11524,f170,f11804])).

fof(f11804,plain,
    ( spl9_1465
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1465])])).

fof(f11524,plain,
    ( spl9_1435
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1435])])).

fof(f11553,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1435 ),
    inference(unit_resulting_resolution,[],[f11525,f232])).

fof(f11525,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_1435 ),
    inference(avatar_component_clause,[],[f11524])).

fof(f11799,plain,
    ( ~ spl9_1463
    | spl9_1435 ),
    inference(avatar_split_clause,[],[f11535,f11524,f11797])).

fof(f11535,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_1435 ),
    inference(unit_resulting_resolution,[],[f114,f11525,f110])).

fof(f11777,plain,
    ( ~ spl9_1461
    | spl9_221
    | ~ spl9_386
    | ~ spl9_1454 ),
    inference(avatar_split_clause,[],[f11755,f11704,f2814,f1601,f11775])).

fof(f2814,plain,
    ( spl9_386
  <=> o_0_0_xboole_0 = sK5(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_386])])).

fof(f11755,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_386
    | ~ spl9_1454 ),
    inference(forward_demodulation,[],[f11732,f2815])).

fof(f2815,plain,
    ( o_0_0_xboole_0 = sK5(sK4(o_0_0_xboole_0))
    | ~ spl9_386 ),
    inference(avatar_component_clause,[],[f2814])).

fof(f11732,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(sK5(sK4(o_0_0_xboole_0))))
    | ~ spl9_221
    | ~ spl9_1454 ),
    inference(unit_resulting_resolution,[],[f115,f1602,f11705,f3067])).

fof(f3067,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X5))
      | ~ m1_subset_1(X5,X6)
      | v1_xboole_0(X6)
      | ~ r2_hidden(X6,X7) ) ),
    inference(subsumption_resolution,[],[f3045,f143])).

fof(f3045,plain,(
    ! [X6,X7,X5] :
      ( v1_xboole_0(X5)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f1863,f142])).

fof(f1863,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f289,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t2_subset)).

fof(f289,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f119,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',antisymmetry_r2_hidden)).

fof(f11764,plain,
    ( ~ spl9_1459
    | spl9_221
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11482,f11386,f1601,f11762])).

fof(f11762,plain,
    ( spl9_1459
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1459])])).

fof(f11482,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f1602,f258,f11387,f1863])).

fof(f11713,plain,
    ( ~ spl9_1457
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11464,f11386,f11711])).

fof(f11711,plain,
    ( spl9_1457
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1457])])).

fof(f11464,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),sK4(o_0_0_xboole_0))
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f258,f11387,f289])).

fof(f11706,plain,
    ( spl9_1454
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11427,f11386,f11704])).

fof(f11427,plain,
    ( r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f258,f11387,f119])).

fof(f11664,plain,
    ( ~ spl9_1453
    | spl9_225
    | spl9_1443 ),
    inference(avatar_split_clause,[],[f11641,f11619,f1644,f11662])).

fof(f11662,plain,
    ( spl9_1453
  <=> ~ m1_subset_1(sK3,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1453])])).

fof(f1644,plain,
    ( spl9_225
  <=> ~ v1_xboole_0(sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_225])])).

fof(f11619,plain,
    ( spl9_1443
  <=> ~ r2_hidden(sK3,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1443])])).

fof(f11641,plain,
    ( ~ m1_subset_1(sK3,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_1443 ),
    inference(unit_resulting_resolution,[],[f1645,f11620,f119])).

fof(f11620,plain,
    ( ~ r2_hidden(sK3,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_1443 ),
    inference(avatar_component_clause,[],[f11619])).

fof(f1645,plain,
    ( ~ v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f11657,plain,
    ( ~ spl9_1451
    | spl9_1429 ),
    inference(avatar_split_clause,[],[f11622,f11382,f11655])).

fof(f11655,plain,
    ( spl9_1451
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1451])])).

fof(f11382,plain,
    ( spl9_1429
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1429])])).

fof(f11622,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_1429 ),
    inference(unit_resulting_resolution,[],[f11383,f117])).

fof(f11383,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_1429 ),
    inference(avatar_component_clause,[],[f11382])).

fof(f11649,plain,
    ( ~ spl9_1449
    | spl9_247
    | spl9_1423 ),
    inference(avatar_split_clause,[],[f11361,f11309,f1792,f11647])).

fof(f11647,plain,
    ( spl9_1449
  <=> ~ m1_subset_1(sK3,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1449])])).

fof(f1792,plain,
    ( spl9_247
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_247])])).

fof(f11309,plain,
    ( spl9_1423
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1423])])).

fof(f11361,plain,
    ( ~ m1_subset_1(sK3,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_247
    | ~ spl9_1423 ),
    inference(unit_resulting_resolution,[],[f1793,f11310,f119])).

fof(f11310,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1423 ),
    inference(avatar_component_clause,[],[f11309])).

fof(f1793,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_247 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f11636,plain,
    ( spl9_1430
    | spl9_1446
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3162,f170,f11634,f11389])).

fof(f11389,plain,
    ( spl9_1430
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1430])])).

fof(f11634,plain,
    ( spl9_1446
  <=> ! [X20,X22,X21] :
        ( ~ r2_hidden(X20,X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(X22))
        | ~ r2_hidden(X21,sK6(X22,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1446])])).

fof(f3162,plain,
    ( ! [X21,X22,X20] :
        ( ~ r2_hidden(X20,X21)
        | ~ r2_hidden(X21,sK6(X22,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(X22))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
        | v1_xboole_0(X22) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f730])).

fof(f730,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f729])).

fof(f729,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f124,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m2_subset_1(sK6(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m2_subset_1(sK6(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f94])).

fof(f94,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_subset_1(X2,X0,X1)
     => m2_subset_1(sK6(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_subset_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ? [X2] : m2_subset_1(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',existence_m2_subset_1)).

fof(f11632,plain,
    ( ~ spl9_1445
    | spl9_223
    | spl9_333
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11483,f11386,f2413,f1615,f11630])).

fof(f11630,plain,
    ( spl9_1445
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1445])])).

fof(f11483,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl9_223
    | ~ spl9_333
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f1616,f2414,f258,f11387,f2181])).

fof(f2181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_eqrel_1(X1,X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(k1_zfmisc_1(X2))
      | m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f759,f118])).

fof(f11621,plain,
    ( ~ spl9_1443
    | spl9_221
    | spl9_1297
    | spl9_1427 ),
    inference(avatar_split_clause,[],[f11375,f11323,f10031,f1601,f11619])).

fof(f11375,plain,
    ( ~ r2_hidden(sK3,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_1297
    | ~ spl9_1427 ),
    inference(unit_resulting_resolution,[],[f10032,f115,f1602,f11324,f3689])).

fof(f11614,plain,
    ( ~ spl9_1441
    | spl9_1421 ),
    inference(avatar_split_clause,[],[f11356,f11302,f11612])).

fof(f11612,plain,
    ( spl9_1441
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1441])])).

fof(f11356,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_1421 ),
    inference(unit_resulting_resolution,[],[f11303,f117])).

fof(f11607,plain,
    ( ~ spl9_1439
    | spl9_1419 ),
    inference(avatar_split_clause,[],[f11331,f11285,f11605])).

fof(f11605,plain,
    ( spl9_1439
  <=> ~ r2_hidden(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1439])])).

fof(f11331,plain,
    ( ~ r2_hidden(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1419 ),
    inference(unit_resulting_resolution,[],[f11286,f117])).

fof(f11533,plain,
    ( ~ spl9_1437
    | ~ spl9_6
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11463,f11386,f170,f11531])).

fof(f11531,plain,
    ( spl9_1437
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1437])])).

fof(f11463,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f11387,f232])).

fof(f11526,plain,
    ( ~ spl9_1435
    | spl9_1431 ),
    inference(avatar_split_clause,[],[f11426,f11386,f11524])).

fof(f11426,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_1431 ),
    inference(unit_resulting_resolution,[],[f114,f11387,f110])).

fof(f11394,plain,
    ( spl9_1430
    | spl9_1432
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3161,f170,f11392,f11389])).

fof(f11392,plain,
    ( spl9_1432
  <=> ! [X18,X17,X19] :
        ( ~ r2_hidden(X17,X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X18,sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1432])])).

fof(f3161,plain,
    ( ! [X19,X17,X18] :
        ( ~ r2_hidden(X17,X18)
        | ~ r2_hidden(X18,sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | v1_xboole_0(X19)
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f708])).

fof(f708,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f707])).

fof(f707,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f123,f126])).

fof(f11384,plain,
    ( ~ spl9_1429
    | spl9_223
    | ~ spl9_1304
    | spl9_1419 ),
    inference(avatar_split_clause,[],[f11326,f11285,f10132,f1615,f11382])).

fof(f11326,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_223
    | ~ spl9_1304
    | ~ spl9_1419 ),
    inference(unit_resulting_resolution,[],[f10133,f1616,f11286,f3494])).

fof(f11325,plain,
    ( ~ spl9_1427
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11269,f11237,f1601,f170,f11323])).

fof(f11269,plain,
    ( ~ m1_subset_1(sK5(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f11238,f4571])).

fof(f4571,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK4(o_0_0_xboole_0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_6
    | ~ spl9_221 ),
    inference(subsumption_resolution,[],[f4569,f1602])).

fof(f4569,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | v1_xboole_0(sK4(o_0_0_xboole_0))
        | ~ m1_subset_1(X1,sK4(o_0_0_xboole_0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f3159,f119])).

fof(f3159,plain,
    ( ! [X14,X13] :
        ( ~ r2_hidden(X14,sK4(o_0_0_xboole_0))
        | ~ r2_hidden(X13,X14) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f258])).

fof(f11318,plain,
    ( ~ spl9_1425
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11267,f11237,f170,f11316])).

fof(f11316,plain,
    ( spl9_1425
  <=> ~ r2_hidden(sK5(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1425])])).

fof(f11267,plain,
    ( ~ r2_hidden(sK5(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f11238,f3159])).

fof(f11311,plain,
    ( ~ spl9_1423
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11265,f11237,f10132,f170,f11309])).

fof(f11265,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f10133,f258,f11238,f3156])).

fof(f11304,plain,
    ( ~ spl9_1421
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11260,f11237,f10132,f170,f11302])).

fof(f11260,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f10133,f11238,f1510])).

fof(f11287,plain,
    ( ~ spl9_1419
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11259,f11237,f170,f11285])).

fof(f11259,plain,
    ( ~ m1_subset_1(sK5(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f11238,f355])).

fof(f11280,plain,
    ( ~ spl9_1417
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(avatar_split_clause,[],[f11264,f11237,f10132,f170,f11278])).

fof(f11278,plain,
    ( spl9_1417
  <=> ~ m1_eqrel_1(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1417])])).

fof(f11264,plain,
    ( ~ m1_eqrel_1(sK3,o_0_0_xboole_0)
    | ~ spl9_6
    | ~ spl9_1304
    | ~ spl9_1410 ),
    inference(unit_resulting_resolution,[],[f10133,f11238,f3155])).

fof(f3155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_eqrel_1(X2,o_0_0_xboole_0)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_6 ),
    inference(resolution,[],[f1510,f118])).

fof(f11253,plain,
    ( ~ spl9_1415
    | ~ spl9_1304
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11144,f11105,f10132,f11251])).

fof(f11144,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK5(sK5(sK3))))
    | ~ spl9_1304
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f10133,f115,f11106,f3067])).

fof(f11246,plain,
    ( ~ spl9_1413
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11140,f11105,f11244])).

fof(f11244,plain,
    ( spl9_1413
  <=> ~ r2_hidden(sK5(sK3),sK5(sK5(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1413])])).

fof(f11140,plain,
    ( ~ r2_hidden(sK5(sK3),sK5(sK5(sK3)))
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f115,f11106,f289])).

fof(f11239,plain,
    ( spl9_1410
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11120,f11105,f11237])).

fof(f11120,plain,
    ( r2_hidden(sK5(sK5(sK3)),sK5(sK3))
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f115,f11106,f119])).

fof(f11210,plain,
    ( ~ spl9_1409
    | ~ spl9_6
    | spl9_1403 ),
    inference(avatar_split_clause,[],[f11194,f11165,f170,f11208])).

fof(f11208,plain,
    ( spl9_1409
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1409])])).

fof(f11165,plain,
    ( spl9_1403
  <=> ~ v1_xboole_0(sK4(sK5(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1403])])).

fof(f11194,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK3)))
    | ~ spl9_6
    | ~ spl9_1403 ),
    inference(unit_resulting_resolution,[],[f11166,f232])).

fof(f11166,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK3)))
    | ~ spl9_1403 ),
    inference(avatar_component_clause,[],[f11165])).

fof(f11203,plain,
    ( ~ spl9_1407
    | spl9_1403 ),
    inference(avatar_split_clause,[],[f11176,f11165,f11201])).

fof(f11176,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK3))))
    | ~ spl9_1403 ),
    inference(unit_resulting_resolution,[],[f114,f11166,f110])).

fof(f11174,plain,
    ( ~ spl9_1405
    | ~ spl9_6
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11138,f11105,f170,f11172])).

fof(f11172,plain,
    ( spl9_1405
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1405])])).

fof(f11138,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK3))
    | ~ spl9_6
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f11106,f232])).

fof(f11167,plain,
    ( ~ spl9_1403
    | spl9_1399 ),
    inference(avatar_split_clause,[],[f11119,f11105,f11165])).

fof(f11119,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK3)))
    | ~ spl9_1399 ),
    inference(unit_resulting_resolution,[],[f114,f11106,f110])).

fof(f11116,plain,
    ( spl9_1398
    | ~ spl9_1401
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10156,f10132,f11114,f11108])).

fof(f11108,plain,
    ( spl9_1398
  <=> v1_xboole_0(sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1398])])).

fof(f11114,plain,
    ( spl9_1401
  <=> ~ m1_subset_1(sK3,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1401])])).

fof(f10156,plain,
    ( ~ m1_subset_1(sK3,sK5(sK3))
    | v1_xboole_0(sK5(sK3))
    | ~ spl9_1304 ),
    inference(resolution,[],[f10133,f289])).

fof(f11064,plain,
    ( ~ spl9_1397
    | ~ spl9_6
    | spl9_1361 ),
    inference(avatar_split_clause,[],[f10794,f10765,f170,f11062])).

fof(f11062,plain,
    ( spl9_1397
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1397])])).

fof(f10765,plain,
    ( spl9_1361
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1361])])).

fof(f10794,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK3))))
    | ~ spl9_6
    | ~ spl9_1361 ),
    inference(unit_resulting_resolution,[],[f10766,f232])).

fof(f10766,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3))))
    | ~ spl9_1361 ),
    inference(avatar_component_clause,[],[f10765])).

fof(f11057,plain,
    ( ~ spl9_1395
    | spl9_1361 ),
    inference(avatar_split_clause,[],[f10776,f10765,f11055])).

fof(f11055,plain,
    ( spl9_1395
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1395])])).

fof(f10776,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK3)))))
    | ~ spl9_1361 ),
    inference(unit_resulting_resolution,[],[f114,f10766,f110])).

fof(f11047,plain,
    ( ~ spl9_1393
    | spl9_221
    | spl9_223
    | spl9_1313 ),
    inference(avatar_split_clause,[],[f10229,f10183,f1615,f1601,f11045])).

fof(f11045,plain,
    ( spl9_1393
  <=> ~ m2_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1393])])).

fof(f10183,plain,
    ( spl9_1313
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1313])])).

fof(f10229,plain,
    ( ~ m2_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_1313 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f10184,f123])).

fof(f10184,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1313 ),
    inference(avatar_component_clause,[],[f10183])).

fof(f11036,plain,
    ( ~ spl9_1391
    | spl9_223
    | spl9_1313 ),
    inference(avatar_split_clause,[],[f10224,f10183,f1615,f11034])).

fof(f11034,plain,
    ( spl9_1391
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1391])])).

fof(f10224,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_223
    | ~ spl9_1313 ),
    inference(unit_resulting_resolution,[],[f1616,f115,f10184,f3494])).

fof(f11006,plain,
    ( ~ spl9_1389
    | spl9_1383 ),
    inference(avatar_split_clause,[],[f10986,f10962,f11004])).

fof(f11004,plain,
    ( spl9_1389
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1389])])).

fof(f10962,plain,
    ( spl9_1383
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1383])])).

fof(f10986,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1383 ),
    inference(unit_resulting_resolution,[],[f10963,f117])).

fof(f10963,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1383 ),
    inference(avatar_component_clause,[],[f10962])).

fof(f10982,plain,
    ( ~ spl9_1387
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1374 ),
    inference(avatar_split_clause,[],[f10953,f10893,f1601,f170,f10980])).

fof(f10980,plain,
    ( spl9_1387
  <=> ~ m1_subset_1(k1_zfmisc_1(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1387])])).

fof(f10953,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1374 ),
    inference(unit_resulting_resolution,[],[f10894,f4571])).

fof(f10971,plain,
    ( ~ spl9_1385
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(avatar_split_clause,[],[f10951,f10893,f170,f10969])).

fof(f10969,plain,
    ( spl9_1385
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1385])])).

fof(f10951,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(unit_resulting_resolution,[],[f10894,f3159])).

fof(f10964,plain,
    ( ~ spl9_1383
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(avatar_split_clause,[],[f10947,f10893,f170,f10962])).

fof(f10947,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1374 ),
    inference(unit_resulting_resolution,[],[f10894,f355])).

fof(f10916,plain,
    ( ~ spl9_1381
    | spl9_1347
    | ~ spl9_1368 ),
    inference(avatar_split_clause,[],[f10864,f10858,f10621,f10914])).

fof(f10914,plain,
    ( spl9_1381
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK5(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1381])])).

fof(f10858,plain,
    ( spl9_1368
  <=> m1_subset_1(sK5(sK4(sK3)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1368])])).

fof(f10864,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK5(sK4(sK3)))
    | ~ spl9_1347
    | ~ spl9_1368 ),
    inference(unit_resulting_resolution,[],[f10622,f10859,f289])).

fof(f10859,plain,
    ( m1_subset_1(sK5(sK4(sK3)),k1_zfmisc_1(sK3))
    | ~ spl9_1368 ),
    inference(avatar_component_clause,[],[f10858])).

fof(f10909,plain,
    ( spl9_1378
    | spl9_1347
    | ~ spl9_1368 ),
    inference(avatar_split_clause,[],[f10863,f10858,f10621,f10907])).

fof(f10907,plain,
    ( spl9_1378
  <=> r2_hidden(sK5(sK4(sK3)),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1378])])).

fof(f10863,plain,
    ( r2_hidden(sK5(sK4(sK3)),k1_zfmisc_1(sK3))
    | ~ spl9_1347
    | ~ spl9_1368 ),
    inference(unit_resulting_resolution,[],[f10622,f10859,f119])).

fof(f10902,plain,
    ( ~ spl9_1377
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10649,f10621,f10900])).

fof(f10900,plain,
    ( spl9_1377
  <=> ~ r2_hidden(k1_zfmisc_1(sK3),sK5(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1377])])).

fof(f10649,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK3),sK5(k1_zfmisc_1(sK3)))
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f115,f10622,f289])).

fof(f10895,plain,
    ( spl9_1374
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10629,f10621,f10893])).

fof(f10629,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f115,f10622,f119])).

fof(f10888,plain,
    ( ~ spl9_1373
    | ~ spl9_6
    | spl9_1323 ),
    inference(avatar_split_clause,[],[f10514,f10478,f170,f10886])).

fof(f10886,plain,
    ( spl9_1373
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1373])])).

fof(f10478,plain,
    ( spl9_1323
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1323])])).

fof(f10514,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK3))))
    | ~ spl9_6
    | ~ spl9_1323 ),
    inference(unit_resulting_resolution,[],[f10479,f232])).

fof(f10479,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK3))))
    | ~ spl9_1323 ),
    inference(avatar_component_clause,[],[f10478])).

fof(f10876,plain,
    ( ~ spl9_1371
    | spl9_1323 ),
    inference(avatar_split_clause,[],[f10496,f10478,f10874])).

fof(f10496,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK3)))))
    | ~ spl9_1323 ),
    inference(unit_resulting_resolution,[],[f114,f10479,f110])).

fof(f10860,plain,
    ( spl9_1368
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10601,f10569,f10858])).

fof(f10601,plain,
    ( m1_subset_1(sK5(sK4(sK3)),k1_zfmisc_1(sK3))
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f258,f10570,f142])).

fof(f10846,plain,
    ( ~ spl9_1367
    | spl9_231
    | ~ spl9_396
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10047,f10031,f2870,f1665,f10844])).

fof(f10844,plain,
    ( spl9_1367
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1367])])).

fof(f10047,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK3,sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f10032,f127])).

fof(f10839,plain,
    ( ~ spl9_1365
    | ~ spl9_40
    | spl9_231
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10046,f10031,f1665,f327,f10837])).

fof(f10837,plain,
    ( spl9_1365
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1365])])).

fof(f10046,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK3,sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f10032,f127])).

fof(f10774,plain,
    ( ~ spl9_1363
    | ~ spl9_6
    | spl9_1349 ),
    inference(avatar_split_clause,[],[f10690,f10658,f170,f10772])).

fof(f10772,plain,
    ( spl9_1363
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1363])])).

fof(f10658,plain,
    ( spl9_1349
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1349])])).

fof(f10690,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK3)))
    | ~ spl9_6
    | ~ spl9_1349 ),
    inference(unit_resulting_resolution,[],[f10659,f232])).

fof(f10659,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK3)))
    | ~ spl9_1349 ),
    inference(avatar_component_clause,[],[f10658])).

fof(f10767,plain,
    ( ~ spl9_1361
    | spl9_1349 ),
    inference(avatar_split_clause,[],[f10672,f10658,f10765])).

fof(f10672,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3))))
    | ~ spl9_1349 ),
    inference(unit_resulting_resolution,[],[f114,f10659,f110])).

fof(f10740,plain,
    ( ~ spl9_1359
    | spl9_1353 ),
    inference(avatar_split_clause,[],[f10720,f10697,f10738])).

fof(f10738,plain,
    ( spl9_1359
  <=> ~ r2_hidden(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1359])])).

fof(f10720,plain,
    ( ~ r2_hidden(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1353 ),
    inference(unit_resulting_resolution,[],[f10698,f117])).

fof(f10716,plain,
    ( ~ spl9_1357
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10610,f10569,f1601,f170,f10714])).

fof(f10714,plain,
    ( spl9_1357
  <=> ~ m1_subset_1(sK4(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1357])])).

fof(f10610,plain,
    ( ~ m1_subset_1(sK4(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f10570,f4571])).

fof(f10706,plain,
    ( ~ spl9_1355
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10608,f10569,f170,f10704])).

fof(f10704,plain,
    ( spl9_1355
  <=> ~ r2_hidden(sK4(sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1355])])).

fof(f10608,plain,
    ( ~ r2_hidden(sK4(sK3),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f10570,f3159])).

fof(f10699,plain,
    ( ~ spl9_1353
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10604,f10569,f170,f10697])).

fof(f10604,plain,
    ( ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f10570,f355])).

fof(f10670,plain,
    ( ~ spl9_1351
    | ~ spl9_6
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10648,f10621,f170,f10668])).

fof(f10668,plain,
    ( spl9_1351
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1351])])).

fof(f10648,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl9_6
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f10622,f232])).

fof(f10660,plain,
    ( ~ spl9_1349
    | spl9_1347 ),
    inference(avatar_split_clause,[],[f10628,f10621,f10658])).

fof(f10628,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK3)))
    | ~ spl9_1347 ),
    inference(unit_resulting_resolution,[],[f114,f10622,f110])).

fof(f10623,plain,
    ( ~ spl9_1347
    | ~ spl9_1336 ),
    inference(avatar_split_clause,[],[f10603,f10569,f10621])).

fof(f10603,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl9_1336 ),
    inference(unit_resulting_resolution,[],[f258,f10570,f143])).

fof(f10596,plain,
    ( ~ spl9_1345
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10154,f10132,f170,f10594])).

fof(f10594,plain,
    ( spl9_1345
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1345])])).

fof(f10154,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(unit_resulting_resolution,[],[f10133,f3160])).

fof(f10589,plain,
    ( spl9_1340
    | spl9_1296
    | spl9_1342
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2865,f2651,f10587,f10034,f10580])).

fof(f10580,plain,
    ( spl9_1340
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1340])])).

fof(f10034,plain,
    ( spl9_1296
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1296])])).

fof(f10587,plain,
    ( spl9_1342
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1342])])).

fof(f2865,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK3)
        | v1_xboole_0(sK3)
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
        | m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) )
    | ~ spl9_380 ),
    inference(resolution,[],[f2652,f759])).

fof(f10585,plain,
    ( ~ spl9_1341
    | ~ spl9_380
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10148,f10132,f2651,f10583])).

fof(f10148,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | ~ spl9_380
    | ~ spl9_1304 ),
    inference(unit_resulting_resolution,[],[f2652,f10133,f143])).

fof(f10578,plain,
    ( ~ spl9_1339
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10095,f10067,f10576])).

fof(f10576,plain,
    ( spl9_1339
  <=> ~ r2_hidden(sK4(sK3),sK5(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1339])])).

fof(f10095,plain,
    ( ~ r2_hidden(sK4(sK3),sK5(sK4(sK3)))
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f115,f10068,f289])).

fof(f10571,plain,
    ( spl9_1336
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10079,f10067,f10569])).

fof(f10079,plain,
    ( r2_hidden(sK5(sK4(sK3)),sK4(sK3))
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f115,f10068,f119])).

fof(f10560,plain,
    ( spl9_1334
    | ~ spl9_396
    | spl9_1297
    | ~ spl9_1328 ),
    inference(avatar_split_clause,[],[f10551,f10528,f10031,f2870,f10558])).

fof(f10558,plain,
    ( spl9_1334
  <=> v1_funct_1(sK7(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1334])])).

fof(f10528,plain,
    ( spl9_1328
  <=> m2_filter_1(sK7(sK3,sK3),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1328])])).

fof(f10551,plain,
    ( v1_funct_1(sK7(sK3,sK3))
    | ~ spl9_396
    | ~ spl9_1297
    | ~ spl9_1328 ),
    inference(unit_resulting_resolution,[],[f10032,f2871,f10529,f127])).

fof(f10529,plain,
    ( m2_filter_1(sK7(sK3,sK3),sK3,sK3)
    | ~ spl9_1328 ),
    inference(avatar_component_clause,[],[f10528])).

fof(f10550,plain,
    ( spl9_1332
    | ~ spl9_40
    | spl9_1297
    | ~ spl9_1326 ),
    inference(avatar_split_clause,[],[f10541,f10521,f10031,f327,f10548])).

fof(f10548,plain,
    ( spl9_1332
  <=> v1_funct_1(sK7(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1332])])).

fof(f10521,plain,
    ( spl9_1326
  <=> m2_filter_1(sK7(sK3,sK1),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1326])])).

fof(f10541,plain,
    ( v1_funct_1(sK7(sK3,sK1))
    | ~ spl9_40
    | ~ spl9_1297
    | ~ spl9_1326 ),
    inference(unit_resulting_resolution,[],[f10032,f328,f10522,f127])).

fof(f10522,plain,
    ( m2_filter_1(sK7(sK3,sK1),sK3,sK1)
    | ~ spl9_1326 ),
    inference(avatar_component_clause,[],[f10521])).

fof(f10537,plain,
    ( ~ spl9_1331
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10062,f10031,f10535])).

fof(f10535,plain,
    ( spl9_1331
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK5(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1331])])).

fof(f10062,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(sK5(sK3))))
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f115,f115,f10032,f3067])).

fof(f10530,plain,
    ( spl9_1328
    | ~ spl9_396
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10054,f10031,f2870,f10528])).

fof(f10054,plain,
    ( m2_filter_1(sK7(sK3,sK3),sK3,sK3)
    | ~ spl9_396
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f2871,f10032,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m2_filter_1(sK7(X0,X1),X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m2_filter_1(sK7(X0,X1),X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f63,f96])).

fof(f96,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
     => m2_filter_1(sK7(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ? [X2] : m2_filter_1(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',existence_m2_filter_1)).

fof(f10523,plain,
    ( spl9_1326
    | ~ spl9_40
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10053,f10031,f327,f10521])).

fof(f10053,plain,
    ( m2_filter_1(sK7(sK3,sK1),sK3,sK1)
    | ~ spl9_40
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f328,f10032,f130])).

fof(f10487,plain,
    ( ~ spl9_1325
    | ~ spl9_6
    | spl9_1309 ),
    inference(avatar_split_clause,[],[f10217,f10165,f170,f10485])).

fof(f10485,plain,
    ( spl9_1325
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1325])])).

fof(f10165,plain,
    ( spl9_1309
  <=> ~ v1_xboole_0(sK4(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1309])])).

fof(f10217,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK3)))
    | ~ spl9_6
    | ~ spl9_1309 ),
    inference(unit_resulting_resolution,[],[f10166,f232])).

fof(f10166,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK3)))
    | ~ spl9_1309 ),
    inference(avatar_component_clause,[],[f10165])).

fof(f10480,plain,
    ( ~ spl9_1323
    | spl9_1309 ),
    inference(avatar_split_clause,[],[f10201,f10165,f10478])).

fof(f10201,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK3))))
    | ~ spl9_1309 ),
    inference(unit_resulting_resolution,[],[f114,f10166,f110])).

fof(f10276,plain,
    ( spl9_1320
    | ~ spl9_1292 ),
    inference(avatar_split_clause,[],[f10220,f9993,f10274])).

fof(f10274,plain,
    ( spl9_1320
  <=> v1_relat_1(k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1320])])).

fof(f9993,plain,
    ( spl9_1292
  <=> m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1292])])).

fof(f10220,plain,
    ( v1_relat_1(k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1292 ),
    inference(unit_resulting_resolution,[],[f9994,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',cc1_relset_1)).

fof(f9994,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ spl9_1292 ),
    inference(avatar_component_clause,[],[f9993])).

fof(f10260,plain,
    ( ~ spl9_1319
    | spl9_1313 ),
    inference(avatar_split_clause,[],[f10228,f10183,f10258])).

fof(f10258,plain,
    ( spl9_1319
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1319])])).

fof(f10228,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1313 ),
    inference(unit_resulting_resolution,[],[f10184,f117])).

fof(f10199,plain,
    ( ~ spl9_1317
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10155,f10132,f1601,f170,f10197])).

fof(f10197,plain,
    ( spl9_1317
  <=> ~ m1_subset_1(sK3,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1317])])).

fof(f10155,plain,
    ( ~ m1_subset_1(sK3,sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1304 ),
    inference(unit_resulting_resolution,[],[f10133,f4571])).

fof(f10192,plain,
    ( ~ spl9_1315
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10153,f10132,f170,f10190])).

fof(f10190,plain,
    ( spl9_1315
  <=> ~ r2_hidden(sK3,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1315])])).

fof(f10153,plain,
    ( ~ r2_hidden(sK3,sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(unit_resulting_resolution,[],[f10133,f3159])).

fof(f10185,plain,
    ( ~ spl9_1313
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(avatar_split_clause,[],[f10149,f10132,f170,f10183])).

fof(f10149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1304 ),
    inference(unit_resulting_resolution,[],[f10133,f355])).

fof(f10178,plain,
    ( ~ spl9_1311
    | ~ spl9_6
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10094,f10067,f170,f10176])).

fof(f10176,plain,
    ( spl9_1311
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1311])])).

fof(f10094,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK3))
    | ~ spl9_6
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f10068,f232])).

fof(f10167,plain,
    ( ~ spl9_1309
    | spl9_1301 ),
    inference(avatar_split_clause,[],[f10078,f10067,f10165])).

fof(f10078,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK3)))
    | ~ spl9_1301 ),
    inference(unit_resulting_resolution,[],[f114,f10068,f110])).

fof(f10141,plain,
    ( ~ spl9_1307
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10061,f10031,f10139])).

fof(f10139,plain,
    ( spl9_1307
  <=> ~ r2_hidden(sK3,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1307])])).

fof(f10061,plain,
    ( ~ r2_hidden(sK3,sK5(sK3))
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f115,f10032,f289])).

fof(f10134,plain,
    ( spl9_1304
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10045,f10031,f10132])).

fof(f10045,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f115,f10032,f119])).

fof(f10076,plain,
    ( ~ spl9_1303
    | ~ spl9_6
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10060,f10031,f170,f10074])).

fof(f10074,plain,
    ( spl9_1303
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1303])])).

fof(f10060,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK3)
    | ~ spl9_6
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f10032,f232])).

fof(f10069,plain,
    ( ~ spl9_1301
    | spl9_1297 ),
    inference(avatar_split_clause,[],[f10044,f10031,f10067])).

fof(f10044,plain,
    ( ~ v1_xboole_0(sK4(sK3))
    | ~ spl9_1297 ),
    inference(unit_resulting_resolution,[],[f114,f10032,f110])).

fof(f10042,plain,
    ( ~ spl9_1295
    | spl9_1296
    | spl9_1298
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f3058,f2651,f10040,f10034,f10028])).

fof(f10028,plain,
    ( spl9_1295
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1295])])).

fof(f10040,plain,
    ( spl9_1298
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1298])])).

fof(f3058,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),sK3)
    | ~ spl9_380 ),
    inference(resolution,[],[f1863,f2652])).

fof(f9995,plain,
    ( spl9_1292
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2863,f2651,f958,f379,f225,f184,f163,f156,f149,f9993])).

fof(f2863,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f150,f380,f157,f164,f185,f226,f959,f2652,f141])).

fof(f9871,plain,
    ( ~ spl9_1291
    | spl9_1221 ),
    inference(avatar_split_clause,[],[f9476,f9472,f9869])).

fof(f9869,plain,
    ( spl9_1291
  <=> ~ r2_hidden(sK0,sK4(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1291])])).

fof(f9472,plain,
    ( spl9_1221
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1221])])).

fof(f9476,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0)))))
    | ~ spl9_1221 ),
    inference(unit_resulting_resolution,[],[f258,f9473,f142])).

fof(f9473,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0)))))
    | ~ spl9_1221 ),
    inference(avatar_component_clause,[],[f9472])).

fof(f9864,plain,
    ( ~ spl9_1289
    | spl9_1221 ),
    inference(avatar_split_clause,[],[f9475,f9472,f9862])).

fof(f9862,plain,
    ( spl9_1289
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1289])])).

fof(f9475,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0)))))
    | ~ spl9_1221 ),
    inference(unit_resulting_resolution,[],[f9473,f117])).

fof(f9857,plain,
    ( ~ spl9_1287
    | ~ spl9_42
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f9372,f4636,f1615,f341,f9855])).

fof(f9855,plain,
    ( spl9_1287
  <=> ~ m1_subset_1(sK8,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1287])])).

fof(f341,plain,
    ( spl9_42
  <=> r2_hidden(sK5(sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f4636,plain,
    ( spl9_647
  <=> ~ m1_subset_1(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_647])])).

fof(f9372,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_42
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f342,f1616,f4637,f3532])).

fof(f4637,plain,
    ( ~ m1_subset_1(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_647 ),
    inference(avatar_component_clause,[],[f4636])).

fof(f342,plain,
    ( r2_hidden(sK5(sK8),sK8)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f341])).

fof(f9850,plain,
    ( ~ spl9_1285
    | spl9_223
    | ~ spl9_458
    | spl9_723 ),
    inference(avatar_split_clause,[],[f9371,f5024,f3379,f1615,f9848])).

fof(f9848,plain,
    ( spl9_1285
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1285])])).

fof(f3379,plain,
    ( spl9_458
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_458])])).

fof(f9371,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_223
    | ~ spl9_458
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f3380,f1616,f5025,f3532])).

fof(f3380,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl9_458 ),
    inference(avatar_component_clause,[],[f3379])).

fof(f9808,plain,
    ( ~ spl9_1283
    | ~ spl9_38
    | spl9_223
    | spl9_599 ),
    inference(avatar_split_clause,[],[f9369,f4282,f1615,f318,f9806])).

fof(f9806,plain,
    ( spl9_1283
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1283])])).

fof(f318,plain,
    ( spl9_38
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f4282,plain,
    ( spl9_599
  <=> ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_599])])).

fof(f9369,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_38
    | ~ spl9_223
    | ~ spl9_599 ),
    inference(unit_resulting_resolution,[],[f319,f1616,f4283,f3532])).

fof(f4283,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_599 ),
    inference(avatar_component_clause,[],[f4282])).

fof(f319,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f9801,plain,
    ( ~ spl9_1281
    | spl9_1025 ),
    inference(avatar_split_clause,[],[f8812,f7384,f9799])).

fof(f9799,plain,
    ( spl9_1281
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1281])])).

fof(f7384,plain,
    ( spl9_1025
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1025])])).

fof(f8812,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1025 ),
    inference(unit_resulting_resolution,[],[f7385,f117])).

fof(f7385,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1025 ),
    inference(avatar_component_clause,[],[f7384])).

fof(f9794,plain,
    ( ~ spl9_1279
    | spl9_1023 ),
    inference(avatar_split_clause,[],[f8801,f7377,f9792])).

fof(f9792,plain,
    ( spl9_1279
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1279])])).

fof(f7377,plain,
    ( spl9_1023
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1023])])).

fof(f8801,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1023 ),
    inference(unit_resulting_resolution,[],[f7378,f117])).

fof(f7378,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1023 ),
    inference(avatar_component_clause,[],[f7377])).

fof(f9787,plain,
    ( ~ spl9_1277
    | spl9_149
    | spl9_223
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7485,f7439,f1615,f1010,f9785])).

fof(f9785,plain,
    ( spl9_1277
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1277])])).

fof(f1010,plain,
    ( spl9_149
  <=> ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f7439,plain,
    ( spl9_1041
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1041])])).

fof(f7485,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_149
    | ~ spl9_223
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f1616,f258,f1011,f258,f7440,f2183])).

fof(f7440,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_1041 ),
    inference(avatar_component_clause,[],[f7439])).

fof(f1011,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f1010])).

fof(f9780,plain,
    ( ~ spl9_1275
    | spl9_149
    | spl9_223
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7472,f7439,f1615,f1010,f9778])).

fof(f9778,plain,
    ( spl9_1275
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1275])])).

fof(f7472,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_149
    | ~ spl9_223
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f1616,f1011,f258,f7440,f759])).

fof(f9741,plain,
    ( ~ spl9_1273
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(avatar_split_clause,[],[f6505,f6481,f170,f9739])).

fof(f9739,plain,
    ( spl9_1273
  <=> ~ r2_hidden(sK5(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1273])])).

fof(f6481,plain,
    ( spl9_894
  <=> r2_hidden(sK5(sK5(o_0_0_xboole_0)),sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_894])])).

fof(f6505,plain,
    ( ~ r2_hidden(sK5(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(unit_resulting_resolution,[],[f115,f6482,f1510])).

fof(f6482,plain,
    ( r2_hidden(sK5(sK5(o_0_0_xboole_0)),sK5(o_0_0_xboole_0))
    | ~ spl9_894 ),
    inference(avatar_component_clause,[],[f6481])).

fof(f9734,plain,
    ( ~ spl9_1271
    | ~ spl9_6
    | spl9_771 ),
    inference(avatar_split_clause,[],[f5377,f5358,f170,f9732])).

fof(f9732,plain,
    ( spl9_1271
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1271])])).

fof(f5358,plain,
    ( spl9_771
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_771])])).

fof(f5377,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK1)))))
    | ~ spl9_6
    | ~ spl9_771 ),
    inference(unit_resulting_resolution,[],[f5359,f232])).

fof(f5359,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK1)))))
    | ~ spl9_771 ),
    inference(avatar_component_clause,[],[f5358])).

fof(f9727,plain,
    ( ~ spl9_1269
    | spl9_771 ),
    inference(avatar_split_clause,[],[f5369,f5358,f9725])).

fof(f9725,plain,
    ( spl9_1269
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1269])])).

fof(f5369,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK1))))))
    | ~ spl9_771 ),
    inference(unit_resulting_resolution,[],[f114,f5359,f110])).

fof(f9720,plain,
    ( ~ spl9_1267
    | spl9_223
    | spl9_451
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5056,f5024,f3314,f1615,f9718])).

fof(f9718,plain,
    ( spl9_1267
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1267])])).

fof(f5056,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_223
    | ~ spl9_451
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f3315,f1616,f115,f115,f5025,f2183])).

fof(f9713,plain,
    ( ~ spl9_1265
    | spl9_223
    | spl9_449
    | ~ spl9_484
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5055,f5024,f3589,f3308,f1615,f9711])).

fof(f9711,plain,
    ( spl9_1265
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1265])])).

fof(f3308,plain,
    ( spl9_449
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_449])])).

fof(f3589,plain,
    ( spl9_484
  <=> m1_subset_1(sK5(sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_484])])).

fof(f5055,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_223
    | ~ spl9_449
    | ~ spl9_484
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f1616,f3309,f3590,f258,f5025,f2183])).

fof(f3590,plain,
    ( m1_subset_1(sK5(sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_484 ),
    inference(avatar_component_clause,[],[f3589])).

fof(f3309,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl9_449 ),
    inference(avatar_component_clause,[],[f3308])).

fof(f9703,plain,
    ( ~ spl9_1263
    | spl9_221
    | spl9_223
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5046,f5024,f1615,f1601,f9701])).

fof(f9701,plain,
    ( spl9_1263
  <=> ~ m2_subset_1(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1263])])).

fof(f5046,plain,
    ( ~ m2_subset_1(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f5025,f123])).

fof(f9696,plain,
    ( ~ spl9_1261
    | spl9_9
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4667,f4636,f1615,f177,f9694])).

fof(f9694,plain,
    ( spl9_1261
  <=> ~ r2_hidden(sK8,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1261])])).

fof(f177,plain,
    ( spl9_9
  <=> ~ v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f4667,plain,
    ( ~ r2_hidden(sK8,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_9
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f178,f1616,f115,f115,f4637,f2183])).

fof(f178,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f9689,plain,
    ( ~ spl9_1259
    | spl9_221
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4660,f4636,f1615,f1601,f9687])).

fof(f9687,plain,
    ( spl9_1259
  <=> ~ m2_subset_1(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1259])])).

fof(f4660,plain,
    ( ~ m2_subset_1(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f4637,f123])).

fof(f9682,plain,
    ( ~ spl9_1257
    | spl9_221
    | spl9_223
    | spl9_599 ),
    inference(avatar_split_clause,[],[f4303,f4282,f1615,f1601,f9680])).

fof(f9680,plain,
    ( spl9_1257
  <=> ~ m2_subset_1(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1257])])).

fof(f4303,plain,
    ( ~ m2_subset_1(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_599 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f4283,f123])).

fof(f9675,plain,
    ( ~ spl9_1255
    | spl9_221
    | spl9_223
    | spl9_549 ),
    inference(avatar_split_clause,[],[f4011,f3998,f1615,f1601,f9673])).

fof(f9673,plain,
    ( spl9_1255
  <=> ~ m2_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1255])])).

fof(f3998,plain,
    ( spl9_549
  <=> ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_549])])).

fof(f4011,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_549 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f3999,f123])).

fof(f3999,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_549 ),
    inference(avatar_component_clause,[],[f3998])).

fof(f9647,plain,
    ( ~ spl9_1253
    | spl9_221
    | spl9_223
    | spl9_513 ),
    inference(avatar_split_clause,[],[f3777,f3763,f1615,f1601,f9645])).

fof(f9645,plain,
    ( spl9_1253
  <=> ~ m2_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1253])])).

fof(f3763,plain,
    ( spl9_513
  <=> ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_513])])).

fof(f3777,plain,
    ( ~ m2_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_513 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f3764,f123])).

fof(f3764,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_513 ),
    inference(avatar_component_clause,[],[f3763])).

fof(f9640,plain,
    ( ~ spl9_1251
    | spl9_221
    | ~ spl9_244
    | spl9_409
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3680,f2981,f2978,f1776,f1601,f9638])).

fof(f9638,plain,
    ( spl9_1251
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1251])])).

fof(f3680,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_221
    | ~ spl9_244
    | ~ spl9_409
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f1602,f1777,f2979,f2982,f258,f2183])).

fof(f9633,plain,
    ( ~ spl9_1249
    | ~ spl9_102
    | spl9_223
    | spl9_409
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3678,f2981,f2978,f1615,f766,f9631])).

fof(f9631,plain,
    ( spl9_1249
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1249])])).

fof(f766,plain,
    ( spl9_102
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f3678,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_102
    | ~ spl9_223
    | ~ spl9_409
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f1616,f767,f2979,f2982,f258,f2183])).

fof(f767,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_102 ),
    inference(avatar_component_clause,[],[f766])).

fof(f9626,plain,
    ( ~ spl9_1247
    | spl9_223
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2903,f2870,f1665,f1615,f9624])).

fof(f9624,plain,
    ( spl9_1247
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(o_0_0_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1247])])).

fof(f2903,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(o_0_0_xboole_0),sK3)
    | ~ spl9_223
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f1616,f1666,f2871,f127])).

fof(f9619,plain,
    ( ~ spl9_1245
    | ~ spl9_6
    | spl9_361 ),
    inference(avatar_split_clause,[],[f2583,f2566,f170,f9617])).

fof(f9617,plain,
    ( spl9_1245
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1245])])).

fof(f2566,plain,
    ( spl9_361
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_361])])).

fof(f2583,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(o_0_0_xboole_0)))))
    | ~ spl9_6
    | ~ spl9_361 ),
    inference(unit_resulting_resolution,[],[f2567,f232])).

fof(f2567,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(o_0_0_xboole_0)))))
    | ~ spl9_361 ),
    inference(avatar_component_clause,[],[f2566])).

fof(f9612,plain,
    ( spl9_1242
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2862,f2651,f958,f379,f225,f184,f163,f156,f149,f9610])).

fof(f9610,plain,
    ( spl9_1242
  <=> v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1242])])).

fof(f2862,plain,
    ( v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f150,f380,f157,f164,f185,f226,f959,f2652,f140])).

fof(f9605,plain,
    ( ~ spl9_1241
    | spl9_361 ),
    inference(avatar_split_clause,[],[f2577,f2566,f9603])).

fof(f9603,plain,
    ( spl9_1241
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(o_0_0_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1241])])).

fof(f2577,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(o_0_0_xboole_0))))))
    | ~ spl9_361 ),
    inference(unit_resulting_resolution,[],[f114,f2567,f110])).

fof(f9598,plain,
    ( ~ spl9_1239
    | spl9_221
    | spl9_223
    | spl9_333 ),
    inference(avatar_split_clause,[],[f2417,f2413,f1615,f1601,f9596])).

fof(f9596,plain,
    ( spl9_1239
  <=> ~ m2_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1239])])).

fof(f2417,plain,
    ( ~ m2_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_333 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f2414,f123])).

fof(f9591,plain,
    ( ~ spl9_1237
    | spl9_221
    | spl9_223
    | spl9_319 ),
    inference(avatar_split_clause,[],[f2321,f2317,f1615,f1601,f9589])).

fof(f9589,plain,
    ( spl9_1237
  <=> ~ m2_subset_1(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1237])])).

fof(f2317,plain,
    ( spl9_319
  <=> ~ m1_subset_1(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).

fof(f2321,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_319 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f2318,f123])).

fof(f2318,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_319 ),
    inference(avatar_component_clause,[],[f2317])).

fof(f9584,plain,
    ( ~ spl9_1235
    | spl9_295 ),
    inference(avatar_split_clause,[],[f2150,f2146,f9582])).

fof(f9582,plain,
    ( spl9_1235
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1235])])).

fof(f2146,plain,
    ( spl9_295
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_295])])).

fof(f2150,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_295 ),
    inference(unit_resulting_resolution,[],[f115,f2147,f142])).

fof(f2147,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_295 ),
    inference(avatar_component_clause,[],[f2146])).

fof(f9577,plain,
    ( ~ spl9_1233
    | spl9_221
    | spl9_223
    | spl9_289 ),
    inference(avatar_split_clause,[],[f2114,f2111,f1615,f1601,f9575])).

fof(f9575,plain,
    ( spl9_1233
  <=> ~ m2_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1233])])).

fof(f2111,plain,
    ( spl9_289
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_289])])).

fof(f2114,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_289 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f2112,f123])).

fof(f2112,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_289 ),
    inference(avatar_component_clause,[],[f2111])).

fof(f9569,plain,
    ( ~ spl9_1231
    | spl9_261 ),
    inference(avatar_split_clause,[],[f1918,f1913,f9567])).

fof(f9567,plain,
    ( spl9_1231
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1231])])).

fof(f1913,plain,
    ( spl9_261
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_261])])).

fof(f1918,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_261 ),
    inference(unit_resulting_resolution,[],[f115,f1914,f142])).

fof(f1914,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_261 ),
    inference(avatar_component_clause,[],[f1913])).

fof(f9562,plain,
    ( ~ spl9_1229
    | spl9_221
    | spl9_223
    | spl9_261 ),
    inference(avatar_split_clause,[],[f1916,f1913,f1615,f1601,f9560])).

fof(f9560,plain,
    ( spl9_1229
  <=> ~ m2_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1229])])).

fof(f1916,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_261 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f1914,f123])).

fof(f9555,plain,
    ( ~ spl9_1227
    | ~ spl9_40
    | spl9_223
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1698,f1665,f1615,f327,f9553])).

fof(f9553,plain,
    ( spl9_1227
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1227])])).

fof(f1698,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(o_0_0_xboole_0),sK1)
    | ~ spl9_40
    | ~ spl9_223
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f1616,f328,f1666,f127])).

fof(f9548,plain,
    ( ~ spl9_1225
    | spl9_171
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1632,f1615,f1601,f1141,f9546])).

fof(f9546,plain,
    ( spl9_1225
  <=> ~ m2_subset_1(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1225])])).

fof(f1141,plain,
    ( spl9_171
  <=> ~ m1_subset_1(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_171])])).

fof(f1632,plain,
    ( ~ m2_subset_1(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_171
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f1142,f1602,f258,f1616,f123])).

fof(f1142,plain,
    ( ~ m1_subset_1(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_171 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f9541,plain,
    ( ~ spl9_1223
    | spl9_149
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1631,f1615,f1601,f1010,f9539])).

fof(f9539,plain,
    ( spl9_1223
  <=> ~ m2_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1223])])).

fof(f1631,plain,
    ( ~ m2_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_149
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f1011,f1602,f258,f1616,f123])).

fof(f9474,plain,
    ( ~ spl9_1221
    | ~ spl9_78
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f9388,f6300,f6297,f627,f9472])).

fof(f627,plain,
    ( spl9_78
  <=> r2_hidden(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f9388,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0)))))
    | ~ spl9_78
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f628,f6301,f6298,f3532])).

fof(f628,plain,
    ( r2_hidden(o_0_0_xboole_0,sK0)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f627])).

fof(f9324,plain,
    ( ~ spl9_1219
    | ~ spl9_6
    | spl9_831 ),
    inference(avatar_split_clause,[],[f5856,f5830,f170,f9322])).

fof(f9322,plain,
    ( spl9_1219
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK4(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1219])])).

fof(f5830,plain,
    ( spl9_831
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_831])])).

fof(f5856,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK4(sK8)))))
    | ~ spl9_6
    | ~ spl9_831 ),
    inference(unit_resulting_resolution,[],[f5831,f232])).

fof(f5831,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK8)))))
    | ~ spl9_831 ),
    inference(avatar_component_clause,[],[f5830])).

fof(f9317,plain,
    ( ~ spl9_1217
    | spl9_831 ),
    inference(avatar_split_clause,[],[f5848,f5830,f9315])).

fof(f9315,plain,
    ( spl9_1217
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK4(sK8)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1217])])).

fof(f5848,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK4(sK8))))))
    | ~ spl9_831 ),
    inference(unit_resulting_resolution,[],[f114,f5831,f110])).

fof(f9306,plain,
    ( ~ spl9_1215
    | ~ spl9_6
    | spl9_683 ),
    inference(avatar_split_clause,[],[f4833,f4814,f170,f9304])).

fof(f9304,plain,
    ( spl9_1215
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1215])])).

fof(f4814,plain,
    ( spl9_683
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_683])])).

fof(f4833,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK8)))))
    | ~ spl9_6
    | ~ spl9_683 ),
    inference(unit_resulting_resolution,[],[f4815,f232])).

fof(f4815,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK8)))))
    | ~ spl9_683 ),
    inference(avatar_component_clause,[],[f4814])).

fof(f9299,plain,
    ( ~ spl9_1213
    | spl9_683 ),
    inference(avatar_split_clause,[],[f4825,f4814,f9297])).

fof(f9297,plain,
    ( spl9_1213
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK8)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1213])])).

fof(f4825,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK8))))))
    | ~ spl9_683 ),
    inference(unit_resulting_resolution,[],[f114,f4815,f110])).

fof(f9292,plain,
    ( ~ spl9_1211
    | ~ spl9_6
    | spl9_357 ),
    inference(avatar_split_clause,[],[f2560,f2539,f170,f9290])).

fof(f9290,plain,
    ( spl9_1211
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(k1_zfmisc_1(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1211])])).

fof(f2539,plain,
    ( spl9_357
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_357])])).

fof(f2560,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(k1_zfmisc_1(sK8)))))
    | ~ spl9_6
    | ~ spl9_357 ),
    inference(unit_resulting_resolution,[],[f2540,f232])).

fof(f2540,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK8)))))
    | ~ spl9_357 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f9285,plain,
    ( ~ spl9_1209
    | spl9_357 ),
    inference(avatar_split_clause,[],[f2554,f2539,f9283])).

fof(f9283,plain,
    ( spl9_1209
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(k1_zfmisc_1(sK8)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1209])])).

fof(f2554,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(k1_zfmisc_1(sK8))))))
    | ~ spl9_357 ),
    inference(unit_resulting_resolution,[],[f114,f2540,f110])).

fof(f9088,plain,
    ( spl9_1206
    | ~ spl9_1198 ),
    inference(avatar_split_clause,[],[f9078,f8780,f9086])).

fof(f9086,plain,
    ( spl9_1206
  <=> v1_relat_1(sK7(sK4(sK8),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1206])])).

fof(f8780,plain,
    ( spl9_1198
  <=> m1_subset_1(sK7(sK4(sK8),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK8),sK4(sK8)),sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1198])])).

fof(f9078,plain,
    ( v1_relat_1(sK7(sK4(sK8),sK1))
    | ~ spl9_1198 ),
    inference(unit_resulting_resolution,[],[f8781,f136])).

fof(f8781,plain,
    ( m1_subset_1(sK7(sK4(sK8),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK8),sK4(sK8)),sK4(sK8))))
    | ~ spl9_1198 ),
    inference(avatar_component_clause,[],[f8780])).

fof(f8892,plain,
    ( spl9_1204
    | ~ spl9_1186 ),
    inference(avatar_split_clause,[],[f8882,f8738,f8890])).

fof(f8890,plain,
    ( spl9_1204
  <=> v1_relat_1(sK7(sK4(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1204])])).

fof(f8738,plain,
    ( spl9_1186
  <=> m1_subset_1(sK7(sK4(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK0),sK4(sK0)),sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1186])])).

fof(f8882,plain,
    ( v1_relat_1(sK7(sK4(sK0),sK1))
    | ~ spl9_1186 ),
    inference(unit_resulting_resolution,[],[f8739,f136])).

fof(f8739,plain,
    ( m1_subset_1(sK7(sK4(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK0),sK4(sK0)),sK4(sK0))))
    | ~ spl9_1186 ),
    inference(avatar_component_clause,[],[f8738])).

fof(f8865,plain,
    ( ~ spl9_1203
    | spl9_225
    | spl9_1143 ),
    inference(avatar_split_clause,[],[f8673,f8406,f1644,f8863])).

fof(f8863,plain,
    ( spl9_1203
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1203])])).

fof(f8406,plain,
    ( spl9_1143
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1143])])).

fof(f8673,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_1143 ),
    inference(unit_resulting_resolution,[],[f1645,f8407,f119])).

fof(f8407,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_1143 ),
    inference(avatar_component_clause,[],[f8406])).

fof(f8858,plain,
    ( ~ spl9_1201
    | spl9_1123 ),
    inference(avatar_split_clause,[],[f8669,f8134,f8856])).

fof(f8856,plain,
    ( spl9_1201
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1201])])).

fof(f8134,plain,
    ( spl9_1123
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1123])])).

fof(f8669,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_1123 ),
    inference(unit_resulting_resolution,[],[f8135,f117])).

fof(f8135,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_1123 ),
    inference(avatar_component_clause,[],[f8134])).

fof(f8782,plain,
    ( spl9_1198
    | spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(avatar_split_clause,[],[f2833,f2624,f327,f255,f8780])).

fof(f255,plain,
    ( spl9_27
  <=> ~ v1_xboole_0(sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f2624,plain,
    ( spl9_374
  <=> m2_filter_1(sK7(sK4(sK8),sK1),sK4(sK8),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_374])])).

fof(f2833,plain,
    ( m1_subset_1(sK7(sK4(sK8),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK8),sK4(sK8)),sK4(sK8))))
    | ~ spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(unit_resulting_resolution,[],[f328,f256,f2625,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2625,plain,
    ( m2_filter_1(sK7(sK4(sK8),sK1),sK4(sK8),sK1)
    | ~ spl9_374 ),
    inference(avatar_component_clause,[],[f2624])).

fof(f256,plain,
    ( ~ v1_xboole_0(sK4(sK8))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f255])).

fof(f8775,plain,
    ( ~ spl9_1197
    | spl9_993 ),
    inference(avatar_split_clause,[],[f7317,f6936,f8773])).

fof(f8773,plain,
    ( spl9_1197
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1197])])).

fof(f6936,plain,
    ( spl9_993
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_993])])).

fof(f7317,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_993 ),
    inference(unit_resulting_resolution,[],[f6937,f117])).

fof(f6937,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_993 ),
    inference(avatar_component_clause,[],[f6936])).

fof(f8768,plain,
    ( ~ spl9_1195
    | spl9_1
    | ~ spl9_76
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6330,f6300,f6297,f606,f149,f8766])).

fof(f8766,plain,
    ( spl9_1195
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(sK5(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1195])])).

fof(f6330,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(sK5(o_0_0_xboole_0)))))
    | ~ spl9_1
    | ~ spl9_76
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f150,f607,f6301,f115,f6298,f2183])).

fof(f8761,plain,
    ( ~ spl9_1193
    | spl9_231
    | ~ spl9_396
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6312,f6300,f2870,f1665,f8759])).

fof(f8759,plain,
    ( spl9_1193
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(o_0_0_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1193])])).

fof(f6312,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(o_0_0_xboole_0),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f6301,f127])).

fof(f8754,plain,
    ( ~ spl9_1191
    | ~ spl9_40
    | spl9_231
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6310,f6300,f1665,f327,f8752])).

fof(f8752,plain,
    ( spl9_1191
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1191])])).

fof(f6310,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(o_0_0_xboole_0),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f6301,f127])).

fof(f8747,plain,
    ( spl9_1188
    | ~ spl9_6
    | ~ spl9_846 ),
    inference(avatar_split_clause,[],[f6000,f5899,f170,f8745])).

fof(f8745,plain,
    ( spl9_1188
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1188])])).

fof(f5899,plain,
    ( spl9_846
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_846])])).

fof(f6000,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_846 ),
    inference(unit_resulting_resolution,[],[f5900,f210])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f208,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t6_boole)).

fof(f208,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f171,f113])).

fof(f5900,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)))
    | ~ spl9_846 ),
    inference(avatar_component_clause,[],[f5899])).

fof(f8740,plain,
    ( spl9_1186
    | spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(avatar_split_clause,[],[f2817,f2589,f327,f239,f8738])).

fof(f239,plain,
    ( spl9_23
  <=> ~ v1_xboole_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f2589,plain,
    ( spl9_364
  <=> m2_filter_1(sK7(sK4(sK0),sK1),sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_364])])).

fof(f2817,plain,
    ( m1_subset_1(sK7(sK4(sK0),sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4(sK0),sK4(sK0)),sK4(sK0))))
    | ~ spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(unit_resulting_resolution,[],[f328,f240,f2590,f129])).

fof(f2590,plain,
    ( m2_filter_1(sK7(sK4(sK0),sK1),sK4(sK0),sK1)
    | ~ spl9_364 ),
    inference(avatar_component_clause,[],[f2589])).

fof(f240,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f8733,plain,
    ( ~ spl9_1185
    | ~ spl9_6
    | spl9_767 ),
    inference(avatar_split_clause,[],[f5352,f5318,f170,f8731])).

fof(f8731,plain,
    ( spl9_1185
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1185])])).

fof(f5318,plain,
    ( spl9_767
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_767])])).

fof(f5352,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK4(sK0)))))
    | ~ spl9_6
    | ~ spl9_767 ),
    inference(unit_resulting_resolution,[],[f5319,f232])).

fof(f5319,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK0)))))
    | ~ spl9_767 ),
    inference(avatar_component_clause,[],[f5318])).

fof(f8726,plain,
    ( ~ spl9_1183
    | spl9_767 ),
    inference(avatar_split_clause,[],[f5344,f5318,f8724])).

fof(f8724,plain,
    ( spl9_1183
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1183])])).

fof(f5344,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK4(sK0))))))
    | ~ spl9_767 ),
    inference(unit_resulting_resolution,[],[f114,f5319,f110])).

fof(f8697,plain,
    ( ~ spl9_1181
    | spl9_1167 ),
    inference(avatar_split_clause,[],[f8629,f8594,f8695])).

fof(f8695,plain,
    ( spl9_1181
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1181])])).

fof(f8594,plain,
    ( spl9_1167
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1167])])).

fof(f8629,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1167 ),
    inference(unit_resulting_resolution,[],[f8595,f117])).

fof(f8595,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1167 ),
    inference(avatar_component_clause,[],[f8594])).

fof(f8668,plain,
    ( spl9_1100
    | spl9_1178
    | spl9_1
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2552,f2462,f149,f8666,f7889])).

fof(f7889,plain,
    ( spl9_1100
  <=> v1_xboole_0(k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1100])])).

fof(f8666,plain,
    ( spl9_1178
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k11_relat_1(sK1,sK5(sK0)))
        | m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1178])])).

fof(f2462,plain,
    ( spl9_342
  <=> m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_342])])).

fof(f2552,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k11_relat_1(sK1,sK5(sK0)))
        | v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
        | m1_subset_1(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_342 ),
    inference(subsumption_resolution,[],[f2551,f150])).

fof(f2551,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k11_relat_1(sK1,sK5(sK0)))
        | v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
        | v1_xboole_0(sK0)
        | m1_subset_1(X0,sK0) )
    | ~ spl9_342 ),
    inference(resolution,[],[f2463,f759])).

fof(f2463,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_342 ),
    inference(avatar_component_clause,[],[f2462])).

fof(f8664,plain,
    ( ~ spl9_1177
    | ~ spl9_6
    | spl9_1071 ),
    inference(avatar_split_clause,[],[f7802,f7721,f170,f8662])).

fof(f8662,plain,
    ( spl9_1177
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1177])])).

fof(f7721,plain,
    ( spl9_1071
  <=> ~ v1_xboole_0(sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1071])])).

fof(f7802,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_1071 ),
    inference(unit_resulting_resolution,[],[f7722,f232])).

fof(f7722,plain,
    ( ~ v1_xboole_0(sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0))))
    | ~ spl9_1071 ),
    inference(avatar_component_clause,[],[f7721])).

fof(f8657,plain,
    ( ~ spl9_1175
    | spl9_1071 ),
    inference(avatar_split_clause,[],[f7790,f7721,f8655])).

fof(f8655,plain,
    ( spl9_1175
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1175])])).

fof(f7790,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0)))))
    | ~ spl9_1071 ),
    inference(unit_resulting_resolution,[],[f114,f7722,f110])).

fof(f8650,plain,
    ( ~ spl9_1173
    | ~ spl9_6
    | spl9_1067 ),
    inference(avatar_split_clause,[],[f7787,f7707,f170,f8648])).

fof(f8648,plain,
    ( spl9_1173
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1173])])).

fof(f7707,plain,
    ( spl9_1067
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1067])])).

fof(f7787,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl9_6
    | ~ spl9_1067 ),
    inference(unit_resulting_resolution,[],[f7708,f232])).

fof(f7708,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl9_1067 ),
    inference(avatar_component_clause,[],[f7707])).

fof(f8610,plain,
    ( ~ spl9_1171
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1152 ),
    inference(avatar_split_clause,[],[f8557,f8491,f1601,f170,f8608])).

fof(f8608,plain,
    ( spl9_1171
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1171])])).

fof(f8557,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1152 ),
    inference(unit_resulting_resolution,[],[f8492,f4571])).

fof(f8603,plain,
    ( ~ spl9_1169
    | ~ spl9_6
    | ~ spl9_1152 ),
    inference(avatar_split_clause,[],[f8555,f8491,f170,f8601])).

fof(f8601,plain,
    ( spl9_1169
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1169])])).

fof(f8555,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1152 ),
    inference(unit_resulting_resolution,[],[f8492,f3159])).

fof(f8596,plain,
    ( ~ spl9_1167
    | ~ spl9_6
    | ~ spl9_1152 ),
    inference(avatar_split_clause,[],[f8545,f8491,f170,f8594])).

fof(f8545,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1152 ),
    inference(unit_resulting_resolution,[],[f8492,f355])).

fof(f8589,plain,
    ( ~ spl9_1165
    | ~ spl9_6
    | spl9_1151 ),
    inference(avatar_split_clause,[],[f8528,f8484,f170,f8587])).

fof(f8587,plain,
    ( spl9_1165
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1165])])).

fof(f8484,plain,
    ( spl9_1151
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1151])])).

fof(f8528,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_6
    | ~ spl9_1151 ),
    inference(unit_resulting_resolution,[],[f8485,f232])).

fof(f8485,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_1151 ),
    inference(avatar_component_clause,[],[f8484])).

fof(f8582,plain,
    ( ~ spl9_1163
    | spl9_1151 ),
    inference(avatar_split_clause,[],[f8516,f8484,f8580])).

fof(f8580,plain,
    ( spl9_1163
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1163])])).

fof(f8516,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl9_1151 ),
    inference(unit_resulting_resolution,[],[f114,f8485,f110])).

fof(f8575,plain,
    ( ~ spl9_1161
    | ~ spl9_20
    | spl9_223
    | spl9_467
    | spl9_1149 ),
    inference(avatar_split_clause,[],[f8461,f8423,f3425,f1615,f225,f8573])).

fof(f8573,plain,
    ( spl9_1161
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1161])])).

fof(f3425,plain,
    ( spl9_467
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_467])])).

fof(f8423,plain,
    ( spl9_1149
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1149])])).

fof(f8461,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),o_0_0_xboole_0)
    | ~ spl9_20
    | ~ spl9_223
    | ~ spl9_467
    | ~ spl9_1149 ),
    inference(unit_resulting_resolution,[],[f1616,f3426,f226,f8424,f2181])).

fof(f8424,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_1149 ),
    inference(avatar_component_clause,[],[f8423])).

fof(f3426,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_467 ),
    inference(avatar_component_clause,[],[f3425])).

fof(f8514,plain,
    ( ~ spl9_1159
    | ~ spl9_20
    | spl9_1149 ),
    inference(avatar_split_clause,[],[f8449,f8423,f225,f8512])).

fof(f8512,plain,
    ( spl9_1159
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1159])])).

fof(f8449,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl9_20
    | ~ spl9_1149 ),
    inference(unit_resulting_resolution,[],[f226,f8424,f289])).

fof(f8507,plain,
    ( ~ spl9_1157
    | spl9_1100
    | spl9_115
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f3071,f2679,f819,f7889,f8505])).

fof(f8505,plain,
    ( spl9_1157
  <=> ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1157])])).

fof(f2679,plain,
    ( spl9_384
  <=> m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_384])])).

fof(f3071,plain,
    ( v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_115
    | ~ spl9_384 ),
    inference(subsumption_resolution,[],[f3056,f820])).

fof(f3056,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_384 ),
    inference(resolution,[],[f1863,f2680])).

fof(f2680,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_384 ),
    inference(avatar_component_clause,[],[f2679])).

fof(f8500,plain,
    ( ~ spl9_1155
    | ~ spl9_6
    | spl9_1149 ),
    inference(avatar_split_clause,[],[f8448,f8423,f170,f8498])).

fof(f8498,plain,
    ( spl9_1155
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1155])])).

fof(f8448,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_6
    | ~ spl9_1149 ),
    inference(unit_resulting_resolution,[],[f8424,f232])).

fof(f8493,plain,
    ( spl9_1152
    | ~ spl9_20
    | spl9_1149 ),
    inference(avatar_split_clause,[],[f8434,f8423,f225,f8491])).

fof(f8434,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_20
    | ~ spl9_1149 ),
    inference(unit_resulting_resolution,[],[f226,f8424,f119])).

fof(f8486,plain,
    ( ~ spl9_1151
    | spl9_1149 ),
    inference(avatar_split_clause,[],[f8433,f8423,f8484])).

fof(f8433,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_1149 ),
    inference(unit_resulting_resolution,[],[f114,f8424,f110])).

fof(f8428,plain,
    ( ~ spl9_1147
    | spl9_450
    | spl9_1148
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f3057,f225,f8426,f3317,f8420])).

fof(f8420,plain,
    ( spl9_1147
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1147])])).

fof(f3317,plain,
    ( spl9_450
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_450])])).

fof(f8426,plain,
    ( spl9_1148
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1148])])).

fof(f3057,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl9_20 ),
    inference(resolution,[],[f1863,f226])).

fof(f8415,plain,
    ( ~ spl9_1145
    | spl9_1067 ),
    inference(avatar_split_clause,[],[f7775,f7707,f8413])).

fof(f8413,plain,
    ( spl9_1145
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1145])])).

fof(f7775,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))))
    | ~ spl9_1067 ),
    inference(unit_resulting_resolution,[],[f114,f7708,f110])).

fof(f8408,plain,
    ( ~ spl9_1143
    | spl9_221
    | spl9_251
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7487,f7439,f1829,f1601,f8406])).

fof(f1829,plain,
    ( spl9_251
  <=> ~ m1_subset_1(sK4(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_251])])).

fof(f7487,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_251
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f1602,f258,f1830,f258,f7440,f2183])).

fof(f1830,plain,
    ( ~ m1_subset_1(sK4(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_251 ),
    inference(avatar_component_clause,[],[f1829])).

fof(f8399,plain,
    ( ~ spl9_1141
    | spl9_1129 ),
    inference(avatar_split_clause,[],[f8337,f8316,f8397])).

fof(f8397,plain,
    ( spl9_1141
  <=> ~ r2_hidden(sK1,sK4(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1141])])).

fof(f8316,plain,
    ( spl9_1129
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1129])])).

fof(f8337,plain,
    ( ~ r2_hidden(sK1,sK4(sK5(sK5(sK1))))
    | ~ spl9_1129 ),
    inference(unit_resulting_resolution,[],[f258,f8317,f142])).

fof(f8317,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK5(sK5(sK1))))
    | ~ spl9_1129 ),
    inference(avatar_component_clause,[],[f8316])).

fof(f8384,plain,
    ( ~ spl9_1139
    | spl9_1129 ),
    inference(avatar_split_clause,[],[f8336,f8316,f8382])).

fof(f8382,plain,
    ( spl9_1139
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK5(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1139])])).

fof(f8336,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK5(sK5(sK1))))
    | ~ spl9_1129 ),
    inference(unit_resulting_resolution,[],[f8317,f117])).

fof(f8375,plain,
    ( ~ spl9_1137
    | spl9_1127 ),
    inference(avatar_split_clause,[],[f8309,f8305,f8373])).

fof(f8373,plain,
    ( spl9_1137
  <=> ~ r2_hidden(sK8,sK4(sK5(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1137])])).

fof(f8305,plain,
    ( spl9_1127
  <=> ~ m1_subset_1(sK8,k1_zfmisc_1(sK5(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1127])])).

fof(f8309,plain,
    ( ~ r2_hidden(sK8,sK4(sK5(sK5(sK8))))
    | ~ spl9_1127 ),
    inference(unit_resulting_resolution,[],[f258,f8306,f142])).

fof(f8306,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK5(sK5(sK8))))
    | ~ spl9_1127 ),
    inference(avatar_component_clause,[],[f8305])).

fof(f8368,plain,
    ( ~ spl9_1135
    | spl9_1127 ),
    inference(avatar_split_clause,[],[f8308,f8305,f8366])).

fof(f8366,plain,
    ( spl9_1135
  <=> ~ r2_hidden(sK8,k1_zfmisc_1(sK5(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1135])])).

fof(f8308,plain,
    ( ~ r2_hidden(sK8,k1_zfmisc_1(sK5(sK5(sK8))))
    | ~ spl9_1127 ),
    inference(unit_resulting_resolution,[],[f8306,f117])).

fof(f8335,plain,
    ( ~ spl9_1133
    | spl9_1125 ),
    inference(avatar_split_clause,[],[f8298,f8294,f8333])).

fof(f8333,plain,
    ( spl9_1133
  <=> ~ r2_hidden(sK0,sK4(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1133])])).

fof(f8294,plain,
    ( spl9_1125
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1125])])).

fof(f8298,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(sK5(sK0))))
    | ~ spl9_1125 ),
    inference(unit_resulting_resolution,[],[f258,f8295,f142])).

fof(f8295,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(sK5(sK0))))
    | ~ spl9_1125 ),
    inference(avatar_component_clause,[],[f8294])).

fof(f8328,plain,
    ( ~ spl9_1131
    | spl9_1125 ),
    inference(avatar_split_clause,[],[f8297,f8294,f8326])).

fof(f8326,plain,
    ( spl9_1131
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK5(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1131])])).

fof(f8297,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK5(sK5(sK0))))
    | ~ spl9_1125 ),
    inference(unit_resulting_resolution,[],[f8295,f117])).

fof(f8318,plain,
    ( ~ spl9_1129
    | ~ spl9_458
    | spl9_697 ),
    inference(avatar_split_clause,[],[f8148,f4872,f3379,f8316])).

fof(f4872,plain,
    ( spl9_697
  <=> ~ v1_xboole_0(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_697])])).

fof(f8148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK5(sK5(sK1))))
    | ~ spl9_458
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f3380,f4873,f115,f3067])).

fof(f4873,plain,
    ( ~ v1_xboole_0(sK5(sK1))
    | ~ spl9_697 ),
    inference(avatar_component_clause,[],[f4872])).

fof(f8307,plain,
    ( ~ spl9_1127
    | ~ spl9_42
    | spl9_629 ),
    inference(avatar_split_clause,[],[f8149,f4492,f341,f8305])).

fof(f4492,plain,
    ( spl9_629
  <=> ~ v1_xboole_0(sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_629])])).

fof(f8149,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK5(sK5(sK8))))
    | ~ spl9_42
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f342,f4493,f115,f3067])).

fof(f4493,plain,
    ( ~ v1_xboole_0(sK5(sK8))
    | ~ spl9_629 ),
    inference(avatar_component_clause,[],[f4492])).

fof(f8296,plain,
    ( ~ spl9_1125
    | ~ spl9_38
    | spl9_579 ),
    inference(avatar_split_clause,[],[f8146,f4156,f318,f8294])).

fof(f4156,plain,
    ( spl9_579
  <=> ~ v1_xboole_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_579])])).

fof(f8146,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(sK5(sK0))))
    | ~ spl9_38
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f319,f4157,f115,f3067])).

fof(f4157,plain,
    ( ~ v1_xboole_0(sK5(sK0))
    | ~ spl9_579 ),
    inference(avatar_component_clause,[],[f4156])).

fof(f8136,plain,
    ( ~ spl9_1123
    | spl9_221
    | spl9_251
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7473,f7439,f1829,f1601,f8134])).

fof(f7473,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_251
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f1602,f1830,f258,f7440,f759])).

fof(f8075,plain,
    ( ~ spl9_1121
    | spl9_1
    | ~ spl9_1106 ),
    inference(avatar_split_clause,[],[f8010,f8000,f149,f8073])).

fof(f8073,plain,
    ( spl9_1121
  <=> ~ r2_hidden(sK0,sK5(k11_relat_1(sK1,sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1121])])).

fof(f8000,plain,
    ( spl9_1106
  <=> m1_subset_1(sK5(k11_relat_1(sK1,sK5(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1106])])).

fof(f8010,plain,
    ( ~ r2_hidden(sK0,sK5(k11_relat_1(sK1,sK5(sK0))))
    | ~ spl9_1
    | ~ spl9_1106 ),
    inference(unit_resulting_resolution,[],[f150,f8001,f289])).

fof(f8001,plain,
    ( m1_subset_1(sK5(k11_relat_1(sK1,sK5(sK0))),sK0)
    | ~ spl9_1106 ),
    inference(avatar_component_clause,[],[f8000])).

fof(f8068,plain,
    ( spl9_1118
    | spl9_1
    | ~ spl9_1106 ),
    inference(avatar_split_clause,[],[f8007,f8000,f149,f8066])).

fof(f8066,plain,
    ( spl9_1118
  <=> r2_hidden(sK5(k11_relat_1(sK1,sK5(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1118])])).

fof(f8007,plain,
    ( r2_hidden(sK5(k11_relat_1(sK1,sK5(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_1106 ),
    inference(unit_resulting_resolution,[],[f150,f8001,f119])).

fof(f8058,plain,
    ( ~ spl9_1117
    | spl9_1
    | ~ spl9_1096 ),
    inference(avatar_split_clause,[],[f7985,f7876,f149,f8056])).

fof(f8056,plain,
    ( spl9_1117
  <=> ~ r2_hidden(sK0,sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1117])])).

fof(f7876,plain,
    ( spl9_1096
  <=> m1_subset_1(sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1096])])).

fof(f7985,plain,
    ( ~ r2_hidden(sK0,sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)))
    | ~ spl9_1
    | ~ spl9_1096 ),
    inference(unit_resulting_resolution,[],[f150,f7877,f289])).

fof(f7877,plain,
    ( m1_subset_1(sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1096 ),
    inference(avatar_component_clause,[],[f7876])).

fof(f8051,plain,
    ( spl9_1114
    | spl9_1
    | ~ spl9_1096 ),
    inference(avatar_split_clause,[],[f7982,f7876,f149,f8049])).

fof(f8049,plain,
    ( spl9_1114
  <=> r2_hidden(sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1114])])).

fof(f7982,plain,
    ( r2_hidden(sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1
    | ~ spl9_1096 ),
    inference(unit_resulting_resolution,[],[f150,f7877,f119])).

fof(f8044,plain,
    ( ~ spl9_1113
    | ~ spl9_6
    | spl9_1103 ),
    inference(avatar_split_clause,[],[f7948,f7925,f170,f8042])).

fof(f8042,plain,
    ( spl9_1113
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k11_relat_1(sK1,sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1113])])).

fof(f7925,plain,
    ( spl9_1103
  <=> ~ v1_xboole_0(sK4(k11_relat_1(sK1,sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1103])])).

fof(f7948,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k11_relat_1(sK1,sK5(sK0))))
    | ~ spl9_6
    | ~ spl9_1103 ),
    inference(unit_resulting_resolution,[],[f7926,f232])).

fof(f7926,plain,
    ( ~ v1_xboole_0(sK4(k11_relat_1(sK1,sK5(sK0))))
    | ~ spl9_1103 ),
    inference(avatar_component_clause,[],[f7925])).

fof(f8037,plain,
    ( ~ spl9_1111
    | spl9_1103 ),
    inference(avatar_split_clause,[],[f7936,f7925,f8035])).

fof(f8035,plain,
    ( spl9_1111
  <=> ~ v1_xboole_0(sK4(sK4(k11_relat_1(sK1,sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1111])])).

fof(f7936,plain,
    ( ~ v1_xboole_0(sK4(sK4(k11_relat_1(sK1,sK5(sK0)))))
    | ~ spl9_1103 ),
    inference(unit_resulting_resolution,[],[f114,f7926,f110])).

fof(f8030,plain,
    ( ~ spl9_1109
    | spl9_1
    | ~ spl9_286
    | spl9_1057
    | spl9_1063 ),
    inference(avatar_split_clause,[],[f7682,f7659,f7557,f2061,f149,f8028])).

fof(f8028,plain,
    ( spl9_1109
  <=> ~ m2_subset_1(k1_zfmisc_1(sK0),sK0,k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1109])])).

fof(f2061,plain,
    ( spl9_286
  <=> m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_286])])).

fof(f7557,plain,
    ( spl9_1057
  <=> ~ v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1057])])).

fof(f7659,plain,
    ( spl9_1063
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1063])])).

fof(f7682,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(sK0),sK0,k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_1
    | ~ spl9_286
    | ~ spl9_1057
    | ~ spl9_1063 ),
    inference(unit_resulting_resolution,[],[f150,f7558,f2062,f7660,f124])).

fof(f7660,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_1063 ),
    inference(avatar_component_clause,[],[f7659])).

fof(f2062,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_286 ),
    inference(avatar_component_clause,[],[f2061])).

fof(f7558,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_1057 ),
    inference(avatar_component_clause,[],[f7557])).

fof(f8002,plain,
    ( spl9_1106
    | spl9_1
    | ~ spl9_328
    | ~ spl9_686
    | spl9_1101 ),
    inference(avatar_split_clause,[],[f7920,f7886,f4840,f2387,f149,f8000])).

fof(f4840,plain,
    ( spl9_686
  <=> r2_hidden(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_686])])).

fof(f7886,plain,
    ( spl9_1101
  <=> ~ v1_xboole_0(k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1101])])).

fof(f7920,plain,
    ( m1_subset_1(sK5(k11_relat_1(sK1,sK5(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_328
    | ~ spl9_686
    | ~ spl9_1101 ),
    inference(unit_resulting_resolution,[],[f150,f2388,f4841,f115,f7887,f2183])).

fof(f7887,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_1101 ),
    inference(avatar_component_clause,[],[f7886])).

fof(f4841,plain,
    ( r2_hidden(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_686 ),
    inference(avatar_component_clause,[],[f4840])).

fof(f7934,plain,
    ( ~ spl9_1105
    | ~ spl9_6
    | spl9_1101 ),
    inference(avatar_split_clause,[],[f7909,f7886,f170,f7932])).

fof(f7932,plain,
    ( spl9_1105
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1105])])).

fof(f7909,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_6
    | ~ spl9_1101 ),
    inference(unit_resulting_resolution,[],[f7887,f232])).

fof(f7927,plain,
    ( ~ spl9_1103
    | spl9_1101 ),
    inference(avatar_split_clause,[],[f7893,f7886,f7925])).

fof(f7893,plain,
    ( ~ v1_xboole_0(sK4(k11_relat_1(sK1,sK5(sK0))))
    | ~ spl9_1101 ),
    inference(unit_resulting_resolution,[],[f114,f7887,f110])).

fof(f7891,plain,
    ( ~ spl9_1099
    | spl9_1100
    | spl9_143
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f3070,f2462,f975,f7889,f7883])).

fof(f7883,plain,
    ( spl9_1099
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1099])])).

fof(f3070,plain,
    ( v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_143
    | ~ spl9_342 ),
    inference(subsumption_resolution,[],[f3055,f976])).

fof(f3055,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | v1_xboole_0(k11_relat_1(sK1,sK5(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_342 ),
    inference(resolution,[],[f1863,f2463])).

fof(f7878,plain,
    ( spl9_1096
    | spl9_1
    | ~ spl9_286
    | spl9_1057 ),
    inference(avatar_split_clause,[],[f7584,f7557,f2061,f149,f7876])).

fof(f7584,plain,
    ( m1_subset_1(sK6(sK0,k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1
    | ~ spl9_286
    | ~ spl9_1057 ),
    inference(unit_resulting_resolution,[],[f150,f2062,f7558,f708])).

fof(f7871,plain,
    ( ~ spl9_1095
    | ~ spl9_328
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7465,f7439,f2387,f7869])).

fof(f7869,plain,
    ( spl9_1095
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1095])])).

fof(f7465,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_328
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f2388,f7440,f289])).

fof(f7864,plain,
    ( spl9_1092
    | ~ spl9_328
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7449,f7439,f2387,f7862])).

fof(f7862,plain,
    ( spl9_1092
  <=> r2_hidden(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1092])])).

fof(f7449,plain,
    ( r2_hidden(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_328
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f2388,f7440,f119])).

fof(f7855,plain,
    ( ~ spl9_1091
    | spl9_1077 ),
    inference(avatar_split_clause,[],[f7813,f7739,f7853])).

fof(f7853,plain,
    ( spl9_1091
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1091])])).

fof(f7739,plain,
    ( spl9_1077
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1077])])).

fof(f7813,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1077 ),
    inference(unit_resulting_resolution,[],[f7740,f117])).

fof(f7740,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_1077 ),
    inference(avatar_component_clause,[],[f7739])).

fof(f7848,plain,
    ( spl9_1088
    | spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(avatar_split_clause,[],[f2834,f2624,f327,f255,f7846])).

fof(f7846,plain,
    ( spl9_1088
  <=> v1_funct_2(sK7(sK4(sK8),sK1),k2_zfmisc_1(sK4(sK8),sK4(sK8)),sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1088])])).

fof(f2834,plain,
    ( v1_funct_2(sK7(sK4(sK8),sK1),k2_zfmisc_1(sK4(sK8),sK4(sK8)),sK4(sK8))
    | ~ spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(unit_resulting_resolution,[],[f328,f256,f2625,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f7810,plain,
    ( spl9_1086
    | spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(avatar_split_clause,[],[f2818,f2589,f327,f239,f7808])).

fof(f7808,plain,
    ( spl9_1086
  <=> v1_funct_2(sK7(sK4(sK0),sK1),k2_zfmisc_1(sK4(sK0),sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1086])])).

fof(f2818,plain,
    ( v1_funct_2(sK7(sK4(sK0),sK1),k2_zfmisc_1(sK4(sK0),sK4(sK0)),sK4(sK0))
    | ~ spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(unit_resulting_resolution,[],[f328,f240,f2590,f128])).

fof(f7773,plain,
    ( ~ spl9_1085
    | spl9_1
    | ~ spl9_1064 ),
    inference(avatar_split_clause,[],[f7692,f7666,f149,f7771])).

fof(f7771,plain,
    ( spl9_1085
  <=> ~ r2_hidden(sK0,sK5(k11_relat_1(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1085])])).

fof(f7666,plain,
    ( spl9_1064
  <=> m1_subset_1(sK5(k11_relat_1(sK1,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1064])])).

fof(f7692,plain,
    ( ~ r2_hidden(sK0,sK5(k11_relat_1(sK1,o_0_0_xboole_0)))
    | ~ spl9_1
    | ~ spl9_1064 ),
    inference(unit_resulting_resolution,[],[f150,f7667,f289])).

fof(f7667,plain,
    ( m1_subset_1(sK5(k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1064 ),
    inference(avatar_component_clause,[],[f7666])).

fof(f7762,plain,
    ( spl9_1082
    | spl9_1
    | ~ spl9_1064 ),
    inference(avatar_split_clause,[],[f7689,f7666,f149,f7760])).

fof(f7760,plain,
    ( spl9_1082
  <=> r2_hidden(sK5(k11_relat_1(sK1,o_0_0_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1082])])).

fof(f7689,plain,
    ( r2_hidden(sK5(k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1
    | ~ spl9_1064 ),
    inference(unit_resulting_resolution,[],[f150,f7667,f119])).

fof(f7755,plain,
    ( ~ spl9_1081
    | ~ spl9_6
    | spl9_221
    | ~ spl9_1048 ),
    inference(avatar_split_clause,[],[f7644,f7533,f1601,f170,f7753])).

fof(f7753,plain,
    ( spl9_1081
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1081])])).

fof(f7533,plain,
    ( spl9_1048
  <=> r2_hidden(sK4(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1048])])).

fof(f7644,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_1048 ),
    inference(unit_resulting_resolution,[],[f7534,f4571])).

fof(f7534,plain,
    ( r2_hidden(sK4(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_1048 ),
    inference(avatar_component_clause,[],[f7533])).

fof(f7748,plain,
    ( ~ spl9_1079
    | ~ spl9_6
    | ~ spl9_1048 ),
    inference(avatar_split_clause,[],[f7642,f7533,f170,f7746])).

fof(f7746,plain,
    ( spl9_1079
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1079])])).

fof(f7642,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1048 ),
    inference(unit_resulting_resolution,[],[f7534,f3159])).

fof(f7741,plain,
    ( ~ spl9_1077
    | ~ spl9_6
    | ~ spl9_1048 ),
    inference(avatar_split_clause,[],[f7636,f7533,f170,f7739])).

fof(f7636,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1048 ),
    inference(unit_resulting_resolution,[],[f7534,f355])).

fof(f7734,plain,
    ( ~ spl9_1075
    | ~ spl9_6
    | spl9_1059 ),
    inference(avatar_split_clause,[],[f7619,f7596,f170,f7732])).

fof(f7732,plain,
    ( spl9_1075
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k11_relat_1(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1075])])).

fof(f7596,plain,
    ( spl9_1059
  <=> ~ v1_xboole_0(sK4(k11_relat_1(sK1,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1059])])).

fof(f7619,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k11_relat_1(sK1,o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_1059 ),
    inference(unit_resulting_resolution,[],[f7597,f232])).

fof(f7597,plain,
    ( ~ v1_xboole_0(sK4(k11_relat_1(sK1,o_0_0_xboole_0)))
    | ~ spl9_1059 ),
    inference(avatar_component_clause,[],[f7596])).

fof(f7727,plain,
    ( spl9_1056
    | spl9_1072
    | spl9_1
    | ~ spl9_286 ),
    inference(avatar_split_clause,[],[f2196,f2061,f149,f7725,f7560])).

fof(f7560,plain,
    ( spl9_1056
  <=> v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1056])])).

fof(f7725,plain,
    ( spl9_1072
  <=> ! [X19] :
        ( ~ m1_subset_1(X19,k11_relat_1(sK1,o_0_0_xboole_0))
        | m1_subset_1(X19,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1072])])).

fof(f2196,plain,
    ( ! [X19] :
        ( ~ m1_subset_1(X19,k11_relat_1(sK1,o_0_0_xboole_0))
        | v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0))
        | m1_subset_1(X19,sK0) )
    | ~ spl9_1
    | ~ spl9_286 ),
    inference(subsumption_resolution,[],[f2187,f150])).

fof(f2187,plain,
    ( ! [X19] :
        ( ~ m1_subset_1(X19,k11_relat_1(sK1,o_0_0_xboole_0))
        | v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0))
        | v1_xboole_0(sK0)
        | m1_subset_1(X19,sK0) )
    | ~ spl9_286 ),
    inference(resolution,[],[f759,f2062])).

fof(f7723,plain,
    ( ~ spl9_1071
    | spl9_1059 ),
    inference(avatar_split_clause,[],[f7607,f7596,f7721])).

fof(f7607,plain,
    ( ~ v1_xboole_0(sK4(sK4(k11_relat_1(sK1,o_0_0_xboole_0))))
    | ~ spl9_1059 ),
    inference(unit_resulting_resolution,[],[f114,f7597,f110])).

fof(f7716,plain,
    ( ~ spl9_1069
    | ~ spl9_6
    | spl9_1043 ),
    inference(avatar_split_clause,[],[f7516,f7493,f170,f7714])).

fof(f7714,plain,
    ( spl9_1069
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1069])])).

fof(f7493,plain,
    ( spl9_1043
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1043])])).

fof(f7516,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | ~ spl9_6
    | ~ spl9_1043 ),
    inference(unit_resulting_resolution,[],[f7494,f232])).

fof(f7494,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | ~ spl9_1043 ),
    inference(avatar_component_clause,[],[f7493])).

fof(f7709,plain,
    ( ~ spl9_1067
    | spl9_1043 ),
    inference(avatar_split_clause,[],[f7504,f7493,f7707])).

fof(f7504,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl9_1043 ),
    inference(unit_resulting_resolution,[],[f114,f7494,f110])).

fof(f7668,plain,
    ( spl9_1064
    | spl9_1
    | ~ spl9_328
    | ~ spl9_584
    | spl9_1057 ),
    inference(avatar_split_clause,[],[f7591,f7557,f4209,f2387,f149,f7666])).

fof(f7591,plain,
    ( m1_subset_1(sK5(k11_relat_1(sK1,o_0_0_xboole_0)),sK0)
    | ~ spl9_1
    | ~ spl9_328
    | ~ spl9_584
    | ~ spl9_1057 ),
    inference(unit_resulting_resolution,[],[f150,f2388,f4210,f115,f7558,f2183])).

fof(f7661,plain,
    ( ~ spl9_1063
    | spl9_143
    | ~ spl9_286
    | spl9_1057 ),
    inference(avatar_split_clause,[],[f7589,f7557,f2061,f975,f7659])).

fof(f7589,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_143
    | ~ spl9_286
    | ~ spl9_1057 ),
    inference(unit_resulting_resolution,[],[f976,f2062,f7558,f1863])).

fof(f7605,plain,
    ( ~ spl9_1061
    | ~ spl9_6
    | spl9_1057 ),
    inference(avatar_split_clause,[],[f7580,f7557,f170,f7603])).

fof(f7603,plain,
    ( spl9_1061
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1061])])).

fof(f7580,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_1057 ),
    inference(unit_resulting_resolution,[],[f7558,f232])).

fof(f7598,plain,
    ( ~ spl9_1059
    | spl9_1057 ),
    inference(avatar_split_clause,[],[f7564,f7557,f7596])).

fof(f7564,plain,
    ( ~ v1_xboole_0(sK4(k11_relat_1(sK1,o_0_0_xboole_0)))
    | ~ spl9_1057 ),
    inference(unit_resulting_resolution,[],[f114,f7558,f110])).

fof(f7562,plain,
    ( ~ spl9_1055
    | spl9_1056
    | spl9_115
    | ~ spl9_336 ),
    inference(avatar_split_clause,[],[f3069,f2433,f819,f7560,f7554])).

fof(f7554,plain,
    ( spl9_1055
  <=> ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1055])])).

fof(f3069,plain,
    ( v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_115
    | ~ spl9_336 ),
    inference(subsumption_resolution,[],[f3054,f820])).

fof(f3054,plain,
    ( v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_336 ),
    inference(resolution,[],[f1863,f2434])).

fof(f7549,plain,
    ( ~ spl9_1053
    | spl9_23
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7478,f7439,f239,f7547])).

fof(f7547,plain,
    ( spl9_1053
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1053])])).

fof(f7478,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK0))
    | ~ spl9_23
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f240,f258,f7440,f1863])).

fof(f7542,plain,
    ( ~ spl9_1051
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7466,f7439,f7540])).

fof(f7540,plain,
    ( spl9_1051
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1051])])).

fof(f7466,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(sK0)),sK4(sK0))
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f258,f7440,f289])).

fof(f7535,plain,
    ( spl9_1048
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7450,f7439,f7533])).

fof(f7450,plain,
    ( r2_hidden(sK4(sK0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f258,f7440,f119])).

fof(f7528,plain,
    ( ~ spl9_1047
    | spl9_149
    | spl9_223
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7480,f7439,f1615,f1010,f7526])).

fof(f7526,plain,
    ( spl9_1047
  <=> ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1047])])).

fof(f7480,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),o_0_0_xboole_0)
    | ~ spl9_149
    | ~ spl9_223
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f1616,f1011,f258,f7440,f2181])).

fof(f7502,plain,
    ( ~ spl9_1045
    | ~ spl9_6
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7464,f7439,f170,f7500])).

fof(f7500,plain,
    ( spl9_1045
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1045])])).

fof(f7464,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_6
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f7440,f232])).

fof(f7495,plain,
    ( ~ spl9_1043
    | spl9_1041 ),
    inference(avatar_split_clause,[],[f7448,f7439,f7493])).

fof(f7448,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | ~ spl9_1041 ),
    inference(unit_resulting_resolution,[],[f114,f7440,f110])).

fof(f7444,plain,
    ( ~ spl9_1039
    | spl9_1040
    | spl9_115
    | ~ spl9_328 ),
    inference(avatar_split_clause,[],[f3068,f2387,f819,f7442,f7436])).

fof(f7436,plain,
    ( spl9_1039
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1039])])).

fof(f7442,plain,
    ( spl9_1040
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1040])])).

fof(f3068,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_115
    | ~ spl9_328 ),
    inference(subsumption_resolution,[],[f3047,f820])).

fof(f3047,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_328 ),
    inference(resolution,[],[f1863,f2388])).

fof(f7431,plain,
    ( ~ spl9_1037
    | ~ spl9_6
    | spl9_611 ),
    inference(avatar_split_clause,[],[f4377,f4351,f170,f7429])).

fof(f7429,plain,
    ( spl9_1037
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1037])])).

fof(f4351,plain,
    ( spl9_611
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_611])])).

fof(f4377,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK5(sK0)))))
    | ~ spl9_6
    | ~ spl9_611 ),
    inference(unit_resulting_resolution,[],[f4352,f232])).

fof(f4352,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK0)))))
    | ~ spl9_611 ),
    inference(avatar_component_clause,[],[f4351])).

fof(f7424,plain,
    ( ~ spl9_1035
    | spl9_611 ),
    inference(avatar_split_clause,[],[f4369,f4351,f7422])).

fof(f7422,plain,
    ( spl9_1035
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1035])])).

fof(f4369,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK5(sK0))))))
    | ~ spl9_611 ),
    inference(unit_resulting_resolution,[],[f114,f4352,f110])).

fof(f7417,plain,
    ( ~ spl9_1033
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(avatar_split_clause,[],[f3989,f3933,f170,f7415])).

fof(f7415,plain,
    ( spl9_1033
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1033])])).

fof(f3933,plain,
    ( spl9_538
  <=> r2_hidden(sK5(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_538])])).

fof(f3989,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(unit_resulting_resolution,[],[f115,f3934,f1510])).

fof(f3934,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_538 ),
    inference(avatar_component_clause,[],[f3933])).

fof(f7410,plain,
    ( spl9_1030
    | ~ spl9_40
    | spl9_449
    | ~ spl9_996 ),
    inference(avatar_split_clause,[],[f7401,f6950,f3308,f327,f7408])).

fof(f7408,plain,
    ( spl9_1030
  <=> v1_funct_1(sK7(k2_zfmisc_1(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1030])])).

fof(f6950,plain,
    ( spl9_996
  <=> m2_filter_1(sK7(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_996])])).

fof(f7401,plain,
    ( v1_funct_1(sK7(k2_zfmisc_1(sK0,sK0),sK1))
    | ~ spl9_40
    | ~ spl9_449
    | ~ spl9_996 ),
    inference(unit_resulting_resolution,[],[f328,f3309,f6951,f127])).

fof(f6951,plain,
    ( m2_filter_1(sK7(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl9_996 ),
    inference(avatar_component_clause,[],[f6950])).

fof(f7400,plain,
    ( ~ spl9_1029
    | ~ spl9_6
    | spl9_535 ),
    inference(avatar_split_clause,[],[f3975,f3916,f170,f7398])).

fof(f7398,plain,
    ( spl9_1029
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1029])])).

fof(f3916,plain,
    ( spl9_535
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_535])])).

fof(f3975,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl9_6
    | ~ spl9_535 ),
    inference(unit_resulting_resolution,[],[f3917,f232])).

fof(f3917,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl9_535 ),
    inference(avatar_component_clause,[],[f3916])).

fof(f7393,plain,
    ( ~ spl9_1027
    | spl9_535 ),
    inference(avatar_split_clause,[],[f3967,f3916,f7391])).

fof(f7391,plain,
    ( spl9_1027
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1027])])).

fof(f3967,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK1))))))
    | ~ spl9_535 ),
    inference(unit_resulting_resolution,[],[f114,f3917,f110])).

fof(f7386,plain,
    ( ~ spl9_1025
    | ~ spl9_238
    | spl9_409 ),
    inference(avatar_split_clause,[],[f3012,f2978,f1744,f7384])).

fof(f1744,plain,
    ( spl9_238
  <=> r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f3012,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_238
    | ~ spl9_409 ),
    inference(unit_resulting_resolution,[],[f1745,f2979,f142])).

fof(f1745,plain,
    ( r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_238 ),
    inference(avatar_component_clause,[],[f1744])).

fof(f7379,plain,
    ( ~ spl9_1023
    | ~ spl9_240
    | spl9_409 ),
    inference(avatar_split_clause,[],[f3010,f2978,f1754,f7377])).

fof(f1754,plain,
    ( spl9_240
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f3010,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_240
    | ~ spl9_409 ),
    inference(unit_resulting_resolution,[],[f1755,f2979,f142])).

fof(f1755,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_240 ),
    inference(avatar_component_clause,[],[f1754])).

fof(f7372,plain,
    ( ~ spl9_1021
    | ~ spl9_6
    | spl9_345 ),
    inference(avatar_split_clause,[],[f2527,f2470,f170,f7370])).

fof(f7370,plain,
    ( spl9_1021
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1021])])).

fof(f2470,plain,
    ( spl9_345
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_345])])).

fof(f2527,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl9_6
    | ~ spl9_345 ),
    inference(unit_resulting_resolution,[],[f2471,f232])).

fof(f2471,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl9_345 ),
    inference(avatar_component_clause,[],[f2470])).

fof(f7361,plain,
    ( ~ spl9_1019
    | spl9_345 ),
    inference(avatar_split_clause,[],[f2521,f2470,f7359])).

fof(f7359,plain,
    ( spl9_1019
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1019])])).

fof(f2521,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(k1_zfmisc_1(sK0))))))
    | ~ spl9_345 ),
    inference(unit_resulting_resolution,[],[f114,f2471,f110])).

fof(f7354,plain,
    ( ~ spl9_1017
    | spl9_333 ),
    inference(avatar_split_clause,[],[f2419,f2413,f7352])).

fof(f7352,plain,
    ( spl9_1017
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1017])])).

fof(f2419,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_333 ),
    inference(unit_resulting_resolution,[],[f115,f2414,f142])).

fof(f7347,plain,
    ( ~ spl9_1015
    | spl9_111 ),
    inference(avatar_split_clause,[],[f848,f797,f7345])).

fof(f7345,plain,
    ( spl9_1015
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1015])])).

fof(f797,plain,
    ( spl9_111
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f848,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_111 ),
    inference(unit_resulting_resolution,[],[f115,f798,f142])).

fof(f798,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_111 ),
    inference(avatar_component_clause,[],[f797])).

fof(f7340,plain,
    ( spl9_1012
    | ~ spl9_40
    | spl9_411
    | ~ spl9_962 ),
    inference(avatar_split_clause,[],[f7331,f6817,f2981,f327,f7338])).

fof(f7338,plain,
    ( spl9_1012
  <=> v1_funct_1(sK7(sK5(k1_zfmisc_1(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1012])])).

fof(f6817,plain,
    ( spl9_962
  <=> m2_filter_1(sK7(sK5(k1_zfmisc_1(sK0)),sK1),sK5(k1_zfmisc_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_962])])).

fof(f7331,plain,
    ( v1_funct_1(sK7(sK5(k1_zfmisc_1(sK0)),sK1))
    | ~ spl9_40
    | ~ spl9_411
    | ~ spl9_962 ),
    inference(unit_resulting_resolution,[],[f328,f2982,f6818,f127])).

fof(f6818,plain,
    ( m2_filter_1(sK7(sK5(k1_zfmisc_1(sK0)),sK1),sK5(k1_zfmisc_1(sK0)),sK1)
    | ~ spl9_962 ),
    inference(avatar_component_clause,[],[f6817])).

fof(f7329,plain,
    ( ~ spl9_1011
    | spl9_319 ),
    inference(avatar_split_clause,[],[f2323,f2317,f7327])).

fof(f7327,plain,
    ( spl9_1011
  <=> ~ r2_hidden(k1_zfmisc_1(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1011])])).

fof(f2323,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_319 ),
    inference(unit_resulting_resolution,[],[f115,f2318,f142])).

fof(f7168,plain,
    ( spl9_1008
    | ~ spl9_938 ),
    inference(avatar_split_clause,[],[f7159,f6733,f7166])).

fof(f7166,plain,
    ( spl9_1008
  <=> v1_relat_1(sK7(sK8,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1008])])).

fof(f6733,plain,
    ( spl9_938
  <=> m1_subset_1(sK7(sK8,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_938])])).

fof(f7159,plain,
    ( v1_relat_1(sK7(sK8,sK1))
    | ~ spl9_938 ),
    inference(unit_resulting_resolution,[],[f6734,f136])).

fof(f6734,plain,
    ( m1_subset_1(sK7(sK8,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
    | ~ spl9_938 ),
    inference(avatar_component_clause,[],[f6733])).

fof(f7158,plain,
    ( spl9_1006
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_158
    | ~ spl9_662
    | ~ spl9_934 ),
    inference(avatar_split_clause,[],[f6996,f6711,f4719,f1069,f225,f184,f163,f156,f149,f7156])).

fof(f7156,plain,
    ( spl9_1006
  <=> v1_funct_1(k3_filter_1(sK0,sK1,sK7(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1006])])).

fof(f1069,plain,
    ( spl9_158
  <=> v1_funct_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f4719,plain,
    ( spl9_662
  <=> v1_funct_2(sK7(sK0,sK1),k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_662])])).

fof(f6711,plain,
    ( spl9_934
  <=> m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_934])])).

fof(f6996,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK7(sK0,sK1)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_158
    | ~ spl9_662
    | ~ spl9_934 ),
    inference(unit_resulting_resolution,[],[f150,f164,f157,f185,f1070,f226,f4720,f6712,f139])).

fof(f6712,plain,
    ( m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl9_934 ),
    inference(avatar_component_clause,[],[f6711])).

fof(f4720,plain,
    ( v1_funct_2(sK7(sK0,sK1),k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl9_662 ),
    inference(avatar_component_clause,[],[f4719])).

fof(f1070,plain,
    ( v1_funct_1(sK7(sK0,sK1))
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f7008,plain,
    ( spl9_1004
    | ~ spl9_934 ),
    inference(avatar_split_clause,[],[f6999,f6711,f7006])).

fof(f7006,plain,
    ( spl9_1004
  <=> v1_relat_1(sK7(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1004])])).

fof(f6999,plain,
    ( v1_relat_1(sK7(sK0,sK1))
    | ~ spl9_934 ),
    inference(unit_resulting_resolution,[],[f6712,f136])).

fof(f6995,plain,
    ( spl9_1002
    | ~ spl9_40
    | spl9_115
    | ~ spl9_926 ),
    inference(avatar_split_clause,[],[f6986,f6672,f819,f327,f6993])).

fof(f6993,plain,
    ( spl9_1002
  <=> v1_funct_1(sK7(k8_eqrel_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1002])])).

fof(f6672,plain,
    ( spl9_926
  <=> m2_filter_1(sK7(k8_eqrel_1(sK0,sK1),sK1),k8_eqrel_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_926])])).

fof(f6986,plain,
    ( v1_funct_1(sK7(k8_eqrel_1(sK0,sK1),sK1))
    | ~ spl9_40
    | ~ spl9_115
    | ~ spl9_926 ),
    inference(unit_resulting_resolution,[],[f328,f820,f6673,f127])).

fof(f6673,plain,
    ( m2_filter_1(sK7(k8_eqrel_1(sK0,sK1),sK1),k8_eqrel_1(sK0,sK1),sK1)
    | ~ spl9_926 ),
    inference(avatar_component_clause,[],[f6672])).

fof(f6983,plain,
    ( spl9_1000
    | ~ spl9_40
    | spl9_53
    | ~ spl9_918 ),
    inference(avatar_split_clause,[],[f6974,f6640,f394,f327,f6981])).

fof(f6981,plain,
    ( spl9_1000
  <=> v1_funct_1(sK7(sK4(sK4(sK8)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1000])])).

fof(f394,plain,
    ( spl9_53
  <=> ~ v1_xboole_0(sK4(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f6640,plain,
    ( spl9_918
  <=> m2_filter_1(sK7(sK4(sK4(sK8)),sK1),sK4(sK4(sK8)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_918])])).

fof(f6974,plain,
    ( v1_funct_1(sK7(sK4(sK4(sK8)),sK1))
    | ~ spl9_40
    | ~ spl9_53
    | ~ spl9_918 ),
    inference(unit_resulting_resolution,[],[f328,f395,f6641,f127])).

fof(f6641,plain,
    ( m2_filter_1(sK7(sK4(sK4(sK8)),sK1),sK4(sK4(sK8)),sK1)
    | ~ spl9_918 ),
    inference(avatar_component_clause,[],[f6640])).

fof(f395,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK8)))
    | ~ spl9_53 ),
    inference(avatar_component_clause,[],[f394])).

fof(f6973,plain,
    ( spl9_998
    | spl9_33
    | ~ spl9_40
    | ~ spl9_910 ),
    inference(avatar_split_clause,[],[f6964,f6604,f327,f279,f6971])).

fof(f6971,plain,
    ( spl9_998
  <=> v1_funct_1(sK7(sK4(sK4(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_998])])).

fof(f279,plain,
    ( spl9_33
  <=> ~ v1_xboole_0(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f6604,plain,
    ( spl9_910
  <=> m2_filter_1(sK7(sK4(sK4(sK0)),sK1),sK4(sK4(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_910])])).

fof(f6964,plain,
    ( v1_funct_1(sK7(sK4(sK4(sK0)),sK1))
    | ~ spl9_33
    | ~ spl9_40
    | ~ spl9_910 ),
    inference(unit_resulting_resolution,[],[f328,f280,f6605,f127])).

fof(f6605,plain,
    ( m2_filter_1(sK7(sK4(sK4(sK0)),sK1),sK4(sK4(sK0)),sK1)
    | ~ spl9_910 ),
    inference(avatar_component_clause,[],[f6604])).

fof(f280,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK0)))
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f279])).

fof(f6952,plain,
    ( spl9_996
    | ~ spl9_40
    | spl9_449 ),
    inference(avatar_split_clause,[],[f3367,f3308,f327,f6950])).

fof(f3367,plain,
    ( m2_filter_1(sK7(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl9_40
    | ~ spl9_449 ),
    inference(unit_resulting_resolution,[],[f328,f3309,f130])).

fof(f6945,plain,
    ( ~ spl9_995
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(avatar_split_clause,[],[f5014,f4981,f170,f6943])).

fof(f6943,plain,
    ( spl9_995
  <=> ~ r2_hidden(sK5(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_995])])).

fof(f4981,plain,
    ( spl9_714
  <=> r2_hidden(sK5(sK5(sK1)),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_714])])).

fof(f5014,plain,
    ( ~ r2_hidden(sK5(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(unit_resulting_resolution,[],[f115,f4982,f1510])).

fof(f4982,plain,
    ( r2_hidden(sK5(sK5(sK1)),sK5(sK1))
    | ~ spl9_714 ),
    inference(avatar_component_clause,[],[f4981])).

fof(f6938,plain,
    ( ~ spl9_993
    | ~ spl9_6
    | ~ spl9_500
    | ~ spl9_714 ),
    inference(avatar_split_clause,[],[f5011,f4981,f3658,f170,f6936])).

fof(f3658,plain,
    ( spl9_500
  <=> r2_hidden(sK5(sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_500])])).

fof(f5011,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_500
    | ~ spl9_714 ),
    inference(unit_resulting_resolution,[],[f3659,f4982,f1510])).

fof(f3659,plain,
    ( r2_hidden(sK5(sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_500 ),
    inference(avatar_component_clause,[],[f3658])).

fof(f6931,plain,
    ( ~ spl9_991
    | spl9_231
    | ~ spl9_396
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4898,f4872,f2870,f1665,f6929])).

fof(f6929,plain,
    ( spl9_991
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_991])])).

fof(f4898,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK1),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f4873,f127])).

fof(f6924,plain,
    ( ~ spl9_989
    | ~ spl9_40
    | spl9_231
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4896,f4872,f1665,f327,f6922])).

fof(f6922,plain,
    ( spl9_989
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_989])])).

fof(f4896,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK1),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f4873,f127])).

fof(f6917,plain,
    ( ~ spl9_987
    | spl9_231
    | ~ spl9_396
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4504,f4492,f2870,f1665,f6915])).

fof(f6915,plain,
    ( spl9_987
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK8),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_987])])).

fof(f4504,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK8),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f4493,f127])).

fof(f6910,plain,
    ( spl9_984
    | ~ spl9_20
    | spl9_449
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3363,f3314,f3308,f225,f6908])).

fof(f6908,plain,
    ( spl9_984
  <=> m2_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_984])])).

fof(f3363,plain,
    ( m2_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl9_20
    | ~ spl9_449
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f3315,f226,f3309,f126])).

fof(f6903,plain,
    ( ~ spl9_983
    | ~ spl9_40
    | spl9_231
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4502,f4492,f1665,f327,f6901])).

fof(f6901,plain,
    ( spl9_983
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK8),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_983])])).

fof(f4502,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK8),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f4493,f127])).

fof(f6896,plain,
    ( ~ spl9_981
    | spl9_231
    | ~ spl9_396
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4168,f4156,f2870,f1665,f6894])).

fof(f6894,plain,
    ( spl9_981
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_981])])).

fof(f4168,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK0),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f4157,f127])).

fof(f6889,plain,
    ( ~ spl9_979
    | ~ spl9_40
    | spl9_231
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4166,f4156,f1665,f327,f6887])).

fof(f6887,plain,
    ( spl9_979
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_979])])).

fof(f4166,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK5(sK0),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f4157,f127])).

fof(f6882,plain,
    ( ~ spl9_977
    | spl9_231
    | ~ spl9_396
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3724,f3712,f2870,f1665,f6880])).

fof(f6880,plain,
    ( spl9_977
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_977])])).

fof(f3712,plain,
    ( spl9_507
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_507])])).

fof(f3724,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK1),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f3713,f127])).

fof(f3713,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl9_507 ),
    inference(avatar_component_clause,[],[f3712])).

fof(f6875,plain,
    ( ~ spl9_975
    | ~ spl9_40
    | spl9_231
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3722,f3712,f1665,f327,f6873])).

fof(f6873,plain,
    ( spl9_975
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_975])])).

fof(f3722,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK1),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f3713,f127])).

fof(f6854,plain,
    ( ~ spl9_973
    | spl9_231
    | ~ spl9_396
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3353,f3338,f2870,f1665,f6852])).

fof(f6852,plain,
    ( spl9_973
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_973])])).

fof(f3338,plain,
    ( spl9_455
  <=> ~ v1_xboole_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_455])])).

fof(f3353,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK1),sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f3339,f127])).

fof(f3339,plain,
    ( ~ v1_xboole_0(sK4(sK1))
    | ~ spl9_455 ),
    inference(avatar_component_clause,[],[f3338])).

fof(f6847,plain,
    ( ~ spl9_971
    | ~ spl9_40
    | spl9_231
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3351,f3338,f1665,f327,f6845])).

fof(f6845,plain,
    ( spl9_971
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_971])])).

fof(f3351,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK1),sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f3339,f127])).

fof(f6840,plain,
    ( ~ spl9_969
    | spl9_1
    | spl9_411
    | spl9_439 ),
    inference(avatar_split_clause,[],[f3275,f3265,f2981,f149,f6838])).

fof(f6838,plain,
    ( spl9_969
  <=> ~ m2_subset_1(k1_zfmisc_1(sK0),sK0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_969])])).

fof(f3265,plain,
    ( spl9_439
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_439])])).

fof(f3275,plain,
    ( ~ m2_subset_1(k1_zfmisc_1(sK0),sK0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_1
    | ~ spl9_411
    | ~ spl9_439 ),
    inference(unit_resulting_resolution,[],[f150,f2982,f115,f3266,f124])).

fof(f3266,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_439 ),
    inference(avatar_component_clause,[],[f3265])).

fof(f6833,plain,
    ( ~ spl9_967
    | spl9_27
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2927,f2870,f1665,f255,f6831])).

fof(f6831,plain,
    ( spl9_967
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK8),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_967])])).

fof(f2927,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK8),sK3)
    | ~ spl9_27
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f256,f1666,f2871,f127])).

fof(f6826,plain,
    ( ~ spl9_965
    | spl9_23
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2911,f2870,f1665,f239,f6824])).

fof(f6824,plain,
    ( spl9_965
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_965])])).

fof(f2911,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK0),sK3)
    | ~ spl9_23
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f240,f1666,f2871,f127])).

fof(f6819,plain,
    ( spl9_962
    | ~ spl9_40
    | spl9_411 ),
    inference(avatar_split_clause,[],[f2997,f2981,f327,f6817])).

fof(f2997,plain,
    ( m2_filter_1(sK7(sK5(k1_zfmisc_1(sK0)),sK1),sK5(k1_zfmisc_1(sK0)),sK1)
    | ~ spl9_40
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f328,f2982,f130])).

fof(f6812,plain,
    ( ~ spl9_961
    | spl9_221
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2910,f2870,f1665,f1601,f6810])).

fof(f6810,plain,
    ( spl9_961
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(o_0_0_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_961])])).

fof(f2910,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(o_0_0_xboole_0),sK3)
    | ~ spl9_221
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f1602,f1666,f2871,f127])).

fof(f6805,plain,
    ( ~ spl9_959
    | spl9_165
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2902,f2870,f1665,f1106,f6803])).

fof(f6803,plain,
    ( spl9_959
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK8),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_959])])).

fof(f1106,plain,
    ( spl9_165
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).

fof(f2902,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK8),sK3)
    | ~ spl9_165
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f1107,f1666,f2871,f127])).

fof(f1107,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK8))
    | ~ spl9_165 ),
    inference(avatar_component_clause,[],[f1106])).

fof(f6798,plain,
    ( ~ spl9_957
    | spl9_143
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2901,f2870,f1665,f975,f6796])).

fof(f6796,plain,
    ( spl9_957
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_957])])).

fof(f2901,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK0),sK3)
    | ~ spl9_143
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f976,f1666,f2871,f127])).

fof(f6791,plain,
    ( ~ spl9_955
    | spl9_289 ),
    inference(avatar_split_clause,[],[f2116,f2111,f6789])).

fof(f6789,plain,
    ( spl9_955
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_955])])).

fof(f2116,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_289 ),
    inference(unit_resulting_resolution,[],[f115,f2112,f142])).

fof(f6784,plain,
    ( ~ spl9_953
    | spl9_253 ),
    inference(avatar_split_clause,[],[f1876,f1836,f6782])).

fof(f6782,plain,
    ( spl9_953
  <=> ~ r2_hidden(sK4(sK8),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_953])])).

fof(f1836,plain,
    ( spl9_253
  <=> ~ m1_subset_1(sK4(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_253])])).

fof(f1876,plain,
    ( ~ r2_hidden(sK4(sK8),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_253 ),
    inference(unit_resulting_resolution,[],[f115,f1837,f142])).

fof(f1837,plain,
    ( ~ m1_subset_1(sK4(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_253 ),
    inference(avatar_component_clause,[],[f1836])).

fof(f6777,plain,
    ( spl9_950
    | spl9_1
    | spl9_411 ),
    inference(avatar_split_clause,[],[f2993,f2981,f149,f6775])).

fof(f6775,plain,
    ( spl9_950
  <=> m2_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_950])])).

fof(f2993,plain,
    ( m2_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_1
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f115,f2982,f126])).

fof(f6770,plain,
    ( ~ spl9_949
    | spl9_251 ),
    inference(avatar_split_clause,[],[f1872,f1829,f6768])).

fof(f6768,plain,
    ( spl9_949
  <=> ~ r2_hidden(sK4(sK0),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_949])])).

fof(f1872,plain,
    ( ~ r2_hidden(sK4(sK0),sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_251 ),
    inference(unit_resulting_resolution,[],[f115,f1830,f142])).

fof(f6763,plain,
    ( ~ spl9_947
    | spl9_27
    | ~ spl9_40
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1713,f1665,f327,f255,f6761])).

fof(f6761,plain,
    ( spl9_947
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK8),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_947])])).

fof(f1713,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK8),sK1)
    | ~ spl9_27
    | ~ spl9_40
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f256,f328,f1666,f127])).

fof(f6756,plain,
    ( ~ spl9_945
    | spl9_23
    | ~ spl9_40
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1705,f1665,f327,f239,f6754])).

fof(f6754,plain,
    ( spl9_945
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_945])])).

fof(f1705,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(sK0),sK1)
    | ~ spl9_23
    | ~ spl9_40
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f240,f328,f1666,f127])).

fof(f6749,plain,
    ( ~ spl9_943
    | ~ spl9_40
    | spl9_221
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1704,f1665,f1601,f327,f6747])).

fof(f6747,plain,
    ( spl9_943
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(o_0_0_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_943])])).

fof(f1704,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK4(o_0_0_xboole_0),sK1)
    | ~ spl9_40
    | ~ spl9_221
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f1602,f328,f1666,f127])).

fof(f6742,plain,
    ( ~ spl9_941
    | ~ spl9_40
    | spl9_165
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1697,f1665,f1106,f327,f6740])).

fof(f6740,plain,
    ( spl9_941
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK8),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_941])])).

fof(f1697,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK8),sK1)
    | ~ spl9_40
    | ~ spl9_165
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f1107,f328,f1666,f127])).

fof(f6735,plain,
    ( spl9_938
    | spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(avatar_split_clause,[],[f1072,f951,f327,f177,f6733])).

fof(f951,plain,
    ( spl9_138
  <=> m2_filter_1(sK7(sK8,sK1),sK8,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f1072,plain,
    ( m1_subset_1(sK7(sK8,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK8,sK8),sK8)))
    | ~ spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f178,f328,f952,f129])).

fof(f952,plain,
    ( m2_filter_1(sK7(sK8,sK1),sK8,sK1)
    | ~ spl9_138 ),
    inference(avatar_component_clause,[],[f951])).

fof(f6728,plain,
    ( ~ spl9_937
    | ~ spl9_40
    | spl9_143
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1696,f1665,f975,f327,f6726])).

fof(f6726,plain,
    ( spl9_937
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_937])])).

fof(f1696,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),k1_zfmisc_1(sK0),sK1)
    | ~ spl9_40
    | ~ spl9_143
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f976,f328,f1666,f127])).

fof(f6713,plain,
    ( spl9_934
    | spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1059,f944,f327,f149,f6711])).

fof(f944,plain,
    ( spl9_136
  <=> m2_filter_1(sK7(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1059,plain,
    ( m1_subset_1(sK7(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(unit_resulting_resolution,[],[f150,f328,f945,f129])).

fof(f945,plain,
    ( m2_filter_1(sK7(sK0,sK1),sK0,sK1)
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f944])).

fof(f6695,plain,
    ( ~ spl9_933
    | spl9_879
    | spl9_917 ),
    inference(avatar_split_clause,[],[f6645,f6625,f6337,f6693])).

fof(f6693,plain,
    ( spl9_933
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_933])])).

fof(f6337,plain,
    ( spl9_879
  <=> ~ v1_xboole_0(sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_879])])).

fof(f6625,plain,
    ( spl9_917
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_917])])).

fof(f6645,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_879
    | ~ spl9_917 ),
    inference(unit_resulting_resolution,[],[f6338,f6626,f119])).

fof(f6626,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_917 ),
    inference(avatar_component_clause,[],[f6625])).

fof(f6338,plain,
    ( ~ v1_xboole_0(sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_879 ),
    inference(avatar_component_clause,[],[f6337])).

fof(f6688,plain,
    ( ~ spl9_931
    | spl9_879
    | spl9_915 ),
    inference(avatar_split_clause,[],[f6643,f6618,f6337,f6686])).

fof(f6686,plain,
    ( spl9_931
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_931])])).

fof(f6618,plain,
    ( spl9_915
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_915])])).

fof(f6643,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_879
    | ~ spl9_915 ),
    inference(unit_resulting_resolution,[],[f6338,f6619,f119])).

fof(f6619,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_915 ),
    inference(avatar_component_clause,[],[f6618])).

fof(f6681,plain,
    ( ~ spl9_929
    | spl9_913 ),
    inference(avatar_split_clause,[],[f6632,f6611,f6679])).

fof(f6679,plain,
    ( spl9_929
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_929])])).

fof(f6611,plain,
    ( spl9_913
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_913])])).

fof(f6632,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_913 ),
    inference(unit_resulting_resolution,[],[f6612,f117])).

fof(f6612,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_913 ),
    inference(avatar_component_clause,[],[f6611])).

fof(f6674,plain,
    ( spl9_926
    | ~ spl9_40
    | spl9_115 ),
    inference(avatar_split_clause,[],[f825,f819,f327,f6672])).

fof(f825,plain,
    ( m2_filter_1(sK7(k8_eqrel_1(sK0,sK1),sK1),k8_eqrel_1(sK0,sK1),sK1)
    | ~ spl9_40
    | ~ spl9_115 ),
    inference(unit_resulting_resolution,[],[f328,f820,f130])).

fof(f6667,plain,
    ( ~ spl9_925
    | spl9_909 ),
    inference(avatar_split_clause,[],[f6628,f6597,f6665])).

fof(f6665,plain,
    ( spl9_925
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_925])])).

fof(f6597,plain,
    ( spl9_909
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_909])])).

fof(f6628,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_909 ),
    inference(unit_resulting_resolution,[],[f6598,f117])).

fof(f6598,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_909 ),
    inference(avatar_component_clause,[],[f6597])).

fof(f6660,plain,
    ( ~ spl9_923
    | ~ spl9_6
    | spl9_887 ),
    inference(avatar_split_clause,[],[f6431,f6386,f170,f6658])).

fof(f6658,plain,
    ( spl9_923
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_923])])).

fof(f6386,plain,
    ( spl9_887
  <=> ~ v1_xboole_0(sK4(sK4(sK5(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_887])])).

fof(f6431,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_887 ),
    inference(unit_resulting_resolution,[],[f6387,f232])).

fof(f6387,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(o_0_0_xboole_0))))
    | ~ spl9_887 ),
    inference(avatar_component_clause,[],[f6386])).

fof(f6653,plain,
    ( ~ spl9_921
    | spl9_887 ),
    inference(avatar_split_clause,[],[f6423,f6386,f6651])).

fof(f6651,plain,
    ( spl9_921
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_921])])).

fof(f6423,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(o_0_0_xboole_0)))))
    | ~ spl9_887 ),
    inference(unit_resulting_resolution,[],[f114,f6387,f110])).

fof(f6642,plain,
    ( spl9_918
    | ~ spl9_40
    | spl9_53 ),
    inference(avatar_split_clause,[],[f416,f394,f327,f6640])).

fof(f416,plain,
    ( m2_filter_1(sK7(sK4(sK4(sK8)),sK1),sK4(sK4(sK8)),sK1)
    | ~ spl9_40
    | ~ spl9_53 ),
    inference(unit_resulting_resolution,[],[f328,f395,f130])).

fof(f6627,plain,
    ( ~ spl9_917
    | spl9_221
    | ~ spl9_244
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6328,f6300,f6297,f1776,f1601,f6625])).

fof(f6328,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_244
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1602,f1777,f6301,f258,f6298,f2183])).

fof(f6620,plain,
    ( ~ spl9_915
    | ~ spl9_102
    | spl9_223
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6326,f6300,f6297,f1615,f766,f6618])).

fof(f6326,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_102
    | ~ spl9_223
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1616,f767,f6301,f258,f6298,f2183])).

fof(f6613,plain,
    ( ~ spl9_913
    | spl9_221
    | ~ spl9_244
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6325,f6300,f6297,f1776,f1601,f6611])).

fof(f6325,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_244
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1602,f1777,f6301,f6298,f759])).

fof(f6606,plain,
    ( spl9_910
    | spl9_33
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f401,f327,f279,f6604])).

fof(f401,plain,
    ( m2_filter_1(sK7(sK4(sK4(sK0)),sK1),sK4(sK4(sK0)),sK1)
    | ~ spl9_33
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f280,f328,f130])).

fof(f6599,plain,
    ( ~ spl9_909
    | ~ spl9_102
    | spl9_223
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6323,f6300,f6297,f1615,f766,f6597])).

fof(f6323,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_102
    | ~ spl9_223
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f1616,f767,f6301,f6298,f759])).

fof(f6588,plain,
    ( ~ spl9_907
    | spl9_901 ),
    inference(avatar_split_clause,[],[f6570,f6517,f6586])).

fof(f6586,plain,
    ( spl9_907
  <=> ~ r2_hidden(sK5(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_907])])).

fof(f6517,plain,
    ( spl9_901
  <=> ~ m1_subset_1(sK5(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_901])])).

fof(f6570,plain,
    ( ~ r2_hidden(sK5(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_901 ),
    inference(unit_resulting_resolution,[],[f6518,f117])).

fof(f6518,plain,
    ( ~ m1_subset_1(sK5(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_901 ),
    inference(avatar_component_clause,[],[f6517])).

fof(f6567,plain,
    ( ~ spl9_905
    | ~ spl9_6
    | spl9_221
    | ~ spl9_894 ),
    inference(avatar_split_clause,[],[f6508,f6481,f1601,f170,f6565])).

fof(f6565,plain,
    ( spl9_905
  <=> ~ m1_subset_1(sK5(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_905])])).

fof(f6508,plain,
    ( ~ m1_subset_1(sK5(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_894 ),
    inference(unit_resulting_resolution,[],[f6482,f4571])).

fof(f6560,plain,
    ( ~ spl9_903
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(avatar_split_clause,[],[f6507,f6481,f170,f6558])).

fof(f6558,plain,
    ( spl9_903
  <=> ~ r2_hidden(sK5(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_903])])).

fof(f6507,plain,
    ( ~ r2_hidden(sK5(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(unit_resulting_resolution,[],[f6482,f3159])).

fof(f6519,plain,
    ( ~ spl9_901
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(avatar_split_clause,[],[f6503,f6481,f170,f6517])).

fof(f6503,plain,
    ( ~ m1_subset_1(sK5(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_894 ),
    inference(unit_resulting_resolution,[],[f6482,f355])).

fof(f6497,plain,
    ( ~ spl9_899
    | spl9_875 ),
    inference(avatar_split_clause,[],[f6322,f6297,f6495])).

fof(f6495,plain,
    ( spl9_899
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_899])])).

fof(f6322,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK5(o_0_0_xboole_0))))
    | ~ spl9_875 ),
    inference(unit_resulting_resolution,[],[f115,f6298,f142])).

fof(f6490,plain,
    ( ~ spl9_897
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6317,f6300,f6488])).

fof(f6488,plain,
    ( spl9_897
  <=> ~ r2_hidden(sK5(o_0_0_xboole_0),sK5(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_897])])).

fof(f6317,plain,
    ( ~ r2_hidden(sK5(o_0_0_xboole_0),sK5(sK5(o_0_0_xboole_0)))
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f115,f6301,f289])).

fof(f6483,plain,
    ( spl9_894
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6308,f6300,f6481])).

fof(f6308,plain,
    ( r2_hidden(sK5(sK5(o_0_0_xboole_0)),sK5(o_0_0_xboole_0))
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f115,f6301,f119])).

fof(f6421,plain,
    ( ~ spl9_893
    | spl9_879
    | spl9_885 ),
    inference(avatar_split_clause,[],[f6380,f6373,f6337,f6419])).

fof(f6419,plain,
    ( spl9_893
  <=> ~ m1_subset_1(sK0,sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_893])])).

fof(f6373,plain,
    ( spl9_885
  <=> ~ r2_hidden(sK0,sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_885])])).

fof(f6380,plain,
    ( ~ m1_subset_1(sK0,sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_879
    | ~ spl9_885 ),
    inference(unit_resulting_resolution,[],[f6338,f6374,f119])).

fof(f6374,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_885 ),
    inference(avatar_component_clause,[],[f6373])).

fof(f6402,plain,
    ( ~ spl9_891
    | spl9_883 ),
    inference(avatar_split_clause,[],[f6376,f6366,f6400])).

fof(f6400,plain,
    ( spl9_891
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_891])])).

fof(f6366,plain,
    ( spl9_883
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_883])])).

fof(f6376,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_883 ),
    inference(unit_resulting_resolution,[],[f6367,f117])).

fof(f6367,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_883 ),
    inference(avatar_component_clause,[],[f6366])).

fof(f6395,plain,
    ( ~ spl9_889
    | ~ spl9_6
    | spl9_879 ),
    inference(avatar_split_clause,[],[f6360,f6337,f170,f6393])).

fof(f6393,plain,
    ( spl9_889
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_889])])).

fof(f6360,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_879 ),
    inference(unit_resulting_resolution,[],[f6338,f232])).

fof(f6388,plain,
    ( ~ spl9_887
    | spl9_879 ),
    inference(avatar_split_clause,[],[f6352,f6337,f6386])).

fof(f6352,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(o_0_0_xboole_0))))
    | ~ spl9_879 ),
    inference(unit_resulting_resolution,[],[f114,f6338,f110])).

fof(f6375,plain,
    ( ~ spl9_885
    | spl9_1
    | ~ spl9_76
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6327,f6300,f6297,f606,f149,f6373])).

fof(f6327,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_1
    | ~ spl9_76
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f150,f607,f6301,f258,f6298,f2183])).

fof(f6368,plain,
    ( ~ spl9_883
    | spl9_1
    | ~ spl9_76
    | spl9_875
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6324,f6300,f6297,f606,f149,f6366])).

fof(f6324,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(o_0_0_xboole_0)))
    | ~ spl9_1
    | ~ spl9_76
    | ~ spl9_875
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f150,f607,f6301,f6298,f759])).

fof(f6350,plain,
    ( ~ spl9_881
    | ~ spl9_6
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6316,f6300,f170,f6348])).

fof(f6348,plain,
    ( spl9_881
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_881])])).

fof(f6316,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f6301,f232])).

fof(f6339,plain,
    ( ~ spl9_879
    | spl9_877 ),
    inference(avatar_split_clause,[],[f6307,f6300,f6337])).

fof(f6307,plain,
    ( ~ v1_xboole_0(sK4(sK5(o_0_0_xboole_0)))
    | ~ spl9_877 ),
    inference(unit_resulting_resolution,[],[f114,f6301,f110])).

fof(f6305,plain,
    ( ~ spl9_875
    | spl9_876
    | spl9_87
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1574,f1407,f678,f6303,f6297])).

fof(f6303,plain,
    ( spl9_876
  <=> v1_xboole_0(sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_876])])).

fof(f678,plain,
    ( spl9_87
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f1407,plain,
    ( spl9_200
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_200])])).

fof(f1574,plain,
    ( v1_xboole_0(sK5(o_0_0_xboole_0))
    | ~ m1_subset_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0))
    | ~ spl9_87
    | ~ spl9_200 ),
    inference(forward_demodulation,[],[f1554,f1408])).

fof(f1408,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl9_200 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1554,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK5(o_0_0_xboole_0))
    | v1_xboole_0(sK5(sK2))
    | ~ spl9_87
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f691])).

fof(f691,plain,
    ( v1_xboole_0(sK5(sK2))
    | ~ m1_subset_1(sK2,sK5(sK2))
    | ~ spl9_87 ),
    inference(resolution,[],[f679,f119])).

fof(f679,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f678])).

fof(f6272,plain,
    ( ~ spl9_873
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(avatar_split_clause,[],[f4626,f4594,f170,f6270])).

fof(f6270,plain,
    ( spl9_873
  <=> ~ r2_hidden(sK5(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_873])])).

fof(f4594,plain,
    ( spl9_638
  <=> r2_hidden(sK5(sK5(sK8)),sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_638])])).

fof(f4626,plain,
    ( ~ r2_hidden(sK5(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(unit_resulting_resolution,[],[f115,f4595,f1510])).

fof(f4595,plain,
    ( r2_hidden(sK5(sK5(sK8)),sK5(sK8))
    | ~ spl9_638 ),
    inference(avatar_component_clause,[],[f4594])).

fof(f6265,plain,
    ( ~ spl9_871
    | ~ spl9_6
    | spl9_307 ),
    inference(avatar_split_clause,[],[f2301,f2248,f170,f6263])).

fof(f6263,plain,
    ( spl9_871
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_871])])).

fof(f2248,plain,
    ( spl9_307
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK8))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_307])])).

fof(f2301,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK8)))))
    | ~ spl9_6
    | ~ spl9_307 ),
    inference(unit_resulting_resolution,[],[f2249,f232])).

fof(f2249,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK8)))))
    | ~ spl9_307 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f6258,plain,
    ( ~ spl9_869
    | spl9_307 ),
    inference(avatar_split_clause,[],[f2295,f2248,f6256])).

fof(f6256,plain,
    ( spl9_869
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK8)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_869])])).

fof(f2295,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK8))))))
    | ~ spl9_307 ),
    inference(unit_resulting_resolution,[],[f114,f2249,f110])).

fof(f6220,plain,
    ( ~ spl9_867
    | ~ spl9_40
    | ~ spl9_552 ),
    inference(avatar_split_clause,[],[f4059,f4019,f327,f6218])).

fof(f6218,plain,
    ( spl9_867
  <=> ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_867])])).

fof(f4019,plain,
    ( spl9_552
  <=> ! [X0] :
        ( ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_552])])).

fof(f4059,plain,
    ( ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),sK1)
    | ~ spl9_40
    | ~ spl9_552 ),
    inference(unit_resulting_resolution,[],[f328,f4020])).

fof(f4020,plain,
    ( ! [X0] :
        ( ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_552 ),
    inference(avatar_component_clause,[],[f4019])).

fof(f6179,plain,
    ( ~ spl9_865
    | spl9_143
    | ~ spl9_690 ),
    inference(avatar_split_clause,[],[f5645,f4854,f975,f6177])).

fof(f6177,plain,
    ( spl9_865
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_865])])).

fof(f4854,plain,
    ( spl9_690
  <=> m1_subset_1(sK5(k8_eqrel_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_690])])).

fof(f5645,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k8_eqrel_1(sK0,sK1)))
    | ~ spl9_143
    | ~ spl9_690 ),
    inference(unit_resulting_resolution,[],[f976,f4855,f289])).

fof(f4855,plain,
    ( m1_subset_1(sK5(k8_eqrel_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl9_690 ),
    inference(avatar_component_clause,[],[f4854])).

fof(f6172,plain,
    ( spl9_862
    | spl9_143
    | ~ spl9_690 ),
    inference(avatar_split_clause,[],[f5644,f4854,f975,f6170])).

fof(f6170,plain,
    ( spl9_862
  <=> r2_hidden(sK5(k8_eqrel_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_862])])).

fof(f5644,plain,
    ( r2_hidden(sK5(k8_eqrel_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl9_143
    | ~ spl9_690 ),
    inference(unit_resulting_resolution,[],[f976,f4855,f119])).

fof(f6165,plain,
    ( ~ spl9_861
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(avatar_split_clause,[],[f4273,f4248,f170,f6163])).

fof(f6163,plain,
    ( spl9_861
  <=> ~ r2_hidden(sK5(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_861])])).

fof(f4248,plain,
    ( spl9_592
  <=> r2_hidden(sK5(sK5(sK0)),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_592])])).

fof(f4273,plain,
    ( ~ r2_hidden(sK5(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(unit_resulting_resolution,[],[f115,f4249,f1510])).

fof(f4249,plain,
    ( r2_hidden(sK5(sK5(sK0)),sK5(sK0))
    | ~ spl9_592 ),
    inference(avatar_component_clause,[],[f4248])).

fof(f6158,plain,
    ( spl9_858
    | ~ spl9_20
    | spl9_449
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3372,f3314,f3308,f225,f6156])).

fof(f6156,plain,
    ( spl9_858
  <=> m1_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_858])])).

fof(f3372,plain,
    ( m1_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_20
    | ~ spl9_449
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f3315,f226,f3309,f708])).

fof(f6151,plain,
    ( ~ spl9_857
    | ~ spl9_6
    | spl9_497 ),
    inference(avatar_split_clause,[],[f3840,f3641,f170,f6149])).

fof(f6149,plain,
    ( spl9_857
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_857])])).

fof(f3641,plain,
    ( spl9_497
  <=> ~ v1_xboole_0(sK4(sK4(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_497])])).

fof(f3840,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_6
    | ~ spl9_497 ),
    inference(unit_resulting_resolution,[],[f3642,f232])).

fof(f3642,plain,
    ( ~ v1_xboole_0(sK4(sK4(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_497 ),
    inference(avatar_component_clause,[],[f3641])).

fof(f6144,plain,
    ( ~ spl9_855
    | spl9_497 ),
    inference(avatar_split_clause,[],[f3832,f3641,f6142])).

fof(f6142,plain,
    ( spl9_855
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_855])])).

fof(f3832,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl9_497 ),
    inference(unit_resulting_resolution,[],[f114,f3642,f110])).

fof(f6137,plain,
    ( ~ spl9_853
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(avatar_split_clause,[],[f3703,f3620,f170,f6135])).

fof(f6135,plain,
    ( spl9_853
  <=> ~ r2_hidden(sK4(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_853])])).

fof(f3620,plain,
    ( spl9_490
  <=> r2_hidden(sK5(sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_490])])).

fof(f3703,plain,
    ( ~ r2_hidden(sK4(sK1),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(unit_resulting_resolution,[],[f115,f3621,f1510])).

fof(f3621,plain,
    ( r2_hidden(sK5(sK4(sK1)),sK4(sK1))
    | ~ spl9_490 ),
    inference(avatar_component_clause,[],[f3620])).

fof(f6130,plain,
    ( ~ spl9_851
    | ~ spl9_6
    | spl9_427 ),
    inference(avatar_split_clause,[],[f3226,f3177,f170,f6128])).

fof(f6128,plain,
    ( spl9_851
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_851])])).

fof(f3177,plain,
    ( spl9_427
  <=> ~ v1_xboole_0(sK4(sK4(sK5(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_427])])).

fof(f3226,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(k1_zfmisc_1(sK0)))))
    | ~ spl9_6
    | ~ spl9_427 ),
    inference(unit_resulting_resolution,[],[f3178,f232])).

fof(f3178,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(k1_zfmisc_1(sK0)))))
    | ~ spl9_427 ),
    inference(avatar_component_clause,[],[f3177])).

fof(f6123,plain,
    ( ~ spl9_849
    | spl9_427 ),
    inference(avatar_split_clause,[],[f3218,f3177,f6121])).

fof(f6121,plain,
    ( spl9_849
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK5(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_849])])).

fof(f3218,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(k1_zfmisc_1(sK0))))))
    | ~ spl9_427 ),
    inference(unit_resulting_resolution,[],[f114,f3178,f110])).

fof(f5901,plain,
    ( spl9_846
    | ~ spl9_6
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f5893,f1615,f1601,f170,f5899])).

fof(f5893,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f115,f3187,f119])).

fof(f3187,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f1602,f258,f2106])).

fof(f2106,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK6(k1_zfmisc_1(o_0_0_xboole_0),X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl9_6
    | ~ spl9_223 ),
    inference(subsumption_resolution,[],[f2105,f1616])).

fof(f2105,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
        | v1_xboole_0(X0)
        | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,sK6(k1_zfmisc_1(o_0_0_xboole_0),X0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f708,f355])).

fof(f5892,plain,
    ( ~ spl9_845
    | ~ spl9_6
    | spl9_207 ),
    inference(avatar_split_clause,[],[f2090,f1491,f170,f5890])).

fof(f5890,plain,
    ( spl9_845
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_845])])).

fof(f1491,plain,
    ( spl9_207
  <=> ~ v1_xboole_0(sK4(sK4(k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).

fof(f2090,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k8_eqrel_1(sK0,sK1))))
    | ~ spl9_6
    | ~ spl9_207 ),
    inference(unit_resulting_resolution,[],[f1492,f232])).

fof(f1492,plain,
    ( ~ v1_xboole_0(sK4(sK4(k8_eqrel_1(sK0,sK1))))
    | ~ spl9_207 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f5885,plain,
    ( ~ spl9_843
    | spl9_207 ),
    inference(avatar_split_clause,[],[f2084,f1491,f5883])).

fof(f5883,plain,
    ( spl9_843
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k8_eqrel_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_843])])).

fof(f2084,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k8_eqrel_1(sK0,sK1)))))
    | ~ spl9_207 ),
    inference(unit_resulting_resolution,[],[f114,f1492,f110])).

fof(f5878,plain,
    ( spl9_840
    | spl9_1
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3004,f2981,f149,f5876])).

fof(f5876,plain,
    ( spl9_840
  <=> m1_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_840])])).

fof(f3004,plain,
    ( m1_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_1
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f115,f2982,f730])).

fof(f5871,plain,
    ( ~ spl9_839
    | ~ spl9_6
    | spl9_203 ),
    inference(avatar_split_clause,[],[f2081,f1477,f170,f5869])).

fof(f5869,plain,
    ( spl9_839
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_839])])).

fof(f1477,plain,
    ( spl9_203
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_203])])).

fof(f2081,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl9_6
    | ~ spl9_203 ),
    inference(unit_resulting_resolution,[],[f1478,f232])).

fof(f1478,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl9_203 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f5864,plain,
    ( ~ spl9_837
    | spl9_203 ),
    inference(avatar_split_clause,[],[f2075,f1477,f5862])).

fof(f5862,plain,
    ( spl9_837
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_837])])).

fof(f2075,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK4(sK0))))))
    | ~ spl9_203 ),
    inference(unit_resulting_resolution,[],[f114,f1478,f110])).

fof(f5846,plain,
    ( ~ spl9_835
    | ~ spl9_6
    | spl9_819 ),
    inference(avatar_split_clause,[],[f5770,f5751,f170,f5844])).

fof(f5844,plain,
    ( spl9_835
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_835])])).

fof(f5751,plain,
    ( spl9_819
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_819])])).

fof(f5770,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK4(sK8))))
    | ~ spl9_6
    | ~ spl9_819 ),
    inference(unit_resulting_resolution,[],[f5752,f232])).

fof(f5752,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK8))))
    | ~ spl9_819 ),
    inference(avatar_component_clause,[],[f5751])).

fof(f5839,plain,
    ( spl9_832
    | spl9_1
    | spl9_411 ),
    inference(avatar_split_clause,[],[f2992,f2981,f149,f5837])).

fof(f5837,plain,
    ( spl9_832
  <=> m2_subset_1(sK5(sK5(k1_zfmisc_1(sK0))),sK0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_832])])).

fof(f2992,plain,
    ( m2_subset_1(sK5(sK5(k1_zfmisc_1(sK0))),sK0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_1
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f115,f115,f2982,f125])).

fof(f5832,plain,
    ( ~ spl9_831
    | spl9_819 ),
    inference(avatar_split_clause,[],[f5762,f5751,f5830])).

fof(f5762,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK8)))))
    | ~ spl9_819 ),
    inference(unit_resulting_resolution,[],[f114,f5752,f110])).

fof(f5823,plain,
    ( ~ spl9_829
    | spl9_823 ),
    inference(avatar_split_clause,[],[f5789,f5777,f5821])).

fof(f5821,plain,
    ( spl9_829
  <=> ~ r2_hidden(sK4(sK4(sK8)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_829])])).

fof(f5777,plain,
    ( spl9_823
  <=> ~ m1_subset_1(sK4(sK4(sK8)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_823])])).

fof(f5789,plain,
    ( ~ r2_hidden(sK4(sK4(sK8)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_823 ),
    inference(unit_resulting_resolution,[],[f5778,f117])).

fof(f5778,plain,
    ( ~ m1_subset_1(sK4(sK4(sK8)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_823 ),
    inference(avatar_component_clause,[],[f5777])).

fof(f5812,plain,
    ( ~ spl9_827
    | ~ spl9_6
    | spl9_221
    | ~ spl9_802 ),
    inference(avatar_split_clause,[],[f5717,f5555,f1601,f170,f5810])).

fof(f5810,plain,
    ( spl9_827
  <=> ~ m1_subset_1(sK4(sK4(sK8)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_827])])).

fof(f5555,plain,
    ( spl9_802
  <=> r2_hidden(sK5(sK4(sK4(sK8))),sK4(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_802])])).

fof(f5717,plain,
    ( ~ m1_subset_1(sK4(sK4(sK8)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_802 ),
    inference(unit_resulting_resolution,[],[f5556,f4571])).

fof(f5556,plain,
    ( r2_hidden(sK5(sK4(sK4(sK8))),sK4(sK4(sK8)))
    | ~ spl9_802 ),
    inference(avatar_component_clause,[],[f5555])).

fof(f5786,plain,
    ( ~ spl9_825
    | ~ spl9_6
    | ~ spl9_802 ),
    inference(avatar_split_clause,[],[f5716,f5555,f170,f5784])).

fof(f5784,plain,
    ( spl9_825
  <=> ~ r2_hidden(sK4(sK4(sK8)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_825])])).

fof(f5716,plain,
    ( ~ r2_hidden(sK4(sK4(sK8)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_802 ),
    inference(unit_resulting_resolution,[],[f5556,f3159])).

fof(f5779,plain,
    ( ~ spl9_823
    | ~ spl9_6
    | ~ spl9_802 ),
    inference(avatar_split_clause,[],[f5713,f5555,f170,f5777])).

fof(f5713,plain,
    ( ~ m1_subset_1(sK4(sK4(sK8)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_802 ),
    inference(unit_resulting_resolution,[],[f5556,f355])).

fof(f5760,plain,
    ( ~ spl9_821
    | ~ spl9_6
    | spl9_817 ),
    inference(avatar_split_clause,[],[f5742,f5726,f170,f5758])).

fof(f5758,plain,
    ( spl9_821
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_821])])).

fof(f5726,plain,
    ( spl9_817
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_817])])).

fof(f5742,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK8)))
    | ~ spl9_6
    | ~ spl9_817 ),
    inference(unit_resulting_resolution,[],[f5727,f232])).

fof(f5727,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4(sK8)))
    | ~ spl9_817 ),
    inference(avatar_component_clause,[],[f5726])).

fof(f5753,plain,
    ( ~ spl9_819
    | spl9_817 ),
    inference(avatar_split_clause,[],[f5732,f5726,f5751])).

fof(f5732,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK8))))
    | ~ spl9_817 ),
    inference(unit_resulting_resolution,[],[f114,f5727,f110])).

fof(f5728,plain,
    ( ~ spl9_817
    | ~ spl9_802 ),
    inference(avatar_split_clause,[],[f5712,f5555,f5726])).

fof(f5712,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4(sK8)))
    | ~ spl9_802 ),
    inference(unit_resulting_resolution,[],[f258,f5556,f143])).

fof(f5704,plain,
    ( ~ spl9_815
    | spl9_171 ),
    inference(avatar_split_clause,[],[f1145,f1141,f5702])).

fof(f5702,plain,
    ( spl9_815
  <=> ~ r2_hidden(sK4(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_815])])).

fof(f1145,plain,
    ( ~ r2_hidden(sK4(sK8),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_171 ),
    inference(unit_resulting_resolution,[],[f115,f1142,f142])).

fof(f5697,plain,
    ( ~ spl9_237
    | spl9_220
    | spl9_127 ),
    inference(avatar_split_clause,[],[f895,f892,f1598,f1686])).

fof(f1686,plain,
    ( spl9_237
  <=> ~ m1_subset_1(sK8,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_237])])).

fof(f1598,plain,
    ( spl9_220
  <=> v1_xboole_0(sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_220])])).

fof(f892,plain,
    ( spl9_127
  <=> ~ r2_hidden(sK8,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f895,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ m1_subset_1(sK8,sK4(o_0_0_xboole_0))
    | ~ spl9_127 ),
    inference(resolution,[],[f893,f119])).

fof(f893,plain,
    ( ~ r2_hidden(sK8,sK4(o_0_0_xboole_0))
    | ~ spl9_127 ),
    inference(avatar_component_clause,[],[f892])).

fof(f5643,plain,
    ( ~ spl9_813
    | spl9_53 ),
    inference(avatar_split_clause,[],[f1858,f394,f5641])).

fof(f5641,plain,
    ( spl9_813
  <=> ~ r2_hidden(sK4(sK4(sK8)),sK5(sK4(sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_813])])).

fof(f1858,plain,
    ( ~ r2_hidden(sK4(sK4(sK8)),sK5(sK4(sK4(sK8))))
    | ~ spl9_53 ),
    inference(unit_resulting_resolution,[],[f395,f115,f289])).

fof(f5597,plain,
    ( ~ spl9_811
    | spl9_451
    | ~ spl9_616 ),
    inference(avatar_split_clause,[],[f4481,f4394,f3314,f5595])).

fof(f5595,plain,
    ( spl9_811
  <=> ~ r2_hidden(sK1,sK6(k2_zfmisc_1(sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_811])])).

fof(f4394,plain,
    ( spl9_616
  <=> m1_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_616])])).

fof(f4481,plain,
    ( ~ r2_hidden(sK1,sK6(k2_zfmisc_1(sK0,sK0),sK1))
    | ~ spl9_451
    | ~ spl9_616 ),
    inference(unit_resulting_resolution,[],[f3315,f4395,f289])).

fof(f4395,plain,
    ( m1_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),sK1)
    | ~ spl9_616 ),
    inference(avatar_component_clause,[],[f4394])).

fof(f5590,plain,
    ( spl9_808
    | spl9_451
    | ~ spl9_616 ),
    inference(avatar_split_clause,[],[f4479,f4394,f3314,f5588])).

fof(f5588,plain,
    ( spl9_808
  <=> r2_hidden(sK6(k2_zfmisc_1(sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_808])])).

fof(f4479,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK0),sK1),sK1)
    | ~ spl9_451
    | ~ spl9_616 ),
    inference(unit_resulting_resolution,[],[f3315,f4395,f119])).

fof(f5576,plain,
    ( ~ spl9_807
    | spl9_225
    | spl9_799 ),
    inference(avatar_split_clause,[],[f5558,f5537,f1644,f5574])).

fof(f5574,plain,
    ( spl9_807
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_807])])).

fof(f5537,plain,
    ( spl9_799
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_799])])).

fof(f5558,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_799 ),
    inference(unit_resulting_resolution,[],[f1645,f5538,f119])).

fof(f5538,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_799 ),
    inference(avatar_component_clause,[],[f5537])).

fof(f5569,plain,
    ( ~ spl9_805
    | spl9_797 ),
    inference(avatar_split_clause,[],[f5547,f5530,f5567])).

fof(f5567,plain,
    ( spl9_805
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_805])])).

fof(f5530,plain,
    ( spl9_797
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_797])])).

fof(f5547,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_797 ),
    inference(unit_resulting_resolution,[],[f5531,f117])).

fof(f5531,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_797 ),
    inference(avatar_component_clause,[],[f5530])).

fof(f5557,plain,
    ( spl9_802
    | spl9_53 ),
    inference(avatar_split_clause,[],[f417,f394,f5555])).

fof(f417,plain,
    ( r2_hidden(sK5(sK4(sK4(sK8))),sK4(sK4(sK8)))
    | ~ spl9_53 ),
    inference(unit_resulting_resolution,[],[f115,f395,f119])).

fof(f5546,plain,
    ( ~ spl9_801
    | spl9_247
    | spl9_795 ),
    inference(avatar_split_clause,[],[f5524,f5512,f1792,f5544])).

fof(f5544,plain,
    ( spl9_801
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_801])])).

fof(f5512,plain,
    ( spl9_795
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_795])])).

fof(f5524,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_247
    | ~ spl9_795 ),
    inference(unit_resulting_resolution,[],[f1793,f5513,f119])).

fof(f5513,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_795 ),
    inference(avatar_component_clause,[],[f5512])).

fof(f5539,plain,
    ( ~ spl9_799
    | spl9_143
    | spl9_221
    | spl9_793 ),
    inference(avatar_split_clause,[],[f5520,f5505,f1601,f975,f5537])).

fof(f5505,plain,
    ( spl9_793
  <=> ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_793])])).

fof(f5520,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_143
    | ~ spl9_221
    | ~ spl9_793 ),
    inference(unit_resulting_resolution,[],[f976,f1602,f115,f258,f5506,f2183])).

fof(f5506,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_793 ),
    inference(avatar_component_clause,[],[f5505])).

fof(f5532,plain,
    ( ~ spl9_797
    | spl9_143
    | spl9_221
    | spl9_793 ),
    inference(avatar_split_clause,[],[f5519,f5505,f1601,f975,f5530])).

fof(f5519,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_143
    | ~ spl9_221
    | ~ spl9_793 ),
    inference(unit_resulting_resolution,[],[f976,f1602,f115,f5506,f759])).

fof(f5514,plain,
    ( ~ spl9_795
    | spl9_143
    | spl9_223
    | spl9_781 ),
    inference(avatar_split_clause,[],[f5445,f5425,f1615,f975,f5512])).

fof(f5425,plain,
    ( spl9_781
  <=> ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_781])])).

fof(f5445,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_143
    | ~ spl9_223
    | ~ spl9_781 ),
    inference(unit_resulting_resolution,[],[f976,f1616,f115,f258,f5426,f2183])).

fof(f5426,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_781 ),
    inference(avatar_component_clause,[],[f5425])).

fof(f5507,plain,
    ( ~ spl9_793
    | spl9_221
    | spl9_223
    | spl9_781 ),
    inference(avatar_split_clause,[],[f5443,f5425,f1615,f1601,f5505])).

fof(f5443,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_781 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f5426,f759])).

fof(f5499,plain,
    ( ~ spl9_791
    | spl9_787 ),
    inference(avatar_split_clause,[],[f5473,f5462,f5497])).

fof(f5497,plain,
    ( spl9_791
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_791])])).

fof(f5462,plain,
    ( spl9_787
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_787])])).

fof(f5473,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_787 ),
    inference(unit_resulting_resolution,[],[f5463,f117])).

fof(f5463,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_787 ),
    inference(avatar_component_clause,[],[f5462])).

fof(f5471,plain,
    ( ~ spl9_789
    | spl9_781 ),
    inference(avatar_split_clause,[],[f5438,f5425,f5469])).

fof(f5469,plain,
    ( spl9_789
  <=> ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_789])])).

fof(f5438,plain,
    ( ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_781 ),
    inference(unit_resulting_resolution,[],[f5426,f117])).

fof(f5464,plain,
    ( ~ spl9_787
    | ~ spl9_6
    | ~ spl9_210
    | ~ spl9_706 ),
    inference(avatar_split_clause,[],[f5413,f4942,f1519,f170,f5462])).

fof(f1519,plain,
    ( spl9_210
  <=> r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f4942,plain,
    ( spl9_706
  <=> r2_hidden(sK5(sK5(k1_zfmisc_1(sK0))),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_706])])).

fof(f5413,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_210
    | ~ spl9_706 ),
    inference(unit_resulting_resolution,[],[f1520,f4943,f1510])).

fof(f4943,plain,
    ( r2_hidden(sK5(sK5(k1_zfmisc_1(sK0))),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_706 ),
    inference(avatar_component_clause,[],[f4942])).

fof(f1520,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_210 ),
    inference(avatar_component_clause,[],[f1519])).

fof(f5454,plain,
    ( ~ spl9_785
    | spl9_143
    | spl9_223
    | spl9_781 ),
    inference(avatar_split_clause,[],[f5436,f5425,f1615,f975,f5452])).

fof(f5452,plain,
    ( spl9_785
  <=> ~ m1_eqrel_1(k1_zfmisc_1(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_785])])).

fof(f5436,plain,
    ( ~ m1_eqrel_1(k1_zfmisc_1(sK0),o_0_0_xboole_0)
    | ~ spl9_143
    | ~ spl9_223
    | ~ spl9_781 ),
    inference(unit_resulting_resolution,[],[f976,f1616,f115,f5426,f2181])).

fof(f5434,plain,
    ( ~ spl9_783
    | ~ spl9_6
    | ~ spl9_706 ),
    inference(avatar_split_clause,[],[f5416,f4942,f170,f5432])).

fof(f5432,plain,
    ( spl9_783
  <=> ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_783])])).

fof(f5416,plain,
    ( ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_706 ),
    inference(unit_resulting_resolution,[],[f4943,f3159])).

fof(f5427,plain,
    ( ~ spl9_781
    | ~ spl9_6
    | ~ spl9_706 ),
    inference(avatar_split_clause,[],[f5412,f4942,f170,f5425])).

fof(f5412,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_706 ),
    inference(unit_resulting_resolution,[],[f4943,f355])).

fof(f5404,plain,
    ( ~ spl9_779
    | spl9_1
    | ~ spl9_600 ),
    inference(avatar_split_clause,[],[f4464,f4289,f149,f5402])).

fof(f5402,plain,
    ( spl9_779
  <=> ~ r2_hidden(sK0,sK6(sK0,sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_779])])).

fof(f4289,plain,
    ( spl9_600
  <=> m1_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_600])])).

fof(f4464,plain,
    ( ~ r2_hidden(sK0,sK6(sK0,sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1
    | ~ spl9_600 ),
    inference(unit_resulting_resolution,[],[f150,f4290,f289])).

fof(f4290,plain,
    ( m1_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_600 ),
    inference(avatar_component_clause,[],[f4289])).

fof(f5397,plain,
    ( spl9_776
    | spl9_1
    | ~ spl9_600 ),
    inference(avatar_split_clause,[],[f4461,f4289,f149,f5395])).

fof(f5395,plain,
    ( spl9_776
  <=> r2_hidden(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_776])])).

fof(f4461,plain,
    ( r2_hidden(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_600 ),
    inference(unit_resulting_resolution,[],[f150,f4290,f119])).

fof(f5386,plain,
    ( ~ spl9_775
    | spl9_221
    | spl9_223
    | spl9_761 ),
    inference(avatar_split_clause,[],[f5295,f5278,f1615,f1601,f5384])).

fof(f5384,plain,
    ( spl9_775
  <=> ~ m1_subset_1(sK4(sK4(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_775])])).

fof(f5278,plain,
    ( spl9_761
  <=> ~ m1_subset_1(sK4(sK4(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_761])])).

fof(f5295,plain,
    ( ~ m1_subset_1(sK4(sK4(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_761 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f5279,f759])).

fof(f5279,plain,
    ( ~ m1_subset_1(sK4(sK4(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_761 ),
    inference(avatar_component_clause,[],[f5278])).

fof(f5367,plain,
    ( ~ spl9_773
    | ~ spl9_6
    | spl9_709 ),
    inference(avatar_split_clause,[],[f4968,f4949,f170,f5365])).

fof(f5365,plain,
    ( spl9_773
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_773])])).

fof(f4949,plain,
    ( spl9_709
  <=> ~ v1_xboole_0(sK4(sK4(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_709])])).

fof(f4968,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK1))))
    | ~ spl9_6
    | ~ spl9_709 ),
    inference(unit_resulting_resolution,[],[f4950,f232])).

fof(f4950,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK1))))
    | ~ spl9_709 ),
    inference(avatar_component_clause,[],[f4949])).

fof(f5360,plain,
    ( ~ spl9_771
    | spl9_709 ),
    inference(avatar_split_clause,[],[f4960,f4949,f5358])).

fof(f4960,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK1)))))
    | ~ spl9_709 ),
    inference(unit_resulting_resolution,[],[f114,f4950,f110])).

fof(f5327,plain,
    ( ~ spl9_769
    | ~ spl9_6
    | spl9_747 ),
    inference(avatar_split_clause,[],[f5189,f5170,f170,f5325])).

fof(f5325,plain,
    ( spl9_769
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_769])])).

fof(f5170,plain,
    ( spl9_747
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_747])])).

fof(f5189,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK4(sK0))))
    | ~ spl9_6
    | ~ spl9_747 ),
    inference(unit_resulting_resolution,[],[f5171,f232])).

fof(f5171,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK0))))
    | ~ spl9_747 ),
    inference(avatar_component_clause,[],[f5170])).

fof(f5320,plain,
    ( ~ spl9_767
    | spl9_747 ),
    inference(avatar_split_clause,[],[f5181,f5170,f5318])).

fof(f5181,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(sK0)))))
    | ~ spl9_747 ),
    inference(unit_resulting_resolution,[],[f114,f5171,f110])).

fof(f5311,plain,
    ( ~ spl9_765
    | spl9_761 ),
    inference(avatar_split_clause,[],[f5291,f5278,f5309])).

fof(f5309,plain,
    ( spl9_765
  <=> ~ r2_hidden(sK4(sK4(sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_765])])).

fof(f5291,plain,
    ( ~ r2_hidden(sK4(sK4(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_761 ),
    inference(unit_resulting_resolution,[],[f5279,f117])).

fof(f5288,plain,
    ( ~ spl9_763
    | ~ spl9_6
    | ~ spl9_642 ),
    inference(avatar_split_clause,[],[f5136,f4608,f170,f5286])).

fof(f5286,plain,
    ( spl9_763
  <=> ~ r2_hidden(sK4(sK4(sK0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_763])])).

fof(f4608,plain,
    ( spl9_642
  <=> r2_hidden(sK5(sK4(sK4(sK0))),sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_642])])).

fof(f5136,plain,
    ( ~ r2_hidden(sK4(sK4(sK0)),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_642 ),
    inference(unit_resulting_resolution,[],[f4609,f3159])).

fof(f4609,plain,
    ( r2_hidden(sK5(sK4(sK4(sK0))),sK4(sK4(sK0)))
    | ~ spl9_642 ),
    inference(avatar_component_clause,[],[f4608])).

fof(f5280,plain,
    ( ~ spl9_761
    | ~ spl9_6
    | ~ spl9_642 ),
    inference(avatar_split_clause,[],[f5133,f4608,f170,f5278])).

fof(f5133,plain,
    ( ~ m1_subset_1(sK4(sK4(sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_642 ),
    inference(unit_resulting_resolution,[],[f4609,f355])).

fof(f5269,plain,
    ( ~ spl9_759
    | spl9_225
    | spl9_753 ),
    inference(avatar_split_clause,[],[f5248,f5234,f1644,f5267])).

fof(f5267,plain,
    ( spl9_759
  <=> ~ m1_subset_1(sK1,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_759])])).

fof(f5234,plain,
    ( spl9_753
  <=> ~ r2_hidden(sK1,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_753])])).

fof(f5248,plain,
    ( ~ m1_subset_1(sK1,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_753 ),
    inference(unit_resulting_resolution,[],[f1645,f5235,f119])).

fof(f5235,plain,
    ( ~ r2_hidden(sK1,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_753 ),
    inference(avatar_component_clause,[],[f5234])).

fof(f5262,plain,
    ( ~ spl9_757
    | spl9_751 ),
    inference(avatar_split_clause,[],[f5244,f5224,f5260])).

fof(f5260,plain,
    ( spl9_757
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_757])])).

fof(f5224,plain,
    ( spl9_751
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_751])])).

fof(f5244,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_751 ),
    inference(unit_resulting_resolution,[],[f5225,f117])).

fof(f5225,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_751 ),
    inference(avatar_component_clause,[],[f5224])).

fof(f5243,plain,
    ( ~ spl9_755
    | spl9_247
    | spl9_743 ),
    inference(avatar_split_clause,[],[f5218,f5123,f1792,f5241])).

fof(f5241,plain,
    ( spl9_755
  <=> ~ m1_subset_1(sK1,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_755])])).

fof(f5123,plain,
    ( spl9_743
  <=> ~ r2_hidden(sK1,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_743])])).

fof(f5218,plain,
    ( ~ m1_subset_1(sK1,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_247
    | ~ spl9_743 ),
    inference(unit_resulting_resolution,[],[f1793,f5124,f119])).

fof(f5124,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_743 ),
    inference(avatar_component_clause,[],[f5123])).

fof(f5236,plain,
    ( ~ spl9_753
    | spl9_221
    | spl9_451
    | spl9_741 ),
    inference(avatar_split_clause,[],[f5213,f5116,f3314,f1601,f5234])).

fof(f5116,plain,
    ( spl9_741
  <=> ~ m1_subset_1(sK5(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_741])])).

fof(f5213,plain,
    ( ~ r2_hidden(sK1,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_451
    | ~ spl9_741 ),
    inference(unit_resulting_resolution,[],[f3315,f1602,f115,f258,f5117,f2183])).

fof(f5117,plain,
    ( ~ m1_subset_1(sK5(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_741 ),
    inference(avatar_component_clause,[],[f5116])).

fof(f5226,plain,
    ( ~ spl9_751
    | spl9_221
    | spl9_451
    | spl9_741 ),
    inference(avatar_split_clause,[],[f5211,f5116,f3314,f1601,f5224])).

fof(f5211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_221
    | ~ spl9_451
    | ~ spl9_741 ),
    inference(unit_resulting_resolution,[],[f3315,f115,f1602,f5117,f759])).

fof(f5179,plain,
    ( ~ spl9_749
    | ~ spl9_6
    | spl9_745 ),
    inference(avatar_split_clause,[],[f5161,f5145,f170,f5177])).

fof(f5177,plain,
    ( spl9_749
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_749])])).

fof(f5145,plain,
    ( spl9_745
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_745])])).

fof(f5161,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK4(sK0)))
    | ~ spl9_6
    | ~ spl9_745 ),
    inference(unit_resulting_resolution,[],[f5146,f232])).

fof(f5146,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4(sK0)))
    | ~ spl9_745 ),
    inference(avatar_component_clause,[],[f5145])).

fof(f5172,plain,
    ( ~ spl9_747
    | spl9_745 ),
    inference(avatar_split_clause,[],[f5151,f5145,f5170])).

fof(f5151,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK4(sK0))))
    | ~ spl9_745 ),
    inference(unit_resulting_resolution,[],[f114,f5146,f110])).

fof(f5147,plain,
    ( ~ spl9_745
    | ~ spl9_642 ),
    inference(avatar_split_clause,[],[f5132,f4608,f5145])).

fof(f5132,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK4(sK0)))
    | ~ spl9_642 ),
    inference(unit_resulting_resolution,[],[f258,f4609,f143])).

fof(f5125,plain,
    ( ~ spl9_743
    | spl9_223
    | spl9_451
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5054,f5024,f3314,f1615,f5123])).

fof(f5054,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_223
    | ~ spl9_451
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f3315,f1616,f115,f258,f5025,f2183])).

fof(f5118,plain,
    ( ~ spl9_741
    | spl9_221
    | spl9_223
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5053,f5024,f1615,f1601,f5116])).

fof(f5053,plain,
    ( ~ m1_subset_1(sK5(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f5025,f759])).

fof(f5111,plain,
    ( ~ spl9_739
    | spl9_223
    | spl9_449
    | ~ spl9_484
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5043,f5024,f3589,f3308,f1615,f5109])).

fof(f5109,plain,
    ( spl9_739
  <=> ~ m1_eqrel_1(k2_zfmisc_1(sK0,sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_739])])).

fof(f5043,plain,
    ( ~ m1_eqrel_1(k2_zfmisc_1(sK0,sK0),o_0_0_xboole_0)
    | ~ spl9_223
    | ~ spl9_449
    | ~ spl9_484
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f3309,f3590,f1616,f5025,f2181])).

fof(f5101,plain,
    ( ~ spl9_737
    | spl9_449 ),
    inference(avatar_split_clause,[],[f3371,f3308,f5099])).

fof(f5099,plain,
    ( spl9_737
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK5(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_737])])).

fof(f3371,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK5(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_449 ),
    inference(unit_resulting_resolution,[],[f115,f3309,f289])).

fof(f5094,plain,
    ( ~ spl9_735
    | spl9_725 ),
    inference(avatar_split_clause,[],[f5074,f5031,f5092])).

fof(f5092,plain,
    ( spl9_735
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_735])])).

fof(f5031,plain,
    ( spl9_725
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_725])])).

fof(f5074,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_725 ),
    inference(unit_resulting_resolution,[],[f5032,f117])).

fof(f5032,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_725 ),
    inference(avatar_component_clause,[],[f5031])).

fof(f5087,plain,
    ( ~ spl9_733
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5045,f5024,f5085])).

fof(f5085,plain,
    ( spl9_733
  <=> ~ r2_hidden(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_733])])).

fof(f5045,plain,
    ( ~ r2_hidden(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f5025,f117])).

fof(f5072,plain,
    ( spl9_730
    | spl9_449 ),
    inference(avatar_split_clause,[],[f3361,f3308,f5070])).

fof(f5070,plain,
    ( spl9_730
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK0)),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_730])])).

fof(f3361,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK0)),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_449 ),
    inference(unit_resulting_resolution,[],[f115,f3309,f119])).

fof(f5065,plain,
    ( ~ spl9_729
    | spl9_223
    | spl9_451
    | spl9_723 ),
    inference(avatar_split_clause,[],[f5042,f5024,f3314,f1615,f5063])).

fof(f5063,plain,
    ( spl9_729
  <=> ~ m1_eqrel_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_729])])).

fof(f5042,plain,
    ( ~ m1_eqrel_1(sK1,o_0_0_xboole_0)
    | ~ spl9_223
    | ~ spl9_451
    | ~ spl9_723 ),
    inference(unit_resulting_resolution,[],[f3315,f115,f1616,f5025,f2181])).

fof(f5040,plain,
    ( ~ spl9_727
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(avatar_split_clause,[],[f5015,f4981,f170,f5038])).

fof(f5038,plain,
    ( spl9_727
  <=> ~ r2_hidden(sK5(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_727])])).

fof(f5015,plain,
    ( ~ r2_hidden(sK5(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(unit_resulting_resolution,[],[f4982,f3159])).

fof(f5033,plain,
    ( ~ spl9_725
    | ~ spl9_6
    | ~ spl9_458
    | ~ spl9_714 ),
    inference(avatar_split_clause,[],[f5012,f4981,f3379,f170,f5031])).

fof(f5012,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_458
    | ~ spl9_714 ),
    inference(unit_resulting_resolution,[],[f3380,f4982,f1510])).

fof(f5026,plain,
    ( ~ spl9_723
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(avatar_split_clause,[],[f5010,f4981,f170,f5024])).

fof(f5010,plain,
    ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_714 ),
    inference(unit_resulting_resolution,[],[f4982,f355])).

fof(f5004,plain,
    ( ~ spl9_721
    | spl9_699 ),
    inference(avatar_split_clause,[],[f4911,f4881,f5002])).

fof(f5002,plain,
    ( spl9_721
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(sK5(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_721])])).

fof(f4881,plain,
    ( spl9_699
  <=> ~ m1_subset_1(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_699])])).

fof(f4911,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(sK5(sK1))))
    | ~ spl9_699 ),
    inference(unit_resulting_resolution,[],[f115,f4882,f142])).

fof(f4882,plain,
    ( ~ m1_subset_1(sK1,sK5(sK1))
    | ~ spl9_699 ),
    inference(avatar_component_clause,[],[f4881])).

fof(f4997,plain,
    ( ~ spl9_719
    | spl9_449
    | ~ spl9_484
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4909,f4872,f3589,f3308,f4995])).

fof(f4995,plain,
    ( spl9_719
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_719])])).

fof(f4909,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK5(sK1))
    | ~ spl9_449
    | ~ spl9_484
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f3309,f3590,f4873,f1863])).

fof(f4990,plain,
    ( ~ spl9_717
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4905,f4872,f4988])).

fof(f4988,plain,
    ( spl9_717
  <=> ~ r2_hidden(sK5(sK1),sK5(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_717])])).

fof(f4905,plain,
    ( ~ r2_hidden(sK5(sK1),sK5(sK5(sK1)))
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f115,f4873,f289])).

fof(f4983,plain,
    ( spl9_714
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4893,f4872,f4981])).

fof(f4893,plain,
    ( r2_hidden(sK5(sK5(sK1)),sK5(sK1))
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f115,f4873,f119])).

fof(f4976,plain,
    ( ~ spl9_713
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3002,f2981,f4974])).

fof(f4974,plain,
    ( spl9_713
  <=> ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),sK5(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_713])])).

fof(f3002,plain,
    ( ~ r2_hidden(sK5(k1_zfmisc_1(sK0)),sK5(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f115,f2982,f289])).

fof(f4958,plain,
    ( ~ spl9_711
    | ~ spl9_6
    | spl9_703 ),
    inference(avatar_split_clause,[],[f4936,f4917,f170,f4956])).

fof(f4956,plain,
    ( spl9_711
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_711])])).

fof(f4917,plain,
    ( spl9_703
  <=> ~ v1_xboole_0(sK4(sK5(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_703])])).

fof(f4936,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK1)))
    | ~ spl9_6
    | ~ spl9_703 ),
    inference(unit_resulting_resolution,[],[f4918,f232])).

fof(f4918,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK1)))
    | ~ spl9_703 ),
    inference(avatar_component_clause,[],[f4917])).

fof(f4951,plain,
    ( ~ spl9_709
    | spl9_703 ),
    inference(avatar_split_clause,[],[f4928,f4917,f4949])).

fof(f4928,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK1))))
    | ~ spl9_703 ),
    inference(unit_resulting_resolution,[],[f114,f4918,f110])).

fof(f4944,plain,
    ( spl9_706
    | spl9_411 ),
    inference(avatar_split_clause,[],[f2989,f2981,f4942])).

fof(f2989,plain,
    ( r2_hidden(sK5(sK5(k1_zfmisc_1(sK0))),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f115,f2982,f119])).

fof(f4926,plain,
    ( ~ spl9_705
    | ~ spl9_6
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4902,f4872,f170,f4924])).

fof(f4924,plain,
    ( spl9_705
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_705])])).

fof(f4902,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK1))
    | ~ spl9_6
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f4873,f232])).

fof(f4919,plain,
    ( ~ spl9_703
    | spl9_697 ),
    inference(avatar_split_clause,[],[f4892,f4872,f4917])).

fof(f4892,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK1)))
    | ~ spl9_697 ),
    inference(unit_resulting_resolution,[],[f114,f4873,f110])).

fof(f4890,plain,
    ( ~ spl9_701
    | spl9_115
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f2947,f2679,f819,f4888])).

fof(f4888,plain,
    ( spl9_701
  <=> ~ r2_hidden(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_701])])).

fof(f2947,plain,
    ( ~ r2_hidden(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_115
    | ~ spl9_384 ),
    inference(unit_resulting_resolution,[],[f820,f2680,f289])).

fof(f4883,plain,
    ( spl9_696
    | ~ spl9_699
    | ~ spl9_458 ),
    inference(avatar_split_clause,[],[f3399,f3379,f4881,f4875])).

fof(f4875,plain,
    ( spl9_696
  <=> v1_xboole_0(sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_696])])).

fof(f3399,plain,
    ( ~ m1_subset_1(sK1,sK5(sK1))
    | v1_xboole_0(sK5(sK1))
    | ~ spl9_458 ),
    inference(resolution,[],[f3380,f289])).

fof(f4870,plain,
    ( ~ spl9_695
    | spl9_143
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2550,f2462,f975,f4868])).

fof(f4868,plain,
    ( spl9_695
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k11_relat_1(sK1,sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_695])])).

fof(f2550,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k11_relat_1(sK1,sK5(sK0)))
    | ~ spl9_143
    | ~ spl9_342 ),
    inference(unit_resulting_resolution,[],[f976,f2463,f289])).

fof(f4863,plain,
    ( spl9_692
    | spl9_143
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2549,f2462,f975,f4861])).

fof(f4861,plain,
    ( spl9_692
  <=> r2_hidden(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_692])])).

fof(f2549,plain,
    ( r2_hidden(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_143
    | ~ spl9_342 ),
    inference(unit_resulting_resolution,[],[f976,f2463,f119])).

fof(f4856,plain,
    ( spl9_690
    | spl9_115
    | spl9_143
    | ~ spl9_328 ),
    inference(avatar_split_clause,[],[f2502,f2387,f975,f819,f4854])).

fof(f2502,plain,
    ( m1_subset_1(sK5(k8_eqrel_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_328 ),
    inference(unit_resulting_resolution,[],[f976,f820,f115,f2388,f759])).

fof(f4849,plain,
    ( ~ spl9_689
    | spl9_149 ),
    inference(avatar_split_clause,[],[f1014,f1010,f4847])).

fof(f4847,plain,
    ( spl9_689
  <=> ~ r2_hidden(sK4(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_689])])).

fof(f1014,plain,
    ( ~ r2_hidden(sK4(sK0),sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_149 ),
    inference(unit_resulting_resolution,[],[f115,f1011,f142])).

fof(f4842,plain,
    ( spl9_686
    | spl9_115
    | ~ spl9_384 ),
    inference(avatar_split_clause,[],[f2945,f2679,f819,f4840])).

fof(f2945,plain,
    ( r2_hidden(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_115
    | ~ spl9_384 ),
    inference(unit_resulting_resolution,[],[f820,f2680,f119])).

fof(f4835,plain,
    ( ~ spl9_235
    | spl9_220
    | spl9_125 ),
    inference(avatar_split_clause,[],[f887,f879,f1598,f1679])).

fof(f1679,plain,
    ( spl9_235
  <=> ~ m1_subset_1(sK0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).

fof(f879,plain,
    ( spl9_125
  <=> ~ r2_hidden(sK0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f887,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ m1_subset_1(sK0,sK4(o_0_0_xboole_0))
    | ~ spl9_125 ),
    inference(resolution,[],[f880,f119])).

fof(f880,plain,
    ( ~ r2_hidden(sK0,sK4(o_0_0_xboole_0))
    | ~ spl9_125 ),
    inference(avatar_component_clause,[],[f879])).

fof(f4823,plain,
    ( ~ spl9_685
    | ~ spl9_6
    | spl9_635 ),
    inference(avatar_split_clause,[],[f4588,f4545,f170,f4821])).

fof(f4821,plain,
    ( spl9_685
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_685])])).

fof(f4545,plain,
    ( spl9_635
  <=> ~ v1_xboole_0(sK4(sK4(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_635])])).

fof(f4588,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK8))))
    | ~ spl9_6
    | ~ spl9_635 ),
    inference(unit_resulting_resolution,[],[f4546,f232])).

fof(f4546,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK8))))
    | ~ spl9_635 ),
    inference(avatar_component_clause,[],[f4545])).

fof(f4816,plain,
    ( ~ spl9_683
    | spl9_635 ),
    inference(avatar_split_clause,[],[f4580,f4545,f4814])).

fof(f4580,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK8)))))
    | ~ spl9_635 ),
    inference(unit_resulting_resolution,[],[f114,f4546,f110])).

fof(f4809,plain,
    ( ~ spl9_681
    | spl9_33 ),
    inference(avatar_split_clause,[],[f1855,f279,f4807])).

fof(f4807,plain,
    ( spl9_681
  <=> ~ r2_hidden(sK4(sK4(sK0)),sK5(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_681])])).

fof(f1855,plain,
    ( ~ r2_hidden(sK4(sK4(sK0)),sK5(sK4(sK4(sK0))))
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f280,f115,f289])).

fof(f4796,plain,
    ( ~ spl9_679
    | spl9_225
    | spl9_669 ),
    inference(avatar_split_clause,[],[f4771,f4750,f1644,f4794])).

fof(f4794,plain,
    ( spl9_679
  <=> ~ m1_subset_1(sK8,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_679])])).

fof(f4750,plain,
    ( spl9_669
  <=> ~ r2_hidden(sK8,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_669])])).

fof(f4771,plain,
    ( ~ m1_subset_1(sK8,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_669 ),
    inference(unit_resulting_resolution,[],[f1645,f4751,f119])).

fof(f4751,plain,
    ( ~ r2_hidden(sK8,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_669 ),
    inference(avatar_component_clause,[],[f4750])).

fof(f4789,plain,
    ( ~ spl9_677
    | spl9_115 ),
    inference(avatar_split_clause,[],[f1844,f819,f4787])).

fof(f4787,plain,
    ( spl9_677
  <=> ~ r2_hidden(k8_eqrel_1(sK0,sK1),sK5(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_677])])).

fof(f1844,plain,
    ( ~ r2_hidden(k8_eqrel_1(sK0,sK1),sK5(k8_eqrel_1(sK0,sK1)))
    | ~ spl9_115 ),
    inference(unit_resulting_resolution,[],[f820,f115,f289])).

fof(f4782,plain,
    ( ~ spl9_675
    | spl9_667 ),
    inference(avatar_split_clause,[],[f4767,f4743,f4780])).

fof(f4780,plain,
    ( spl9_675
  <=> ~ r2_hidden(sK8,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_675])])).

fof(f4743,plain,
    ( spl9_667
  <=> ~ m1_subset_1(sK8,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_667])])).

fof(f4767,plain,
    ( ~ r2_hidden(sK8,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_667 ),
    inference(unit_resulting_resolution,[],[f4744,f117])).

fof(f4744,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_667 ),
    inference(avatar_component_clause,[],[f4743])).

fof(f4766,plain,
    ( ~ spl9_673
    | spl9_247
    | spl9_665 ),
    inference(avatar_split_clause,[],[f4737,f4726,f1792,f4764])).

fof(f4764,plain,
    ( spl9_673
  <=> ~ m1_subset_1(sK8,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_673])])).

fof(f4726,plain,
    ( spl9_665
  <=> ~ r2_hidden(sK8,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_665])])).

fof(f4737,plain,
    ( ~ m1_subset_1(sK8,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_247
    | ~ spl9_665 ),
    inference(unit_resulting_resolution,[],[f1793,f4727,f119])).

fof(f4727,plain,
    ( ~ r2_hidden(sK8,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_665 ),
    inference(avatar_component_clause,[],[f4726])).

fof(f4759,plain,
    ( spl9_670
    | spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(avatar_split_clause,[],[f1073,f951,f327,f177,f4757])).

fof(f4757,plain,
    ( spl9_670
  <=> v1_funct_2(sK7(sK8,sK1),k2_zfmisc_1(sK8,sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_670])])).

fof(f1073,plain,
    ( v1_funct_2(sK7(sK8,sK1),k2_zfmisc_1(sK8,sK8),sK8)
    | ~ spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f178,f328,f952,f128])).

fof(f4752,plain,
    ( ~ spl9_669
    | spl9_9
    | spl9_221
    | spl9_661 ),
    inference(avatar_split_clause,[],[f4734,f4712,f1601,f177,f4750])).

fof(f4712,plain,
    ( spl9_661
  <=> ~ m1_subset_1(sK5(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_661])])).

fof(f4734,plain,
    ( ~ r2_hidden(sK8,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_9
    | ~ spl9_221
    | ~ spl9_661 ),
    inference(unit_resulting_resolution,[],[f178,f1602,f115,f258,f4713,f2183])).

fof(f4713,plain,
    ( ~ m1_subset_1(sK5(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_661 ),
    inference(avatar_component_clause,[],[f4712])).

fof(f4745,plain,
    ( ~ spl9_667
    | spl9_9
    | spl9_221
    | spl9_661 ),
    inference(avatar_split_clause,[],[f4733,f4712,f1601,f177,f4743])).

fof(f4733,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_9
    | ~ spl9_221
    | ~ spl9_661 ),
    inference(unit_resulting_resolution,[],[f178,f115,f1602,f4713,f759])).

fof(f4728,plain,
    ( ~ spl9_665
    | spl9_9
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4666,f4636,f1615,f177,f4726])).

fof(f4666,plain,
    ( ~ r2_hidden(sK8,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_9
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f178,f1616,f115,f258,f4637,f2183])).

fof(f4721,plain,
    ( spl9_662
    | spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1060,f944,f327,f149,f4719])).

fof(f1060,plain,
    ( v1_funct_2(sK7(sK0,sK1),k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(unit_resulting_resolution,[],[f150,f328,f945,f128])).

fof(f4714,plain,
    ( ~ spl9_661
    | spl9_221
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4665,f4636,f1615,f1601,f4712])).

fof(f4665,plain,
    ( ~ m1_subset_1(sK5(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f4637,f759])).

fof(f4704,plain,
    ( ~ spl9_659
    | spl9_649 ),
    inference(avatar_split_clause,[],[f4677,f4643,f4702])).

fof(f4702,plain,
    ( spl9_659
  <=> ~ r2_hidden(sK8,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_659])])).

fof(f4643,plain,
    ( spl9_649
  <=> ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_649])])).

fof(f4677,plain,
    ( ~ r2_hidden(sK8,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_649 ),
    inference(unit_resulting_resolution,[],[f4644,f117])).

fof(f4644,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_649 ),
    inference(avatar_component_clause,[],[f4643])).

fof(f4697,plain,
    ( ~ spl9_657
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4659,f4636,f4695])).

fof(f4695,plain,
    ( spl9_657
  <=> ~ r2_hidden(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_657])])).

fof(f4659,plain,
    ( ~ r2_hidden(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f4637,f117])).

fof(f4690,plain,
    ( spl9_654
    | spl9_115 ),
    inference(avatar_split_clause,[],[f824,f819,f4688])).

fof(f4688,plain,
    ( spl9_654
  <=> r2_hidden(sK5(k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_654])])).

fof(f824,plain,
    ( r2_hidden(sK5(k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_115 ),
    inference(unit_resulting_resolution,[],[f115,f820,f119])).

fof(f4675,plain,
    ( ~ spl9_653
    | spl9_9
    | spl9_223
    | spl9_647 ),
    inference(avatar_split_clause,[],[f4657,f4636,f1615,f177,f4673])).

fof(f4673,plain,
    ( spl9_653
  <=> ~ m1_eqrel_1(sK8,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_653])])).

fof(f4657,plain,
    ( ~ m1_eqrel_1(sK8,o_0_0_xboole_0)
    | ~ spl9_9
    | ~ spl9_223
    | ~ spl9_647 ),
    inference(unit_resulting_resolution,[],[f178,f115,f1616,f4637,f2181])).

fof(f4652,plain,
    ( ~ spl9_651
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(avatar_split_clause,[],[f4627,f4594,f170,f4650])).

fof(f4650,plain,
    ( spl9_651
  <=> ~ r2_hidden(sK5(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_651])])).

fof(f4627,plain,
    ( ~ r2_hidden(sK5(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(unit_resulting_resolution,[],[f4595,f3159])).

fof(f4645,plain,
    ( ~ spl9_649
    | ~ spl9_6
    | ~ spl9_42
    | ~ spl9_638 ),
    inference(avatar_split_clause,[],[f4624,f4594,f341,f170,f4643])).

fof(f4624,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_42
    | ~ spl9_638 ),
    inference(unit_resulting_resolution,[],[f342,f4595,f1510])).

fof(f4638,plain,
    ( ~ spl9_647
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(avatar_split_clause,[],[f4623,f4594,f170,f4636])).

fof(f4623,plain,
    ( ~ m1_subset_1(sK5(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_638 ),
    inference(unit_resulting_resolution,[],[f4595,f355])).

fof(f4617,plain,
    ( ~ spl9_645
    | spl9_627 ),
    inference(avatar_split_clause,[],[f4514,f4489,f4615])).

fof(f4615,plain,
    ( spl9_645
  <=> ~ r2_hidden(sK8,sK5(k1_zfmisc_1(sK5(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_645])])).

fof(f4489,plain,
    ( spl9_627
  <=> ~ m1_subset_1(sK8,sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_627])])).

fof(f4514,plain,
    ( ~ r2_hidden(sK8,sK5(k1_zfmisc_1(sK5(sK8))))
    | ~ spl9_627 ),
    inference(unit_resulting_resolution,[],[f115,f4490,f142])).

fof(f4490,plain,
    ( ~ m1_subset_1(sK8,sK5(sK8))
    | ~ spl9_627 ),
    inference(avatar_component_clause,[],[f4489])).

fof(f4610,plain,
    ( spl9_642
    | spl9_33 ),
    inference(avatar_split_clause,[],[f356,f279,f4608])).

fof(f356,plain,
    ( r2_hidden(sK5(sK4(sK4(sK0))),sK4(sK4(sK0)))
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f115,f280,f119])).

fof(f4603,plain,
    ( ~ spl9_641
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4510,f4492,f4601])).

fof(f4601,plain,
    ( spl9_641
  <=> ~ r2_hidden(sK5(sK8),sK5(sK5(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_641])])).

fof(f4510,plain,
    ( ~ r2_hidden(sK5(sK8),sK5(sK5(sK8)))
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f115,f4493,f289])).

fof(f4596,plain,
    ( spl9_638
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4500,f4492,f4594])).

fof(f4500,plain,
    ( r2_hidden(sK5(sK5(sK8)),sK5(sK8))
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f115,f4493,f119])).

fof(f4578,plain,
    ( ~ spl9_637
    | ~ spl9_6
    | spl9_631 ),
    inference(avatar_split_clause,[],[f4539,f4520,f170,f4576])).

fof(f4576,plain,
    ( spl9_637
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_637])])).

fof(f4520,plain,
    ( spl9_631
  <=> ~ v1_xboole_0(sK4(sK5(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_631])])).

fof(f4539,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK8)))
    | ~ spl9_6
    | ~ spl9_631 ),
    inference(unit_resulting_resolution,[],[f4521,f232])).

fof(f4521,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK8)))
    | ~ spl9_631 ),
    inference(avatar_component_clause,[],[f4520])).

fof(f4547,plain,
    ( ~ spl9_635
    | spl9_631 ),
    inference(avatar_split_clause,[],[f4531,f4520,f4545])).

fof(f4531,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK8))))
    | ~ spl9_631 ),
    inference(unit_resulting_resolution,[],[f114,f4521,f110])).

fof(f4529,plain,
    ( ~ spl9_633
    | ~ spl9_6
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4508,f4492,f170,f4527])).

fof(f4527,plain,
    ( spl9_633
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_633])])).

fof(f4508,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK8))
    | ~ spl9_6
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f4493,f232])).

fof(f4522,plain,
    ( ~ spl9_631
    | spl9_629 ),
    inference(avatar_split_clause,[],[f4499,f4492,f4520])).

fof(f4499,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK8)))
    | ~ spl9_629 ),
    inference(unit_resulting_resolution,[],[f114,f4493,f110])).

fof(f4497,plain,
    ( ~ spl9_627
    | spl9_628
    | spl9_55 ),
    inference(avatar_split_clause,[],[f420,f406,f4495,f4489])).

fof(f4495,plain,
    ( spl9_628
  <=> v1_xboole_0(sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_628])])).

fof(f406,plain,
    ( spl9_55
  <=> ~ r2_hidden(sK8,sK5(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f420,plain,
    ( v1_xboole_0(sK5(sK8))
    | ~ m1_subset_1(sK8,sK5(sK8))
    | ~ spl9_55 ),
    inference(resolution,[],[f407,f119])).

fof(f407,plain,
    ( ~ r2_hidden(sK8,sK5(sK8))
    | ~ spl9_55 ),
    inference(avatar_component_clause,[],[f406])).

fof(f4454,plain,
    ( ~ spl9_625
    | spl9_221
    | spl9_223
    | spl9_619 ),
    inference(avatar_split_clause,[],[f4434,f4418,f1615,f1601,f4452])).

fof(f4452,plain,
    ( spl9_625
  <=> ~ m1_subset_1(k8_eqrel_1(sK0,sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_625])])).

fof(f4418,plain,
    ( spl9_619
  <=> ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_619])])).

fof(f4434,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_619 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f4419,f759])).

fof(f4419,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_619 ),
    inference(avatar_component_clause,[],[f4418])).

fof(f4445,plain,
    ( ~ spl9_623
    | spl9_619 ),
    inference(avatar_split_clause,[],[f4430,f4418,f4443])).

fof(f4443,plain,
    ( spl9_623
  <=> ~ r2_hidden(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_623])])).

fof(f4430,plain,
    ( ~ r2_hidden(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_619 ),
    inference(unit_resulting_resolution,[],[f4419,f117])).

fof(f4427,plain,
    ( ~ spl9_621
    | ~ spl9_6
    | ~ spl9_584 ),
    inference(avatar_split_clause,[],[f4408,f4209,f170,f4425])).

fof(f4425,plain,
    ( spl9_621
  <=> ~ r2_hidden(k8_eqrel_1(sK0,sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_621])])).

fof(f4408,plain,
    ( ~ r2_hidden(k8_eqrel_1(sK0,sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_584 ),
    inference(unit_resulting_resolution,[],[f258,f4210,f1510])).

fof(f4420,plain,
    ( ~ spl9_619
    | ~ spl9_6
    | ~ spl9_584 ),
    inference(avatar_split_clause,[],[f4407,f4209,f170,f4418])).

fof(f4407,plain,
    ( ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_584 ),
    inference(unit_resulting_resolution,[],[f4210,f355])).

fof(f4396,plain,
    ( spl9_616
    | ~ spl9_20
    | spl9_449
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3373,f3314,f3308,f225,f4394])).

fof(f3373,plain,
    ( m1_subset_1(sK6(k2_zfmisc_1(sK0,sK0),sK1),sK1)
    | ~ spl9_20
    | ~ spl9_449
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f3315,f226,f3309,f730])).

fof(f4367,plain,
    ( ~ spl9_615
    | ~ spl9_6
    | spl9_587 ),
    inference(avatar_split_clause,[],[f4235,f4216,f170,f4365])).

fof(f4365,plain,
    ( spl9_615
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_615])])).

fof(f4216,plain,
    ( spl9_587
  <=> ~ v1_xboole_0(sK4(sK4(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_587])])).

fof(f4235,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK5(sK0))))
    | ~ spl9_6
    | ~ spl9_587 ),
    inference(unit_resulting_resolution,[],[f4217,f232])).

fof(f4217,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK0))))
    | ~ spl9_587 ),
    inference(avatar_component_clause,[],[f4216])).

fof(f4360,plain,
    ( spl9_612
    | ~ spl9_20
    | spl9_449
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3362,f3314,f3308,f225,f4358])).

fof(f4358,plain,
    ( spl9_612
  <=> m2_subset_1(sK5(sK1),k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_612])])).

fof(f3362,plain,
    ( m2_subset_1(sK5(sK1),k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl9_20
    | ~ spl9_449
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f115,f3315,f226,f3309,f125])).

fof(f4353,plain,
    ( ~ spl9_611
    | spl9_587 ),
    inference(avatar_split_clause,[],[f4227,f4216,f4351])).

fof(f4227,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK5(sK0)))))
    | ~ spl9_587 ),
    inference(unit_resulting_resolution,[],[f114,f4217,f110])).

fof(f4336,plain,
    ( ~ spl9_609
    | spl9_221
    | spl9_223
    | spl9_599 ),
    inference(avatar_split_clause,[],[f4308,f4282,f1615,f1601,f4334])).

fof(f4334,plain,
    ( spl9_609
  <=> ~ m1_subset_1(sK5(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_609])])).

fof(f4308,plain,
    ( ~ m1_subset_1(sK5(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_599 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f4283,f759])).

fof(f4329,plain,
    ( ~ spl9_607
    | spl9_409 ),
    inference(avatar_split_clause,[],[f3013,f2978,f4327])).

fof(f4327,plain,
    ( spl9_607
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_607])])).

fof(f3013,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))))
    | ~ spl9_409 ),
    inference(unit_resulting_resolution,[],[f115,f2979,f142])).

fof(f4320,plain,
    ( ~ spl9_605
    | spl9_599 ),
    inference(avatar_split_clause,[],[f4302,f4282,f4318])).

fof(f4318,plain,
    ( spl9_605
  <=> ~ r2_hidden(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_605])])).

fof(f4302,plain,
    ( ~ r2_hidden(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_599 ),
    inference(unit_resulting_resolution,[],[f4283,f117])).

fof(f4298,plain,
    ( ~ spl9_603
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(avatar_split_clause,[],[f4272,f4248,f170,f4296])).

fof(f4296,plain,
    ( spl9_603
  <=> ~ r2_hidden(sK5(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_603])])).

fof(f4272,plain,
    ( ~ r2_hidden(sK5(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(unit_resulting_resolution,[],[f258,f4249,f1510])).

fof(f4291,plain,
    ( spl9_600
    | spl9_1
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3003,f2981,f149,f4289])).

fof(f3003,plain,
    ( m1_subset_1(sK6(sK0,sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f115,f2982,f708])).

fof(f4284,plain,
    ( ~ spl9_599
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(avatar_split_clause,[],[f4270,f4248,f170,f4282])).

fof(f4270,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_592 ),
    inference(unit_resulting_resolution,[],[f4249,f355])).

fof(f4264,plain,
    ( ~ spl9_597
    | spl9_577 ),
    inference(avatar_split_clause,[],[f4178,f4153,f4262])).

fof(f4262,plain,
    ( spl9_597
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK5(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_597])])).

fof(f4153,plain,
    ( spl9_577
  <=> ~ m1_subset_1(sK0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_577])])).

fof(f4178,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK5(sK0))))
    | ~ spl9_577 ),
    inference(unit_resulting_resolution,[],[f115,f4154,f142])).

fof(f4154,plain,
    ( ~ m1_subset_1(sK0,sK5(sK0))
    | ~ spl9_577 ),
    inference(avatar_component_clause,[],[f4153])).

fof(f4257,plain,
    ( ~ spl9_595
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4174,f4156,f4255])).

fof(f4255,plain,
    ( spl9_595
  <=> ~ r2_hidden(sK5(sK0),sK5(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_595])])).

fof(f4174,plain,
    ( ~ r2_hidden(sK5(sK0),sK5(sK5(sK0)))
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f115,f4157,f289])).

fof(f4250,plain,
    ( spl9_592
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4164,f4156,f4248])).

fof(f4164,plain,
    ( r2_hidden(sK5(sK5(sK0)),sK5(sK0))
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f115,f4157,f119])).

fof(f4243,plain,
    ( ~ spl9_591
    | spl9_115
    | ~ spl9_336 ),
    inference(avatar_split_clause,[],[f2531,f2433,f819,f4241])).

fof(f4241,plain,
    ( spl9_591
  <=> ~ r2_hidden(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_591])])).

fof(f2531,plain,
    ( ~ r2_hidden(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_115
    | ~ spl9_336 ),
    inference(unit_resulting_resolution,[],[f820,f2434,f289])).

fof(f4225,plain,
    ( ~ spl9_589
    | ~ spl9_6
    | spl9_581 ),
    inference(avatar_split_clause,[],[f4203,f4184,f170,f4223])).

fof(f4223,plain,
    ( spl9_589
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_589])])).

fof(f4184,plain,
    ( spl9_581
  <=> ~ v1_xboole_0(sK4(sK5(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_581])])).

fof(f4203,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(sK0)))
    | ~ spl9_6
    | ~ spl9_581 ),
    inference(unit_resulting_resolution,[],[f4185,f232])).

fof(f4185,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK0)))
    | ~ spl9_581 ),
    inference(avatar_component_clause,[],[f4184])).

fof(f4218,plain,
    ( ~ spl9_587
    | spl9_581 ),
    inference(avatar_split_clause,[],[f4195,f4184,f4216])).

fof(f4195,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(sK0))))
    | ~ spl9_581 ),
    inference(unit_resulting_resolution,[],[f114,f4185,f110])).

fof(f4211,plain,
    ( spl9_584
    | spl9_115
    | ~ spl9_336 ),
    inference(avatar_split_clause,[],[f2529,f2433,f819,f4209])).

fof(f2529,plain,
    ( r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_115
    | ~ spl9_336 ),
    inference(unit_resulting_resolution,[],[f820,f2434,f119])).

fof(f4193,plain,
    ( ~ spl9_583
    | ~ spl9_6
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4172,f4156,f170,f4191])).

fof(f4191,plain,
    ( spl9_583
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_583])])).

fof(f4172,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(sK0))
    | ~ spl9_6
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f4157,f232])).

fof(f4186,plain,
    ( ~ spl9_581
    | spl9_579 ),
    inference(avatar_split_clause,[],[f4163,f4156,f4184])).

fof(f4163,plain,
    ( ~ v1_xboole_0(sK4(sK5(sK0)))
    | ~ spl9_579 ),
    inference(unit_resulting_resolution,[],[f114,f4157,f110])).

fof(f4161,plain,
    ( ~ spl9_577
    | spl9_578
    | spl9_45 ),
    inference(avatar_split_clause,[],[f373,f363,f4159,f4153])).

fof(f4159,plain,
    ( spl9_578
  <=> v1_xboole_0(sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_578])])).

fof(f363,plain,
    ( spl9_45
  <=> ~ r2_hidden(sK0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f373,plain,
    ( v1_xboole_0(sK5(sK0))
    | ~ m1_subset_1(sK0,sK5(sK0))
    | ~ spl9_45 ),
    inference(resolution,[],[f364,f119])).

fof(f364,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f363])).

fof(f4148,plain,
    ( ~ spl9_575
    | spl9_225
    | spl9_393 ),
    inference(avatar_split_clause,[],[f2857,f2847,f1644,f4146])).

fof(f4146,plain,
    ( spl9_575
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_575])])).

fof(f2847,plain,
    ( spl9_393
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_393])])).

fof(f2857,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_393 ),
    inference(unit_resulting_resolution,[],[f1645,f2848,f119])).

fof(f2848,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_393 ),
    inference(avatar_component_clause,[],[f2847])).

fof(f4141,plain,
    ( ~ spl9_573
    | ~ spl9_6
    | spl9_269 ),
    inference(avatar_split_clause,[],[f2021,f1962,f170,f4139])).

fof(f4139,plain,
    ( spl9_573
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_573])])).

fof(f1962,plain,
    ( spl9_269
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_269])])).

fof(f2021,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_269 ),
    inference(unit_resulting_resolution,[],[f1963,f232])).

fof(f1963,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_269 ),
    inference(avatar_component_clause,[],[f1962])).

fof(f4133,plain,
    ( ~ spl9_571
    | spl9_473 ),
    inference(avatar_split_clause,[],[f3496,f3470,f4131])).

fof(f4131,plain,
    ( spl9_571
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_571])])).

fof(f3470,plain,
    ( spl9_473
  <=> ~ m1_subset_1(sK1,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_473])])).

fof(f3496,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_473 ),
    inference(unit_resulting_resolution,[],[f115,f3471,f142])).

fof(f3471,plain,
    ( ~ m1_subset_1(sK1,sK4(o_0_0_xboole_0))
    | ~ spl9_473 ),
    inference(avatar_component_clause,[],[f3470])).

fof(f4107,plain,
    ( ~ spl9_569
    | spl9_221
    | spl9_223
    | spl9_527 ),
    inference(avatar_split_clause,[],[f3894,f3868,f1615,f1601,f4105])).

fof(f4105,plain,
    ( spl9_569
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_569])])).

fof(f3868,plain,
    ( spl9_527
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_527])])).

fof(f3894,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_527 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f3869,f759])).

fof(f3869,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_527 ),
    inference(avatar_component_clause,[],[f3868])).

fof(f4100,plain,
    ( ~ spl9_567
    | ~ spl9_6
    | spl9_519 ),
    inference(avatar_split_clause,[],[f3816,f3797,f170,f4098])).

fof(f4098,plain,
    ( spl9_567
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_567])])).

fof(f3797,plain,
    ( spl9_519
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_519])])).

fof(f3816,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK1))))
    | ~ spl9_6
    | ~ spl9_519 ),
    inference(unit_resulting_resolution,[],[f3798,f232])).

fof(f3798,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK1))))
    | ~ spl9_519 ),
    inference(avatar_component_clause,[],[f3797])).

fof(f4090,plain,
    ( ~ spl9_565
    | spl9_519 ),
    inference(avatar_split_clause,[],[f3808,f3797,f4088])).

fof(f4088,plain,
    ( spl9_565
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_565])])).

fof(f3808,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK1)))))
    | ~ spl9_519 ),
    inference(unit_resulting_resolution,[],[f114,f3798,f110])).

fof(f4083,plain,
    ( ~ spl9_563
    | spl9_221
    | spl9_223
    | spl9_467 ),
    inference(avatar_split_clause,[],[f3450,f3425,f1615,f1601,f4081])).

fof(f4081,plain,
    ( spl9_563
  <=> ~ m2_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_563])])).

fof(f3450,plain,
    ( ~ m2_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_467 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f3426,f123])).

fof(f4051,plain,
    ( ~ spl9_561
    | spl9_221
    | spl9_223
    | spl9_549 ),
    inference(avatar_split_clause,[],[f4014,f3998,f1615,f1601,f4049])).

fof(f4049,plain,
    ( spl9_561
  <=> ~ m1_subset_1(k1_zfmisc_1(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_561])])).

fof(f4014,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_549 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f3999,f759])).

fof(f4044,plain,
    ( ~ spl9_559
    | spl9_549 ),
    inference(avatar_split_clause,[],[f4010,f3998,f4042])).

fof(f4042,plain,
    ( spl9_559
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_559])])).

fof(f4010,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_549 ),
    inference(unit_resulting_resolution,[],[f3999,f117])).

fof(f4037,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_400
    | spl9_555 ),
    inference(avatar_contradiction_clause,[],[f4036])).

fof(f4036,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_400
    | ~ spl9_555 ),
    inference(subsumption_resolution,[],[f4026,f2952])).

fof(f4026,plain,
    ( ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_555 ),
    inference(avatar_component_clause,[],[f4025])).

fof(f4025,plain,
    ( spl9_555
  <=> ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_555])])).

fof(f4035,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_398
    | spl9_557 ),
    inference(avatar_contradiction_clause,[],[f4034])).

fof(f4034,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_76
    | ~ spl9_242
    | ~ spl9_398
    | ~ spl9_557 ),
    inference(subsumption_resolution,[],[f4032,f2944])).

fof(f4032,plain,
    ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_557 ),
    inference(avatar_component_clause,[],[f4031])).

fof(f4031,plain,
    ( spl9_557
  <=> ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_557])])).

fof(f4033,plain,
    ( spl9_552
    | ~ spl9_555
    | ~ spl9_557
    | ~ spl9_112
    | spl9_115
    | spl9_143
    | spl9_233
    | ~ spl9_258 ),
    inference(avatar_split_clause,[],[f2293,f1906,f1672,f975,f819,f810,f4031,f4025,f4019])).

fof(f810,plain,
    ( spl9_112
  <=> m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f1906,plain,
    ( spl9_258
  <=> m2_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f2293,plain,
    ( ! [X0] :
        ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_233
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f2292,f820])).

fof(f2292,plain,
    ( ! [X0] :
        ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),X0)
        | ~ v1_relat_1(X0)
        | v1_xboole_0(k8_eqrel_1(sK0,sK1)) )
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_233
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f2291,f1939])).

fof(f1939,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1938,f976])).

fof(f1938,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1937,f820])).

fof(f1937,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1935,f813])).

fof(f813,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f811,f118])).

fof(f811,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl9_112 ),
    inference(avatar_component_clause,[],[f810])).

fof(f1935,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_258 ),
    inference(resolution,[],[f1907,f124])).

fof(f1907,plain,
    ( m2_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_258 ),
    inference(avatar_component_clause,[],[f1906])).

fof(f2291,plain,
    ( ! [X0] :
        ( ~ r1_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ r2_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
        | ~ m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k8_eqrel_1(sK0,sK1))
        | ~ m2_filter_1(k3_filter_1(sK0,sK1,sK3),k8_eqrel_1(sK0,sK1),X0)
        | ~ v1_relat_1(X0)
        | v1_xboole_0(k8_eqrel_1(sK0,sK1)) )
    | ~ spl9_233 ),
    inference(resolution,[],[f1064,f1673])).

fof(f1064,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ r2_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m2_filter_1(X2,X0,X3)
      | ~ v1_relat_1(X3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1063,f129])).

fof(f1063,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | r3_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m2_filter_1(X2,X0,X3)
      | ~ v1_relat_1(X3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f1062,f127])).

fof(f1062,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_binop_1(X0,X1,X2)
      | ~ r1_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | r3_binop_1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m2_filter_1(X2,X0,X3)
      | ~ v1_relat_1(X3)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f122,f128])).

fof(f4007,plain,
    ( ~ spl9_551
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(avatar_split_clause,[],[f3988,f3933,f170,f4005])).

fof(f4005,plain,
    ( spl9_551
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_551])])).

fof(f3988,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(unit_resulting_resolution,[],[f258,f3934,f1510])).

fof(f4000,plain,
    ( ~ spl9_549
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(avatar_split_clause,[],[f3987,f3933,f170,f3998])).

fof(f3987,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_538 ),
    inference(unit_resulting_resolution,[],[f3934,f355])).

fof(f3965,plain,
    ( ~ spl9_547
    | spl9_527 ),
    inference(avatar_split_clause,[],[f3890,f3868,f3963])).

fof(f3963,plain,
    ( spl9_547
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_547])])).

fof(f3890,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_527 ),
    inference(unit_resulting_resolution,[],[f3869,f117])).

fof(f3956,plain,
    ( ~ spl9_545
    | spl9_507
    | ~ spl9_524 ),
    inference(avatar_split_clause,[],[f3879,f3861,f3712,f3954])).

fof(f3954,plain,
    ( spl9_545
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),sK5(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_545])])).

fof(f3861,plain,
    ( spl9_524
  <=> m1_subset_1(sK5(sK4(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_524])])).

fof(f3879,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),sK5(sK4(sK1)))
    | ~ spl9_507
    | ~ spl9_524 ),
    inference(unit_resulting_resolution,[],[f3713,f3862,f289])).

fof(f3862,plain,
    ( m1_subset_1(sK5(sK4(sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_524 ),
    inference(avatar_component_clause,[],[f3861])).

fof(f3949,plain,
    ( spl9_542
    | spl9_507
    | ~ spl9_524 ),
    inference(avatar_split_clause,[],[f3878,f3861,f3712,f3947])).

fof(f3947,plain,
    ( spl9_542
  <=> r2_hidden(sK5(sK4(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_542])])).

fof(f3878,plain,
    ( r2_hidden(sK5(sK4(sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_507
    | ~ spl9_524 ),
    inference(unit_resulting_resolution,[],[f3713,f3862,f119])).

fof(f3942,plain,
    ( ~ spl9_541
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3729,f3712,f3940])).

fof(f3940,plain,
    ( spl9_541
  <=> ~ r2_hidden(k1_zfmisc_1(sK1),sK5(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_541])])).

fof(f3729,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK1),sK5(k1_zfmisc_1(sK1)))
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f115,f3713,f289])).

fof(f3935,plain,
    ( spl9_538
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3719,f3712,f3933])).

fof(f3719,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f115,f3713,f119])).

fof(f3928,plain,
    ( ~ spl9_537
    | ~ spl9_6
    | spl9_479 ),
    inference(avatar_split_clause,[],[f3556,f3537,f170,f3926])).

fof(f3926,plain,
    ( spl9_537
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_537])])).

fof(f3537,plain,
    ( spl9_479
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_479])])).

fof(f3556,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK1))))
    | ~ spl9_6
    | ~ spl9_479 ),
    inference(unit_resulting_resolution,[],[f3538,f232])).

fof(f3538,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK1))))
    | ~ spl9_479 ),
    inference(avatar_component_clause,[],[f3537])).

fof(f3918,plain,
    ( ~ spl9_535
    | spl9_479 ),
    inference(avatar_split_clause,[],[f3548,f3537,f3916])).

fof(f3548,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl9_479 ),
    inference(unit_resulting_resolution,[],[f114,f3538,f110])).

fof(f3911,plain,
    ( ~ spl9_533
    | spl9_231
    | ~ spl9_396
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3328,f3314,f2870,f1665,f3909])).

fof(f3909,plain,
    ( spl9_533
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_533])])).

fof(f3328,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK1,sK3)
    | ~ spl9_231
    | ~ spl9_396
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f1666,f2871,f3315,f127])).

fof(f3904,plain,
    ( ~ spl9_531
    | ~ spl9_40
    | spl9_231
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3326,f3314,f1665,f327,f3902])).

fof(f3902,plain,
    ( spl9_531
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_531])])).

fof(f3326,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK1,sK1)
    | ~ spl9_40
    | ~ spl9_231
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f1666,f328,f3315,f127])).

fof(f3877,plain,
    ( ~ spl9_529
    | ~ spl9_6
    | ~ spl9_500 ),
    inference(avatar_split_clause,[],[f3848,f3658,f170,f3875])).

fof(f3875,plain,
    ( spl9_529
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_529])])).

fof(f3848,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_500 ),
    inference(unit_resulting_resolution,[],[f258,f3659,f1510])).

fof(f3870,plain,
    ( ~ spl9_527
    | ~ spl9_6
    | ~ spl9_500 ),
    inference(avatar_split_clause,[],[f3847,f3658,f170,f3868])).

fof(f3847,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_500 ),
    inference(unit_resulting_resolution,[],[f3659,f355])).

fof(f3863,plain,
    ( spl9_524
    | ~ spl9_490 ),
    inference(avatar_split_clause,[],[f3698,f3620,f3861])).

fof(f3698,plain,
    ( m1_subset_1(sK5(sK4(sK1)),k1_zfmisc_1(sK1))
    | ~ spl9_490 ),
    inference(unit_resulting_resolution,[],[f258,f3621,f142])).

fof(f3824,plain,
    ( ~ spl9_523
    | spl9_221
    | spl9_223
    | spl9_513 ),
    inference(avatar_split_clause,[],[f3780,f3763,f1615,f1601,f3822])).

fof(f3822,plain,
    ( spl9_523
  <=> ~ m1_subset_1(sK4(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_523])])).

fof(f3780,plain,
    ( ~ m1_subset_1(sK4(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_513 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f3764,f759])).

fof(f3806,plain,
    ( ~ spl9_521
    | ~ spl9_6
    | spl9_509 ),
    inference(avatar_split_clause,[],[f3757,f3737,f170,f3804])).

fof(f3804,plain,
    ( spl9_521
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_521])])).

fof(f3737,plain,
    ( spl9_509
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_509])])).

fof(f3757,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK1)))
    | ~ spl9_6
    | ~ spl9_509 ),
    inference(unit_resulting_resolution,[],[f3738,f232])).

fof(f3738,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK1)))
    | ~ spl9_509 ),
    inference(avatar_component_clause,[],[f3737])).

fof(f3799,plain,
    ( ~ spl9_519
    | spl9_509 ),
    inference(avatar_split_clause,[],[f3749,f3737,f3797])).

fof(f3749,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK1))))
    | ~ spl9_509 ),
    inference(unit_resulting_resolution,[],[f114,f3738,f110])).

fof(f3790,plain,
    ( ~ spl9_517
    | spl9_513 ),
    inference(avatar_split_clause,[],[f3776,f3763,f3788])).

fof(f3788,plain,
    ( spl9_517
  <=> ~ r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_517])])).

fof(f3776,plain,
    ( ~ r2_hidden(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_513 ),
    inference(unit_resulting_resolution,[],[f3764,f117])).

fof(f3772,plain,
    ( ~ spl9_515
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(avatar_split_clause,[],[f3702,f3620,f170,f3770])).

fof(f3770,plain,
    ( spl9_515
  <=> ~ r2_hidden(sK4(sK1),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_515])])).

fof(f3702,plain,
    ( ~ r2_hidden(sK4(sK1),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(unit_resulting_resolution,[],[f258,f3621,f1510])).

fof(f3765,plain,
    ( ~ spl9_513
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(avatar_split_clause,[],[f3701,f3620,f170,f3763])).

fof(f3701,plain,
    ( ~ m1_subset_1(sK4(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_490 ),
    inference(unit_resulting_resolution,[],[f3621,f355])).

fof(f3747,plain,
    ( ~ spl9_511
    | ~ spl9_6
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3728,f3712,f170,f3745])).

fof(f3745,plain,
    ( spl9_511
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_511])])).

fof(f3728,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl9_6
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f3713,f232])).

fof(f3739,plain,
    ( ~ spl9_509
    | spl9_507 ),
    inference(avatar_split_clause,[],[f3718,f3712,f3737])).

fof(f3718,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK1)))
    | ~ spl9_507 ),
    inference(unit_resulting_resolution,[],[f114,f3713,f110])).

fof(f3714,plain,
    ( ~ spl9_507
    | ~ spl9_490 ),
    inference(avatar_split_clause,[],[f3700,f3620,f3712])).

fof(f3700,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1))
    | ~ spl9_490 ),
    inference(unit_resulting_resolution,[],[f258,f3621,f143])).

fof(f3677,plain,
    ( spl9_504
    | ~ spl9_396
    | spl9_451
    | ~ spl9_488 ),
    inference(avatar_split_clause,[],[f3670,f3613,f3314,f2870,f3675])).

fof(f3675,plain,
    ( spl9_504
  <=> v1_funct_1(sK7(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_504])])).

fof(f3613,plain,
    ( spl9_488
  <=> m2_filter_1(sK7(sK1,sK3),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_488])])).

fof(f3670,plain,
    ( v1_funct_1(sK7(sK1,sK3))
    | ~ spl9_396
    | ~ spl9_451
    | ~ spl9_488 ),
    inference(unit_resulting_resolution,[],[f3315,f2871,f3614,f127])).

fof(f3614,plain,
    ( m2_filter_1(sK7(sK1,sK3),sK1,sK3)
    | ~ spl9_488 ),
    inference(avatar_component_clause,[],[f3613])).

fof(f3667,plain,
    ( ~ spl9_503
    | spl9_449
    | ~ spl9_484 ),
    inference(avatar_split_clause,[],[f3603,f3589,f3308,f3665])).

fof(f3665,plain,
    ( spl9_503
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_503])])).

fof(f3603,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK5(sK1))
    | ~ spl9_449
    | ~ spl9_484 ),
    inference(unit_resulting_resolution,[],[f3309,f3590,f289])).

fof(f3660,plain,
    ( spl9_500
    | spl9_449
    | ~ spl9_484 ),
    inference(avatar_split_clause,[],[f3602,f3589,f3308,f3658])).

fof(f3602,plain,
    ( r2_hidden(sK5(sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_449
    | ~ spl9_484 ),
    inference(unit_resulting_resolution,[],[f3309,f3590,f119])).

fof(f3653,plain,
    ( ~ spl9_499
    | ~ spl9_6
    | spl9_475 ),
    inference(avatar_split_clause,[],[f3522,f3503,f170,f3651])).

fof(f3651,plain,
    ( spl9_499
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_499])])).

fof(f3503,plain,
    ( spl9_475
  <=> ~ v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_475])])).

fof(f3522,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_6
    | ~ spl9_475 ),
    inference(unit_resulting_resolution,[],[f3504,f232])).

fof(f3504,plain,
    ( ~ v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_475 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f3643,plain,
    ( ~ spl9_497
    | spl9_475 ),
    inference(avatar_split_clause,[],[f3514,f3503,f3641])).

fof(f3514,plain,
    ( ~ v1_xboole_0(sK4(sK4(k2_zfmisc_1(sK0,sK0))))
    | ~ spl9_475 ),
    inference(unit_resulting_resolution,[],[f114,f3504,f110])).

fof(f3636,plain,
    ( ~ spl9_495
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(avatar_split_clause,[],[f3398,f3379,f170,f3634])).

fof(f3634,plain,
    ( spl9_495
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_495])])).

fof(f3398,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(unit_resulting_resolution,[],[f115,f3380,f1510])).

fof(f3629,plain,
    ( ~ spl9_493
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3358,f3338,f3627])).

fof(f3627,plain,
    ( spl9_493
  <=> ~ r2_hidden(sK4(sK1),sK5(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_493])])).

fof(f3358,plain,
    ( ~ r2_hidden(sK4(sK1),sK5(sK4(sK1)))
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f115,f3339,f289])).

fof(f3622,plain,
    ( spl9_490
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3350,f3338,f3620])).

fof(f3350,plain,
    ( r2_hidden(sK5(sK4(sK1)),sK4(sK1))
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f115,f3339,f119])).

fof(f3615,plain,
    ( spl9_488
    | ~ spl9_396
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3331,f3314,f2870,f3613])).

fof(f3331,plain,
    ( m2_filter_1(sK7(sK1,sK3),sK1,sK3)
    | ~ spl9_396
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f2871,f3315,f130])).

fof(f3601,plain,
    ( spl9_486
    | ~ spl9_40
    | spl9_451
    | ~ spl9_482 ),
    inference(avatar_split_clause,[],[f3594,f3562,f3314,f327,f3599])).

fof(f3599,plain,
    ( spl9_486
  <=> v1_funct_1(sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_486])])).

fof(f3562,plain,
    ( spl9_482
  <=> m2_filter_1(sK7(sK1,sK1),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_482])])).

fof(f3594,plain,
    ( v1_funct_1(sK7(sK1,sK1))
    | ~ spl9_40
    | ~ spl9_451
    | ~ spl9_482 ),
    inference(unit_resulting_resolution,[],[f3315,f328,f3563,f127])).

fof(f3563,plain,
    ( m2_filter_1(sK7(sK1,sK1),sK1,sK1)
    | ~ spl9_482 ),
    inference(avatar_component_clause,[],[f3562])).

fof(f3591,plain,
    ( spl9_484
    | ~ spl9_20
    | spl9_449
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3374,f3314,f3308,f225,f3589])).

fof(f3374,plain,
    ( m1_subset_1(sK5(sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl9_20
    | ~ spl9_449
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f3315,f115,f226,f3309,f759])).

fof(f3564,plain,
    ( spl9_482
    | ~ spl9_40
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3329,f3314,f327,f3562])).

fof(f3329,plain,
    ( m2_filter_1(sK7(sK1,sK1),sK1,sK1)
    | ~ spl9_40
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f328,f3315,f130])).

fof(f3546,plain,
    ( ~ spl9_481
    | ~ spl9_6
    | spl9_463 ),
    inference(avatar_split_clause,[],[f3444,f3408,f170,f3544])).

fof(f3544,plain,
    ( spl9_481
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_481])])).

fof(f3408,plain,
    ( spl9_463
  <=> ~ v1_xboole_0(sK4(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_463])])).

fof(f3444,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK1)))
    | ~ spl9_6
    | ~ spl9_463 ),
    inference(unit_resulting_resolution,[],[f3409,f232])).

fof(f3409,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK1)))
    | ~ spl9_463 ),
    inference(avatar_component_clause,[],[f3408])).

fof(f3539,plain,
    ( ~ spl9_479
    | spl9_463 ),
    inference(avatar_split_clause,[],[f3436,f3408,f3537])).

fof(f3436,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK1))))
    | ~ spl9_463 ),
    inference(unit_resulting_resolution,[],[f114,f3409,f110])).

fof(f3512,plain,
    ( ~ spl9_477
    | ~ spl9_6
    | spl9_449 ),
    inference(avatar_split_clause,[],[f3370,f3308,f170,f3510])).

fof(f3510,plain,
    ( spl9_477
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_477])])).

fof(f3370,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK0))
    | ~ spl9_6
    | ~ spl9_449 ),
    inference(unit_resulting_resolution,[],[f3309,f232])).

fof(f3505,plain,
    ( ~ spl9_475
    | spl9_449 ),
    inference(avatar_split_clause,[],[f3360,f3308,f3503])).

fof(f3360,plain,
    ( ~ v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl9_449 ),
    inference(unit_resulting_resolution,[],[f114,f3309,f110])).

fof(f3472,plain,
    ( ~ spl9_473
    | spl9_221
    | spl9_223
    | spl9_467 ),
    inference(avatar_split_clause,[],[f3449,f3425,f1615,f1601,f3470])).

fof(f3449,plain,
    ( ~ m1_subset_1(sK1,sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_467 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f3426,f759])).

fof(f3463,plain,
    ( ~ spl9_471
    | spl9_467 ),
    inference(avatar_split_clause,[],[f3453,f3425,f3461])).

fof(f3461,plain,
    ( spl9_471
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_471])])).

fof(f3453,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_467 ),
    inference(unit_resulting_resolution,[],[f3426,f117])).

fof(f3434,plain,
    ( ~ spl9_469
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(avatar_split_clause,[],[f3397,f3379,f170,f3432])).

fof(f3432,plain,
    ( spl9_469
  <=> ~ r2_hidden(sK1,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_469])])).

fof(f3397,plain,
    ( ~ r2_hidden(sK1,sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(unit_resulting_resolution,[],[f258,f3380,f1510])).

fof(f3427,plain,
    ( ~ spl9_467
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(avatar_split_clause,[],[f3396,f3379,f170,f3425])).

fof(f3396,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_458 ),
    inference(unit_resulting_resolution,[],[f3380,f355])).

fof(f3420,plain,
    ( ~ spl9_465
    | ~ spl9_6
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3357,f3338,f170,f3418])).

fof(f3418,plain,
    ( spl9_465
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_465])])).

fof(f3357,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK1))
    | ~ spl9_6
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f3339,f232])).

fof(f3410,plain,
    ( ~ spl9_463
    | spl9_455 ),
    inference(avatar_split_clause,[],[f3349,f3338,f3408])).

fof(f3349,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK1)))
    | ~ spl9_455 ),
    inference(unit_resulting_resolution,[],[f114,f3339,f110])).

fof(f3388,plain,
    ( ~ spl9_461
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3333,f3314,f3386])).

fof(f3386,plain,
    ( spl9_461
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_461])])).

fof(f3333,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f115,f3315,f289])).

fof(f3381,plain,
    ( spl9_458
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3325,f3314,f3379])).

fof(f3325,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f115,f3315,f119])).

fof(f3347,plain,
    ( ~ spl9_457
    | ~ spl9_6
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3332,f3314,f170,f3345])).

fof(f3345,plain,
    ( spl9_457
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_457])])).

fof(f3332,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK1)
    | ~ spl9_6
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f3315,f232])).

fof(f3340,plain,
    ( ~ spl9_455
    | spl9_451 ),
    inference(avatar_split_clause,[],[f3324,f3314,f3338])).

fof(f3324,plain,
    ( ~ v1_xboole_0(sK4(sK1))
    | ~ spl9_451 ),
    inference(unit_resulting_resolution,[],[f114,f3315,f110])).

fof(f3322,plain,
    ( spl9_448
    | spl9_450
    | spl9_452
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f2188,f225,f3320,f3317,f3311])).

fof(f3311,plain,
    ( spl9_448
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_448])])).

fof(f3320,plain,
    ( spl9_452
  <=> ! [X20] :
        ( ~ m1_subset_1(X20,sK1)
        | m1_subset_1(X20,k2_zfmisc_1(sK0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_452])])).

fof(f2188,plain,
    ( ! [X20] :
        ( ~ m1_subset_1(X20,sK1)
        | v1_xboole_0(sK1)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | m1_subset_1(X20,k2_zfmisc_1(sK0,sK0)) )
    | ~ spl9_20 ),
    inference(resolution,[],[f759,f226])).

fof(f3306,plain,
    ( ~ spl9_447
    | spl9_269 ),
    inference(avatar_split_clause,[],[f2015,f1962,f3304])).

fof(f3304,plain,
    ( spl9_447
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_447])])).

fof(f2015,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_269 ),
    inference(unit_resulting_resolution,[],[f114,f1963,f110])).

fof(f3298,plain,
    ( ~ spl9_445
    | spl9_9
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2928,f2870,f1665,f177,f3296])).

fof(f3296,plain,
    ( spl9_445
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK8,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_445])])).

fof(f2928,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK8,sK3)
    | ~ spl9_9
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f178,f1666,f2871,f127])).

fof(f3288,plain,
    ( ~ spl9_443
    | spl9_1
    | spl9_231
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2905,f2870,f1665,f149,f3286])).

fof(f3286,plain,
    ( spl9_443
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_443])])).

fof(f2905,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK0,sK3)
    | ~ spl9_1
    | ~ spl9_231
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f150,f1666,f2871,f127])).

fof(f3274,plain,
    ( ~ spl9_441
    | spl9_413
    | spl9_435 ),
    inference(avatar_split_clause,[],[f3242,f3207,f3020,f3272])).

fof(f3272,plain,
    ( spl9_441
  <=> ~ m1_subset_1(sK0,sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_441])])).

fof(f3020,plain,
    ( spl9_413
  <=> ~ v1_xboole_0(sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_413])])).

fof(f3207,plain,
    ( spl9_435
  <=> ~ r2_hidden(sK0,sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_435])])).

fof(f3242,plain,
    ( ~ m1_subset_1(sK0,sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_413
    | ~ spl9_435 ),
    inference(unit_resulting_resolution,[],[f3021,f3208,f119])).

fof(f3208,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_435 ),
    inference(avatar_component_clause,[],[f3207])).

fof(f3021,plain,
    ( ~ v1_xboole_0(sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_413 ),
    inference(avatar_component_clause,[],[f3020])).

fof(f3267,plain,
    ( ~ spl9_439
    | ~ spl9_210
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3001,f2981,f1519,f3265])).

fof(f3001,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_210
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f1520,f2982,f289])).

fof(f3216,plain,
    ( ~ spl9_437
    | spl9_421 ),
    inference(avatar_split_clause,[],[f3118,f3090,f3214])).

fof(f3214,plain,
    ( spl9_437
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_437])])).

fof(f3090,plain,
    ( spl9_421
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_421])])).

fof(f3118,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_421 ),
    inference(unit_resulting_resolution,[],[f3091,f117])).

fof(f3091,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_421 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f3209,plain,
    ( ~ spl9_435
    | spl9_421 ),
    inference(avatar_split_clause,[],[f3116,f3090,f3207])).

fof(f3116,plain,
    ( ~ r2_hidden(sK0,sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_421 ),
    inference(unit_resulting_resolution,[],[f258,f3091,f142])).

fof(f3202,plain,
    ( ~ spl9_433
    | spl9_1
    | ~ spl9_416 ),
    inference(avatar_split_clause,[],[f3096,f3076,f149,f3200])).

fof(f3200,plain,
    ( spl9_433
  <=> ~ r2_hidden(sK0,sK5(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_433])])).

fof(f3076,plain,
    ( spl9_416
  <=> m1_subset_1(sK5(sK5(k1_zfmisc_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_416])])).

fof(f3096,plain,
    ( ~ r2_hidden(sK0,sK5(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_1
    | ~ spl9_416 ),
    inference(unit_resulting_resolution,[],[f150,f3077,f289])).

fof(f3077,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_416 ),
    inference(avatar_component_clause,[],[f3076])).

fof(f3195,plain,
    ( spl9_430
    | spl9_1
    | ~ spl9_416 ),
    inference(avatar_split_clause,[],[f3093,f3076,f149,f3193])).

fof(f3193,plain,
    ( spl9_430
  <=> r2_hidden(sK5(sK5(k1_zfmisc_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_430])])).

fof(f3093,plain,
    ( r2_hidden(sK5(sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_416 ),
    inference(unit_resulting_resolution,[],[f150,f3077,f119])).

fof(f3186,plain,
    ( ~ spl9_429
    | ~ spl9_6
    | spl9_413 ),
    inference(avatar_split_clause,[],[f3039,f3020,f170,f3184])).

fof(f3184,plain,
    ( spl9_429
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_429])])).

fof(f3039,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_6
    | ~ spl9_413 ),
    inference(unit_resulting_resolution,[],[f3021,f232])).

fof(f3179,plain,
    ( ~ spl9_427
    | spl9_413 ),
    inference(avatar_split_clause,[],[f3031,f3020,f3177])).

fof(f3031,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK5(k1_zfmisc_1(sK0)))))
    | ~ spl9_413 ),
    inference(unit_resulting_resolution,[],[f114,f3021,f110])).

fof(f3172,plain,
    ( spl9_424
    | spl9_9
    | ~ spl9_396
    | ~ spl9_406 ),
    inference(avatar_split_clause,[],[f3165,f2971,f2870,f177,f3170])).

fof(f3170,plain,
    ( spl9_424
  <=> v1_funct_1(sK7(sK8,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_424])])).

fof(f2971,plain,
    ( spl9_406
  <=> m2_filter_1(sK7(sK8,sK3),sK8,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_406])])).

fof(f3165,plain,
    ( v1_funct_1(sK7(sK8,sK3))
    | ~ spl9_9
    | ~ spl9_396
    | ~ spl9_406 ),
    inference(unit_resulting_resolution,[],[f178,f2871,f2972,f127])).

fof(f2972,plain,
    ( m2_filter_1(sK7(sK8,sK3),sK8,sK3)
    | ~ spl9_406 ),
    inference(avatar_component_clause,[],[f2971])).

fof(f3129,plain,
    ( spl9_422
    | spl9_1
    | ~ spl9_396
    | ~ spl9_404 ),
    inference(avatar_split_clause,[],[f3122,f2964,f2870,f149,f3127])).

fof(f3127,plain,
    ( spl9_422
  <=> v1_funct_1(sK7(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_422])])).

fof(f2964,plain,
    ( spl9_404
  <=> m2_filter_1(sK7(sK0,sK3),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_404])])).

fof(f3122,plain,
    ( v1_funct_1(sK7(sK0,sK3))
    | ~ spl9_1
    | ~ spl9_396
    | ~ spl9_404 ),
    inference(unit_resulting_resolution,[],[f150,f2871,f2965,f127])).

fof(f2965,plain,
    ( m2_filter_1(sK7(sK0,sK3),sK0,sK3)
    | ~ spl9_404 ),
    inference(avatar_component_clause,[],[f2964])).

fof(f3092,plain,
    ( ~ spl9_421
    | ~ spl9_78
    | spl9_409 ),
    inference(avatar_split_clause,[],[f3011,f2978,f627,f3090])).

fof(f3011,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_78
    | ~ spl9_409 ),
    inference(unit_resulting_resolution,[],[f628,f2979,f142])).

fof(f3085,plain,
    ( ~ spl9_419
    | spl9_1
    | spl9_409
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3009,f2981,f2978,f149,f3083])).

fof(f3083,plain,
    ( spl9_419
  <=> ~ m2_subset_1(o_0_0_xboole_0,sK0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_419])])).

fof(f3009,plain,
    ( ~ m2_subset_1(o_0_0_xboole_0,sK0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_1
    | ~ spl9_409
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f2982,f115,f2979,f124])).

fof(f3078,plain,
    ( spl9_416
    | spl9_1
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3005,f2981,f149,f3076])).

fof(f3005,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(sK0))),sK0)
    | ~ spl9_1
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f150,f115,f115,f2982,f759])).

fof(f3029,plain,
    ( ~ spl9_415
    | ~ spl9_6
    | spl9_411 ),
    inference(avatar_split_clause,[],[f3000,f2981,f170,f3027])).

fof(f3027,plain,
    ( spl9_415
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_415])])).

fof(f3000,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_6
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f2982,f232])).

fof(f3022,plain,
    ( ~ spl9_413
    | spl9_411 ),
    inference(avatar_split_clause,[],[f2988,f2981,f3020])).

fof(f2988,plain,
    ( ~ v1_xboole_0(sK4(sK5(k1_zfmisc_1(sK0))))
    | ~ spl9_411 ),
    inference(unit_resulting_resolution,[],[f114,f2982,f110])).

fof(f2986,plain,
    ( ~ spl9_409
    | spl9_410
    | spl9_91 ),
    inference(avatar_split_clause,[],[f709,f704,f2984,f2978])).

fof(f2984,plain,
    ( spl9_410
  <=> v1_xboole_0(sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_410])])).

fof(f704,plain,
    ( spl9_91
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f709,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_91 ),
    inference(resolution,[],[f705,f119])).

fof(f705,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_91 ),
    inference(avatar_component_clause,[],[f704])).

fof(f2973,plain,
    ( spl9_406
    | spl9_9
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2900,f2870,f177,f2971])).

fof(f2900,plain,
    ( m2_filter_1(sK7(sK8,sK3),sK8,sK3)
    | ~ spl9_9
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f178,f2871,f130])).

fof(f2966,plain,
    ( spl9_404
    | spl9_1
    | ~ spl9_396 ),
    inference(avatar_split_clause,[],[f2877,f2870,f149,f2964])).

fof(f2877,plain,
    ( m2_filter_1(sK7(sK0,sK3),sK0,sK3)
    | ~ spl9_1
    | ~ spl9_396 ),
    inference(unit_resulting_resolution,[],[f150,f2871,f130])).

fof(f2959,plain,
    ( spl9_402
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2861,f2651,f958,f379,f225,f184,f163,f156,f149,f2957])).

fof(f2957,plain,
    ( spl9_402
  <=> v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_402])])).

fof(f2861,plain,
    ( v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_48
    | ~ spl9_140
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f150,f380,f157,f164,f185,f226,f959,f2652,f139])).

fof(f2942,plain,
    ( spl9_400
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_216
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2860,f2651,f1587,f958,f606,f379,f2940])).

fof(f1587,plain,
    ( spl9_216
  <=> r3_binop_1(sK0,o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f2860,plain,
    ( r2_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_216
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f380,f607,f1588,f959,f2652,f121])).

fof(f1588,plain,
    ( r3_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_216 ),
    inference(avatar_component_clause,[],[f1587])).

fof(f2935,plain,
    ( spl9_398
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_216
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2859,f2651,f1587,f958,f606,f379,f2933])).

fof(f2859,plain,
    ( r1_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_48
    | ~ spl9_76
    | ~ spl9_140
    | ~ spl9_216
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f380,f607,f1588,f959,f2652,f120])).

fof(f2872,plain,
    ( spl9_396
    | ~ spl9_380 ),
    inference(avatar_split_clause,[],[f2864,f2651,f2870])).

fof(f2864,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_380 ),
    inference(unit_resulting_resolution,[],[f2652,f136])).

fof(f2856,plain,
    ( ~ spl9_395
    | spl9_373 ),
    inference(avatar_split_clause,[],[f2656,f2617,f2854])).

fof(f2854,plain,
    ( spl9_395
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_395])])).

fof(f2617,plain,
    ( spl9_373
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_373])])).

fof(f2656,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_373 ),
    inference(unit_resulting_resolution,[],[f2618,f117])).

fof(f2618,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_373 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2849,plain,
    ( ~ spl9_393
    | spl9_373 ),
    inference(avatar_split_clause,[],[f2654,f2617,f2847])).

fof(f2654,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_373 ),
    inference(unit_resulting_resolution,[],[f258,f2618,f142])).

fof(f2842,plain,
    ( spl9_390
    | spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(avatar_split_clause,[],[f2835,f2624,f327,f255,f2840])).

fof(f2840,plain,
    ( spl9_390
  <=> v1_funct_1(sK7(sK4(sK8),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_390])])).

fof(f2835,plain,
    ( v1_funct_1(sK7(sK4(sK8),sK1))
    | ~ spl9_27
    | ~ spl9_40
    | ~ spl9_374 ),
    inference(unit_resulting_resolution,[],[f328,f256,f2625,f127])).

fof(f2828,plain,
    ( spl9_370
    | ~ spl9_6
    | spl9_221
    | spl9_223
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f2733,f2672,f1615,f1601,f170,f2607])).

fof(f2607,plain,
    ( spl9_370
  <=> m2_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_370])])).

fof(f2672,plain,
    ( spl9_382
  <=> v1_xboole_0(sK5(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_382])])).

fof(f2733,plain,
    ( m2_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_382 ),
    inference(backward_demodulation,[],[f2727,f1634])).

fof(f1634,plain,
    ( m2_subset_1(sK5(sK4(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f115,f1602,f258,f1616,f125])).

fof(f2727,plain,
    ( o_0_0_xboole_0 = sK5(sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_382 ),
    inference(unit_resulting_resolution,[],[f2673,f210])).

fof(f2673,plain,
    ( v1_xboole_0(sK5(sK4(o_0_0_xboole_0)))
    | ~ spl9_382 ),
    inference(avatar_component_clause,[],[f2672])).

fof(f2826,plain,
    ( spl9_388
    | spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(avatar_split_clause,[],[f2819,f2589,f327,f239,f2824])).

fof(f2824,plain,
    ( spl9_388
  <=> v1_funct_1(sK7(sK4(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_388])])).

fof(f2819,plain,
    ( v1_funct_1(sK7(sK4(sK0),sK1))
    | ~ spl9_23
    | ~ spl9_40
    | ~ spl9_364 ),
    inference(unit_resulting_resolution,[],[f328,f240,f2590,f127])).

fof(f2816,plain,
    ( spl9_386
    | ~ spl9_6
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f2727,f2672,f170,f2814])).

fof(f2793,plain,
    ( spl9_238
    | ~ spl9_6
    | ~ spl9_326
    | ~ spl9_382 ),
    inference(avatar_split_clause,[],[f2734,f2672,f2380,f170,f1744])).

fof(f2380,plain,
    ( spl9_326
  <=> r2_hidden(sK5(sK4(o_0_0_xboole_0)),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_326])])).

fof(f2734,plain,
    ( r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_326
    | ~ spl9_382 ),
    inference(backward_demodulation,[],[f2727,f2381])).

fof(f2381,plain,
    ( r2_hidden(sK5(sK4(o_0_0_xboole_0)),sK4(o_0_0_xboole_0))
    | ~ spl9_326 ),
    inference(avatar_component_clause,[],[f2380])).

fof(f2745,plain,
    ( ~ spl9_6
    | spl9_239
    | ~ spl9_326
    | ~ spl9_382 ),
    inference(avatar_contradiction_clause,[],[f2744])).

fof(f2744,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_239
    | ~ spl9_326
    | ~ spl9_382 ),
    inference(subsumption_resolution,[],[f2734,f1748])).

fof(f1748,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_239 ),
    inference(avatar_component_clause,[],[f1747])).

fof(f1747,plain,
    ( spl9_239
  <=> ~ r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_239])])).

fof(f2743,plain,
    ( ~ spl9_6
    | spl9_221
    | spl9_223
    | spl9_371
    | ~ spl9_382 ),
    inference(avatar_contradiction_clause,[],[f2742])).

fof(f2742,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_371
    | ~ spl9_382 ),
    inference(subsumption_resolution,[],[f2733,f2611])).

fof(f2611,plain,
    ( ~ m2_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_371 ),
    inference(avatar_component_clause,[],[f2610])).

fof(f2610,plain,
    ( spl9_371
  <=> ~ m2_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_371])])).

fof(f2681,plain,
    ( spl9_384
    | ~ spl9_112
    | spl9_115
    | spl9_143
    | ~ spl9_282 ),
    inference(avatar_split_clause,[],[f2070,f2011,f975,f819,f810,f2679])).

fof(f2011,plain,
    ( spl9_282
  <=> m2_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_282])])).

fof(f2070,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2069,f976])).

fof(f2069,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2068,f820])).

fof(f2068,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2066,f813])).

fof(f2066,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k8_eqrel_1(sK0,sK1))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_282 ),
    inference(resolution,[],[f2012,f124])).

fof(f2012,plain,
    ( m2_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_282 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2674,plain,
    ( spl9_382
    | ~ spl9_6
    | ~ spl9_378 ),
    inference(avatar_split_clause,[],[f2666,f2638,f170,f2672])).

fof(f2638,plain,
    ( spl9_378
  <=> m1_subset_1(sK5(sK4(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_378])])).

fof(f2666,plain,
    ( v1_xboole_0(sK5(sK4(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_378 ),
    inference(unit_resulting_resolution,[],[f115,f2661,f119])).

fof(f2661,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(sK4(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_378 ),
    inference(unit_resulting_resolution,[],[f171,f2639,f143])).

fof(f2639,plain,
    ( m1_subset_1(sK5(sK4(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_378 ),
    inference(avatar_component_clause,[],[f2638])).

fof(f2653,plain,
    ( spl9_380
    | spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f778,f327,f198,f149,f2651])).

fof(f778,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f150,f328,f199,f129])).

fof(f2640,plain,
    ( spl9_378
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f2180,f1615,f1601,f2638])).

fof(f2180,plain,
    ( m1_subset_1(sK5(sK4(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f115,f258,f759])).

fof(f2633,plain,
    ( ~ spl9_377
    | spl9_245 ),
    inference(avatar_split_clause,[],[f1785,f1779,f2631])).

fof(f2631,plain,
    ( spl9_377
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_377])])).

fof(f1779,plain,
    ( spl9_245
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).

fof(f1785,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_245 ),
    inference(unit_resulting_resolution,[],[f115,f1780,f142])).

fof(f1780,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_245 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f2626,plain,
    ( spl9_374
    | spl9_27
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f400,f327,f255,f2624])).

fof(f400,plain,
    ( m2_filter_1(sK7(sK4(sK8),sK1),sK4(sK8),sK1)
    | ~ spl9_27
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f256,f328,f130])).

fof(f2619,plain,
    ( ~ spl9_373
    | ~ spl9_240
    | spl9_245 ),
    inference(avatar_split_clause,[],[f1783,f1779,f1754,f2617])).

fof(f1783,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_240
    | ~ spl9_245 ),
    inference(unit_resulting_resolution,[],[f1755,f1780,f142])).

fof(f2612,plain,
    ( ~ spl9_371
    | spl9_221
    | spl9_223
    | spl9_245 ),
    inference(avatar_split_clause,[],[f1782,f1779,f1615,f1601,f2610])).

fof(f1782,plain,
    ( ~ m2_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_245 ),
    inference(unit_resulting_resolution,[],[f1616,f1602,f258,f1780,f124])).

fof(f2605,plain,
    ( ~ spl9_369
    | spl9_57
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1633,f1615,f1601,f413,f2603])).

fof(f2603,plain,
    ( spl9_369
  <=> ~ m2_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_369])])).

fof(f413,plain,
    ( spl9_57
  <=> ~ m1_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f1633,plain,
    ( ~ m2_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_57
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f414,f1602,f258,f1616,f123])).

fof(f414,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f413])).

fof(f2598,plain,
    ( ~ spl9_367
    | spl9_47
    | spl9_221
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1630,f1615,f1601,f370,f2596])).

fof(f2596,plain,
    ( spl9_367
  <=> ~ m2_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_367])])).

fof(f370,plain,
    ( spl9_47
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f1630,plain,
    ( ~ m2_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_47
    | ~ spl9_221
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f371,f1602,f258,f1616,f123])).

fof(f371,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f370])).

fof(f2591,plain,
    ( spl9_364
    | spl9_23
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f399,f327,f239,f2589])).

fof(f399,plain,
    ( m2_filter_1(sK7(sK4(sK0),sK1),sK4(sK0),sK1)
    | ~ spl9_23
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f240,f328,f130])).

fof(f2575,plain,
    ( ~ spl9_363
    | ~ spl9_6
    | spl9_107
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1564,f1407,f783,f170,f2573])).

fof(f2573,plain,
    ( spl9_363
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_363])])).

fof(f783,plain,
    ( spl9_107
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f1564,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(o_0_0_xboole_0))))
    | ~ spl9_6
    | ~ spl9_107
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f804])).

fof(f804,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK2))))
    | ~ spl9_6
    | ~ spl9_107 ),
    inference(unit_resulting_resolution,[],[f784,f232])).

fof(f784,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK2))))
    | ~ spl9_107 ),
    inference(avatar_component_clause,[],[f783])).

fof(f2568,plain,
    ( ~ spl9_361
    | spl9_107
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1561,f1407,f783,f2566])).

fof(f1561,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(o_0_0_xboole_0)))))
    | ~ spl9_107
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f801])).

fof(f801,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK2)))))
    | ~ spl9_107 ),
    inference(unit_resulting_resolution,[],[f114,f784,f110])).

fof(f2548,plain,
    ( ~ spl9_359
    | ~ spl9_6
    | spl9_177 ),
    inference(avatar_split_clause,[],[f1186,f1171,f170,f2546])).

fof(f2546,plain,
    ( spl9_359
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_359])])).

fof(f1171,plain,
    ( spl9_177
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_177])])).

fof(f1186,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK8))))
    | ~ spl9_6
    | ~ spl9_177 ),
    inference(unit_resulting_resolution,[],[f1172,f232])).

fof(f1172,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK8))))
    | ~ spl9_177 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f2541,plain,
    ( ~ spl9_357
    | spl9_177 ),
    inference(avatar_split_clause,[],[f1182,f1171,f2539])).

fof(f1182,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK8)))))
    | ~ spl9_177 ),
    inference(unit_resulting_resolution,[],[f114,f1172,f110])).

fof(f2519,plain,
    ( ~ spl9_355
    | spl9_237 ),
    inference(avatar_split_clause,[],[f1740,f1686,f2517])).

fof(f2517,plain,
    ( spl9_355
  <=> ~ r2_hidden(sK8,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_355])])).

fof(f1740,plain,
    ( ~ r2_hidden(sK8,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_237 ),
    inference(unit_resulting_resolution,[],[f115,f1687,f142])).

fof(f1687,plain,
    ( ~ m1_subset_1(sK8,sK4(o_0_0_xboole_0))
    | ~ spl9_237 ),
    inference(avatar_component_clause,[],[f1686])).

fof(f2512,plain,
    ( ~ spl9_353
    | spl9_235 ),
    inference(avatar_split_clause,[],[f1736,f1679,f2510])).

fof(f2510,plain,
    ( spl9_353
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_353])])).

fof(f1736,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK4(o_0_0_xboole_0))))
    | ~ spl9_235 ),
    inference(unit_resulting_resolution,[],[f115,f1680,f142])).

fof(f1680,plain,
    ( ~ m1_subset_1(sK0,sK4(o_0_0_xboole_0))
    | ~ spl9_235 ),
    inference(avatar_component_clause,[],[f1679])).

fof(f2493,plain,
    ( ~ spl9_351
    | spl9_9
    | ~ spl9_40
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1714,f1665,f327,f177,f2491])).

fof(f2491,plain,
    ( spl9_351
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK8,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_351])])).

fof(f1714,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK8,sK1)
    | ~ spl9_9
    | ~ spl9_40
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f178,f328,f1666,f127])).

fof(f2486,plain,
    ( ~ spl9_349
    | spl9_1
    | ~ spl9_40
    | spl9_231 ),
    inference(avatar_split_clause,[],[f1700,f1665,f327,f149,f2484])).

fof(f2484,plain,
    ( spl9_349
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_349])])).

fof(f1700,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),sK0,sK1)
    | ~ spl9_1
    | ~ spl9_40
    | ~ spl9_231 ),
    inference(unit_resulting_resolution,[],[f150,f328,f1666,f127])).

fof(f2479,plain,
    ( ~ spl9_347
    | ~ spl9_6
    | spl9_155 ),
    inference(avatar_split_clause,[],[f1058,f1043,f170,f2477])).

fof(f2477,plain,
    ( spl9_347
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_347])])).

fof(f1043,plain,
    ( spl9_155
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_155])])).

fof(f1058,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl9_6
    | ~ spl9_155 ),
    inference(unit_resulting_resolution,[],[f1044,f232])).

fof(f1044,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl9_155 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f2472,plain,
    ( ~ spl9_345
    | spl9_155 ),
    inference(avatar_split_clause,[],[f1054,f1043,f2470])).

fof(f1054,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl9_155 ),
    inference(unit_resulting_resolution,[],[f114,f1044,f110])).

fof(f2464,plain,
    ( spl9_342
    | ~ spl9_112
    | spl9_115
    | spl9_143
    | ~ spl9_282 ),
    inference(avatar_split_clause,[],[f2073,f2011,f975,f819,f810,f2462])).

fof(f2073,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2072,f976])).

fof(f2072,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2071,f820])).

fof(f2071,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_282 ),
    inference(subsumption_resolution,[],[f2067,f813])).

fof(f2067,plain,
    ( m1_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_282 ),
    inference(resolution,[],[f2012,f123])).

fof(f2453,plain,
    ( ~ spl9_341
    | spl9_221
    | spl9_223
    | spl9_333 ),
    inference(avatar_split_clause,[],[f2416,f2413,f1615,f1601,f2451])).

fof(f2451,plain,
    ( spl9_341
  <=> ~ m1_subset_1(sK4(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_341])])).

fof(f2416,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_333 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f2414,f759])).

fof(f2442,plain,
    ( ~ spl9_339
    | spl9_333 ),
    inference(avatar_split_clause,[],[f2420,f2413,f2440])).

fof(f2440,plain,
    ( spl9_339
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_339])])).

fof(f2420,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_333 ),
    inference(unit_resulting_resolution,[],[f2414,f117])).

fof(f2435,plain,
    ( spl9_336
    | ~ spl9_112
    | spl9_115
    | spl9_143
    | ~ spl9_258 ),
    inference(avatar_split_clause,[],[f1939,f1906,f975,f819,f810,f2433])).

fof(f2428,plain,
    ( ~ spl9_335
    | spl9_333 ),
    inference(avatar_split_clause,[],[f2418,f2413,f2426])).

fof(f2426,plain,
    ( spl9_335
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_335])])).

fof(f2418,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_333 ),
    inference(unit_resulting_resolution,[],[f258,f2414,f142])).

fof(f2415,plain,
    ( ~ spl9_333
    | ~ spl9_6
    | ~ spl9_326 ),
    inference(avatar_split_clause,[],[f2404,f2380,f170,f2413])).

fof(f2404,plain,
    ( ~ m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_326 ),
    inference(unit_resulting_resolution,[],[f2381,f355])).

fof(f2396,plain,
    ( ~ spl9_331
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1850,f1601,f2394])).

fof(f2394,plain,
    ( spl9_331
  <=> ~ r2_hidden(sK4(o_0_0_xboole_0),sK5(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).

fof(f1850,plain,
    ( ~ r2_hidden(sK4(o_0_0_xboole_0),sK5(sK4(o_0_0_xboole_0)))
    | ~ spl9_221 ),
    inference(unit_resulting_resolution,[],[f1602,f115,f289])).

fof(f2389,plain,
    ( spl9_328
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f813,f810,f2387])).

fof(f2382,plain,
    ( spl9_326
    | spl9_73
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1547,f1407,f533,f2380])).

fof(f533,plain,
    ( spl9_73
  <=> ~ v1_xboole_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f1547,plain,
    ( r2_hidden(sK5(sK4(o_0_0_xboole_0)),sK4(o_0_0_xboole_0))
    | ~ spl9_73
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f538])).

fof(f538,plain,
    ( r2_hidden(sK5(sK4(sK2)),sK4(sK2))
    | ~ spl9_73 ),
    inference(unit_resulting_resolution,[],[f115,f534,f119])).

fof(f534,plain,
    ( ~ v1_xboole_0(sK4(sK2))
    | ~ spl9_73 ),
    inference(avatar_component_clause,[],[f533])).

fof(f2357,plain,
    ( ~ spl9_325
    | spl9_221
    | spl9_223
    | spl9_319 ),
    inference(avatar_split_clause,[],[f2320,f2317,f1615,f1601,f2355])).

fof(f2355,plain,
    ( spl9_325
  <=> ~ m1_subset_1(k1_zfmisc_1(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_325])])).

fof(f2320,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_223
    | ~ spl9_319 ),
    inference(unit_resulting_resolution,[],[f1602,f1616,f258,f2318,f759])).

fof(f2346,plain,
    ( ~ spl9_323
    | spl9_319 ),
    inference(avatar_split_clause,[],[f2324,f2317,f2344])).

fof(f2344,plain,
    ( spl9_323
  <=> ~ r2_hidden(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_323])])).

fof(f2324,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_319 ),
    inference(unit_resulting_resolution,[],[f2318,f117])).

fof(f2339,plain,
    ( ~ spl9_321
    | spl9_319 ),
    inference(avatar_split_clause,[],[f2322,f2317,f2337])).

fof(f2337,plain,
    ( spl9_321
  <=> ~ r2_hidden(k1_zfmisc_1(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_321])])).

fof(f2322,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_319 ),
    inference(unit_resulting_resolution,[],[f258,f2318,f142])).

fof(f2319,plain,
    ( ~ spl9_319
    | ~ spl9_6
    | ~ spl9_310 ),
    inference(avatar_split_clause,[],[f2308,f2267,f170,f2317])).

fof(f2267,plain,
    ( spl9_310
  <=> r2_hidden(sK5(k1_zfmisc_1(sK8)),k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_310])])).

fof(f2308,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_310 ),
    inference(unit_resulting_resolution,[],[f2268,f355])).

fof(f2268,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK8)),k1_zfmisc_1(sK8))
    | ~ spl9_310 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f2290,plain,
    ( ~ spl9_317
    | spl9_165
    | ~ spl9_190 ),
    inference(avatar_split_clause,[],[f1862,f1234,f1106,f2288])).

fof(f2288,plain,
    ( spl9_317
  <=> ~ r2_hidden(k1_zfmisc_1(sK8),sK5(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_317])])).

fof(f1234,plain,
    ( spl9_190
  <=> m1_subset_1(sK5(sK4(sK8)),k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_190])])).

fof(f1862,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK8),sK5(sK4(sK8)))
    | ~ spl9_165
    | ~ spl9_190 ),
    inference(unit_resulting_resolution,[],[f1107,f1235,f289])).

fof(f1235,plain,
    ( m1_subset_1(sK5(sK4(sK8)),k1_zfmisc_1(sK8))
    | ~ spl9_190 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f2283,plain,
    ( ~ spl9_315
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1842,f1106,f2281])).

fof(f2281,plain,
    ( spl9_315
  <=> ~ r2_hidden(k1_zfmisc_1(sK8),sK5(k1_zfmisc_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f1842,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK8),sK5(k1_zfmisc_1(sK8)))
    | ~ spl9_165 ),
    inference(unit_resulting_resolution,[],[f1107,f115,f289])).

fof(f2276,plain,
    ( spl9_312
    | spl9_165
    | ~ spl9_190 ),
    inference(avatar_split_clause,[],[f1252,f1234,f1106,f2274])).

fof(f2274,plain,
    ( spl9_312
  <=> r2_hidden(sK5(sK4(sK8)),k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_312])])).

fof(f1252,plain,
    ( r2_hidden(sK5(sK4(sK8)),k1_zfmisc_1(sK8))
    | ~ spl9_165
    | ~ spl9_190 ),
    inference(unit_resulting_resolution,[],[f1107,f1235,f119])).

fof(f2269,plain,
    ( spl9_310
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1111,f1106,f2267])).

fof(f1111,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK8)),k1_zfmisc_1(sK8))
    | ~ spl9_165 ),
    inference(unit_resulting_resolution,[],[f115,f1107,f119])).

fof(f2262,plain,
    ( ~ spl9_309
    | ~ spl9_6
    | spl9_99 ),
    inference(avatar_split_clause,[],[f756,f742,f170,f2260])).

fof(f2260,plain,
    ( spl9_309
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_309])])).

fof(f742,plain,
    ( spl9_99
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f756,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK8))))
    | ~ spl9_6
    | ~ spl9_99 ),
    inference(unit_resulting_resolution,[],[f743,f232])).

fof(f743,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK8))))
    | ~ spl9_99 ),
    inference(avatar_component_clause,[],[f742])).

fof(f2250,plain,
    ( ~ spl9_307
    | spl9_99 ),
    inference(avatar_split_clause,[],[f753,f742,f2248])).

fof(f753,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK8)))))
    | ~ spl9_99 ),
    inference(unit_resulting_resolution,[],[f114,f743,f110])).

fof(f2226,plain,
    ( ~ spl9_305
    | spl9_143
    | ~ spl9_286 ),
    inference(avatar_split_clause,[],[f2065,f2061,f975,f2224])).

fof(f2224,plain,
    ( spl9_305
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k11_relat_1(sK1,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_305])])).

fof(f2065,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k11_relat_1(sK1,o_0_0_xboole_0))
    | ~ spl9_143
    | ~ spl9_286 ),
    inference(unit_resulting_resolution,[],[f976,f2062,f289])).

fof(f2219,plain,
    ( spl9_302
    | spl9_143
    | ~ spl9_286 ),
    inference(avatar_split_clause,[],[f2064,f2061,f975,f2217])).

fof(f2064,plain,
    ( r2_hidden(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_143
    | ~ spl9_286 ),
    inference(unit_resulting_resolution,[],[f976,f2062,f119])).

fof(f2212,plain,
    ( ~ spl9_301
    | spl9_143
    | ~ spl9_182 ),
    inference(avatar_split_clause,[],[f1861,f1198,f975,f2210])).

fof(f2210,plain,
    ( spl9_301
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_301])])).

fof(f1198,plain,
    ( spl9_182
  <=> m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f1861,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(sK4(sK0)))
    | ~ spl9_143
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f976,f1199,f289])).

fof(f1199,plain,
    ( m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_182 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f2205,plain,
    ( ~ spl9_299
    | spl9_143 ),
    inference(avatar_split_clause,[],[f1841,f975,f2203])).

fof(f2203,plain,
    ( spl9_299
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).

fof(f1841,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_143 ),
    inference(unit_resulting_resolution,[],[f976,f115,f289])).

fof(f2169,plain,
    ( ~ spl9_297
    | spl9_197
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1579,f1407,f1255,f2167])).

fof(f2167,plain,
    ( spl9_297
  <=> ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),o_0_0_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_297])])).

fof(f1255,plain,
    ( spl9_197
  <=> ~ m2_filter_1(sK7(sK2,sK1),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_197])])).

fof(f1579,plain,
    ( ~ m2_filter_1(sK7(o_0_0_xboole_0,sK1),o_0_0_xboole_0,sK1)
    | ~ spl9_197
    | ~ spl9_200 ),
    inference(forward_demodulation,[],[f1256,f1408])).

fof(f1256,plain,
    ( ~ m2_filter_1(sK7(sK2,sK1),sK2,sK1)
    | ~ spl9_197 ),
    inference(avatar_component_clause,[],[f1255])).

fof(f2148,plain,
    ( ~ spl9_295
    | spl9_221
    | spl9_291 ),
    inference(avatar_split_clause,[],[f2133,f2123,f1601,f2146])).

fof(f2123,plain,
    ( spl9_291
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).

fof(f2133,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_291 ),
    inference(unit_resulting_resolution,[],[f1602,f2124,f119])).

fof(f2124,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_291 ),
    inference(avatar_component_clause,[],[f2123])).

fof(f2132,plain,
    ( ~ spl9_293
    | spl9_289 ),
    inference(avatar_split_clause,[],[f2117,f2111,f2130])).

fof(f2130,plain,
    ( spl9_293
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).

fof(f2117,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_289 ),
    inference(unit_resulting_resolution,[],[f2112,f117])).

fof(f2125,plain,
    ( ~ spl9_291
    | spl9_289 ),
    inference(avatar_split_clause,[],[f2115,f2111,f2123])).

fof(f2115,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_289 ),
    inference(unit_resulting_resolution,[],[f258,f2112,f142])).

fof(f2113,plain,
    ( ~ spl9_289
    | ~ spl9_6
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f2097,f1519,f170,f2111])).

fof(f2097,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_210 ),
    inference(unit_resulting_resolution,[],[f1520,f355])).

fof(f2063,plain,
    ( spl9_286
    | ~ spl9_112
    | spl9_115
    | spl9_143
    | ~ spl9_258 ),
    inference(avatar_split_clause,[],[f1942,f1906,f975,f819,f810,f2061])).

fof(f1942,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_143
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1941,f976])).

fof(f1941,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_115
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1940,f820])).

fof(f1940,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_112
    | ~ spl9_258 ),
    inference(subsumption_resolution,[],[f1936,f813])).

fof(f1936,plain,
    ( m1_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_258 ),
    inference(resolution,[],[f1907,f123])).

fof(f2053,plain,
    ( ~ spl9_285
    | spl9_225
    | spl9_277 ),
    inference(avatar_split_clause,[],[f2026,f1990,f1644,f2051])).

fof(f2051,plain,
    ( spl9_285
  <=> ~ m1_subset_1(sK0,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_285])])).

fof(f1990,plain,
    ( spl9_277
  <=> ~ r2_hidden(sK0,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_277])])).

fof(f2026,plain,
    ( ~ m1_subset_1(sK0,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_225
    | ~ spl9_277 ),
    inference(unit_resulting_resolution,[],[f1645,f1991,f119])).

fof(f1991,plain,
    ( ~ r2_hidden(sK0,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_277 ),
    inference(avatar_component_clause,[],[f1990])).

fof(f2013,plain,
    ( spl9_282
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f1036,f225,f184,f163,f156,f149,f2011])).

fof(f1036,plain,
    ( m2_subset_1(k11_relat_1(sK1,sK5(sK0)),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f1034,f883])).

fof(f883,plain,
    ( k9_eqrel_1(sK0,sK1,sK5(sK0)) = k11_relat_1(sK1,sK5(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f150,f157,f164,f115,f185,f226,f137])).

fof(f1034,plain,
    ( m2_subset_1(k9_eqrel_1(sK0,sK1,sK5(sK0)),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f150,f157,f164,f115,f185,f226,f138])).

fof(f2006,plain,
    ( ~ spl9_281
    | spl9_221
    | spl9_265 ),
    inference(avatar_split_clause,[],[f1954,f1932,f1601,f2004])).

fof(f2004,plain,
    ( spl9_281
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_281])])).

fof(f1932,plain,
    ( spl9_265
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_265])])).

fof(f1954,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_221
    | ~ spl9_265 ),
    inference(unit_resulting_resolution,[],[f1602,f1933,f119])).

fof(f1933,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_265 ),
    inference(avatar_component_clause,[],[f1932])).

fof(f1999,plain,
    ( ~ spl9_279
    | spl9_263 ),
    inference(avatar_split_clause,[],[f1952,f1925,f1997])).

fof(f1997,plain,
    ( spl9_279
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_279])])).

fof(f1925,plain,
    ( spl9_263
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_263])])).

fof(f1952,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_263 ),
    inference(unit_resulting_resolution,[],[f1926,f117])).

fof(f1926,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_263 ),
    inference(avatar_component_clause,[],[f1925])).

fof(f1992,plain,
    ( ~ spl9_277
    | spl9_263 ),
    inference(avatar_split_clause,[],[f1950,f1925,f1990])).

fof(f1950,plain,
    ( ~ r2_hidden(sK0,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_263 ),
    inference(unit_resulting_resolution,[],[f258,f1926,f142])).

fof(f1985,plain,
    ( ~ spl9_275
    | ~ spl9_6
    | spl9_247 ),
    inference(avatar_split_clause,[],[f1824,f1792,f170,f1983])).

fof(f1983,plain,
    ( spl9_275
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_275])])).

fof(f1824,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6
    | ~ spl9_247 ),
    inference(unit_resulting_resolution,[],[f1793,f232])).

fof(f1978,plain,
    ( ~ spl9_273
    | spl9_133
    | spl9_247 ),
    inference(avatar_split_clause,[],[f1819,f1792,f915,f1976])).

fof(f1976,plain,
    ( spl9_273
  <=> ~ m1_subset_1(sK0,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_273])])).

fof(f915,plain,
    ( spl9_133
  <=> ~ r2_hidden(sK0,sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f1819,plain,
    ( ~ m1_subset_1(sK0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_133
    | ~ spl9_247 ),
    inference(unit_resulting_resolution,[],[f916,f1793,f119])).

fof(f916,plain,
    ( ~ r2_hidden(sK0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_133 ),
    inference(avatar_component_clause,[],[f915])).

fof(f1971,plain,
    ( spl9_270
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f883,f225,f184,f163,f156,f149,f1969])).

fof(f1969,plain,
    ( spl9_270
  <=> k9_eqrel_1(sK0,sK1,sK5(sK0)) = k11_relat_1(sK1,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_270])])).

fof(f1964,plain,
    ( ~ spl9_269
    | spl9_247 ),
    inference(avatar_split_clause,[],[f1817,f1792,f1962])).

fof(f1817,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_247 ),
    inference(unit_resulting_resolution,[],[f114,f1793,f110])).

fof(f1949,plain,
    ( ~ spl9_267
    | spl9_261 ),
    inference(avatar_split_clause,[],[f1919,f1913,f1947])).

fof(f1947,plain,
    ( spl9_267
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_267])])).

fof(f1919,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_261 ),
    inference(unit_resulting_resolution,[],[f1914,f117])).

fof(f1934,plain,
    ( ~ spl9_265
    | spl9_261 ),
    inference(avatar_split_clause,[],[f1917,f1913,f1932])).

fof(f1917,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK4(o_0_0_xboole_0))
    | ~ spl9_261 ),
    inference(unit_resulting_resolution,[],[f258,f1914,f142])).

fof(f1927,plain,
    ( ~ spl9_263
    | ~ spl9_78
    | spl9_245 ),
    inference(avatar_split_clause,[],[f1784,f1779,f627,f1925])).

fof(f1784,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl9_78
    | ~ spl9_245 ),
    inference(unit_resulting_resolution,[],[f628,f1780,f142])).

fof(f1915,plain,
    ( ~ spl9_261
    | ~ spl9_6
    | ~ spl9_240 ),
    inference(avatar_split_clause,[],[f1771,f1754,f170,f1913])).

fof(f1771,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_240 ),
    inference(unit_resulting_resolution,[],[f1755,f355])).

fof(f1908,plain,
    ( spl9_258
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f1410,f606,f225,f184,f163,f156,f149,f1906])).

fof(f1410,plain,
    ( m2_subset_1(k11_relat_1(sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_76 ),
    inference(forward_demodulation,[],[f1381,f1380])).

fof(f1380,plain,
    ( k9_eqrel_1(sK0,sK1,o_0_0_xboole_0) = k11_relat_1(sK1,o_0_0_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_76 ),
    inference(unit_resulting_resolution,[],[f150,f157,f164,f185,f226,f607,f137])).

fof(f1381,plain,
    ( m2_subset_1(k9_eqrel_1(sK0,sK1,o_0_0_xboole_0),k1_zfmisc_1(sK0),k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_76 ),
    inference(unit_resulting_resolution,[],[f150,f157,f164,f185,f226,f607,f138])).

fof(f1892,plain,
    ( ~ spl9_257
    | spl9_109
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1560,f1407,f790,f1890])).

fof(f1890,plain,
    ( spl9_257
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_257])])).

fof(f790,plain,
    ( spl9_109
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f1560,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_109
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f791])).

fof(f791,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK2)))
    | ~ spl9_109 ),
    inference(avatar_component_clause,[],[f790])).

fof(f1885,plain,
    ( ~ spl9_255
    | spl9_107
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1559,f1407,f783,f1883])).

fof(f1883,plain,
    ( spl9_255
  <=> ~ v1_xboole_0(sK4(sK4(sK4(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_255])])).

fof(f1559,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(o_0_0_xboole_0))))
    | ~ spl9_107
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f784])).

fof(f1838,plain,
    ( ~ spl9_253
    | spl9_173
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1609,f1601,f1152,f1836])).

fof(f1152,plain,
    ( spl9_173
  <=> ~ r2_hidden(sK4(sK8),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_173])])).

fof(f1609,plain,
    ( ~ m1_subset_1(sK4(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_173
    | ~ spl9_221 ),
    inference(unit_resulting_resolution,[],[f1153,f1602,f119])).

fof(f1153,plain,
    ( ~ r2_hidden(sK4(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_173 ),
    inference(avatar_component_clause,[],[f1152])).

fof(f1831,plain,
    ( ~ spl9_251
    | spl9_151
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1608,f1601,f1021,f1829])).

fof(f1021,plain,
    ( spl9_151
  <=> ~ r2_hidden(sK4(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_151])])).

fof(f1608,plain,
    ( ~ m1_subset_1(sK4(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_151
    | ~ spl9_221 ),
    inference(unit_resulting_resolution,[],[f1022,f1602,f119])).

fof(f1022,plain,
    ( ~ r2_hidden(sK4(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_151 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1815,plain,
    ( ~ spl9_249
    | ~ spl9_6
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1638,f1615,f170,f1813])).

fof(f1813,plain,
    ( spl9_249
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_249])])).

fof(f1638,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f1616,f232])).

fof(f1794,plain,
    ( ~ spl9_247
    | spl9_223 ),
    inference(avatar_split_clause,[],[f1623,f1615,f1792])).

fof(f1623,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_223 ),
    inference(unit_resulting_resolution,[],[f114,f1616,f110])).

fof(f1781,plain,
    ( ~ spl9_245
    | spl9_73
    | spl9_129
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1578,f1407,f900,f533,f1779])).

fof(f900,plain,
    ( spl9_129
  <=> ~ r2_hidden(sK2,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f1578,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_73
    | ~ spl9_129
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f1567,f1546])).

fof(f1546,plain,
    ( ~ v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl9_73
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f534])).

fof(f1567,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ spl9_129
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f903])).

fof(f903,plain,
    ( v1_xboole_0(sK4(o_0_0_xboole_0))
    | ~ m1_subset_1(sK2,sK4(o_0_0_xboole_0))
    | ~ spl9_129 ),
    inference(resolution,[],[f901,f119])).

fof(f901,plain,
    ( ~ r2_hidden(sK2,sK4(o_0_0_xboole_0))
    | ~ spl9_129 ),
    inference(avatar_component_clause,[],[f900])).

fof(f1763,plain,
    ( spl9_242
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f1380,f606,f225,f184,f163,f156,f149,f1761])).

fof(f1756,plain,
    ( spl9_240
    | ~ spl9_88
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1621,f1407,f693,f1754])).

fof(f693,plain,
    ( spl9_88
  <=> r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f1621,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_88
    | ~ spl9_200 ),
    inference(forward_demodulation,[],[f694,f1408])).

fof(f694,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f693])).

fof(f1749,plain,
    ( ~ spl9_239
    | spl9_129
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1566,f1407,f900,f1747])).

fof(f1566,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_129
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f901])).

fof(f1688,plain,
    ( ~ spl9_237
    | spl9_127
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1610,f1601,f892,f1686])).

fof(f1610,plain,
    ( ~ m1_subset_1(sK8,sK4(o_0_0_xboole_0))
    | ~ spl9_127
    | ~ spl9_221 ),
    inference(unit_resulting_resolution,[],[f893,f1602,f119])).

fof(f1681,plain,
    ( ~ spl9_235
    | spl9_125
    | spl9_221 ),
    inference(avatar_split_clause,[],[f1607,f1601,f879,f1679])).

fof(f1607,plain,
    ( ~ m1_subset_1(sK0,sK4(o_0_0_xboole_0))
    | ~ spl9_125
    | ~ spl9_221 ),
    inference(unit_resulting_resolution,[],[f880,f1602,f119])).

fof(f1674,plain,
    ( ~ spl9_233
    | spl9_131
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1568,f1407,f908,f1672])).

fof(f1568,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,o_0_0_xboole_0),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_131
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f909])).

fof(f1667,plain,
    ( ~ spl9_231
    | ~ spl9_200
    | spl9_215 ),
    inference(avatar_split_clause,[],[f1573,f1533,f1407,f1665])).

fof(f1533,plain,
    ( spl9_215
  <=> ~ v1_funct_1(sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_215])])).

fof(f1573,plain,
    ( ~ v1_funct_1(sK7(o_0_0_xboole_0,sK1))
    | ~ spl9_200
    | ~ spl9_215 ),
    inference(backward_demodulation,[],[f1408,f1534])).

fof(f1534,plain,
    ( ~ v1_funct_1(sK7(sK2,sK1))
    | ~ spl9_215 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f1660,plain,
    ( ~ spl9_229
    | spl9_87
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1551,f1407,f678,f1658])).

fof(f1658,plain,
    ( spl9_229
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_229])])).

fof(f1551,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(o_0_0_xboole_0))
    | ~ spl9_87
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f679])).

fof(f1653,plain,
    ( ~ spl9_227
    | spl9_83
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1550,f1407,f664,f1651])).

fof(f1651,plain,
    ( spl9_227
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_227])])).

fof(f664,plain,
    ( spl9_83
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f1550,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(o_0_0_xboole_0))
    | ~ spl9_83
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f665])).

fof(f665,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK2))
    | ~ spl9_83 ),
    inference(avatar_component_clause,[],[f664])).

fof(f1646,plain,
    ( ~ spl9_225
    | spl9_81
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1549,f1407,f657,f1644])).

fof(f657,plain,
    ( spl9_81
  <=> ~ v1_xboole_0(sK4(sK4(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f1549,plain,
    ( ~ v1_xboole_0(sK4(sK4(o_0_0_xboole_0)))
    | ~ spl9_81
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f658])).

fof(f658,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK2)))
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f657])).

fof(f1620,plain,
    ( spl9_222
    | spl9_89
    | ~ spl9_102
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1575,f1407,f766,f696,f1618])).

fof(f1618,plain,
    ( spl9_222
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f696,plain,
    ( spl9_89
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f1575,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_89
    | ~ spl9_102
    | ~ spl9_200 ),
    inference(subsumption_resolution,[],[f1556,f767])).

fof(f1556,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_89
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f699])).

fof(f699,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_89 ),
    inference(resolution,[],[f697,f119])).

fof(f697,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_89 ),
    inference(avatar_component_clause,[],[f696])).

fof(f1603,plain,
    ( ~ spl9_221
    | spl9_73
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1546,f1407,f533,f1601])).

fof(f1596,plain,
    ( ~ spl9_219
    | spl9_71
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1545,f1407,f526,f1594])).

fof(f1594,plain,
    ( spl9_219
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_219])])).

fof(f526,plain,
    ( spl9_71
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f1545,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl9_71
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f527])).

fof(f527,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK2)
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f526])).

fof(f1589,plain,
    ( spl9_216
    | ~ spl9_16
    | ~ spl9_200 ),
    inference(avatar_split_clause,[],[f1540,f1407,f205,f1587])).

fof(f1540,plain,
    ( r3_binop_1(sK0,o_0_0_xboole_0,sK3)
    | ~ spl9_16
    | ~ spl9_200 ),
    inference(backward_demodulation,[],[f1408,f206])).

fof(f1538,plain,
    ( spl9_214
    | ~ spl9_40
    | spl9_69
    | ~ spl9_196 ),
    inference(avatar_split_clause,[],[f1531,f1258,f507,f327,f1536])).

fof(f1536,plain,
    ( spl9_214
  <=> v1_funct_1(sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f507,plain,
    ( spl9_69
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f1258,plain,
    ( spl9_196
  <=> m2_filter_1(sK7(sK2,sK1),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_196])])).

fof(f1531,plain,
    ( v1_funct_1(sK7(sK2,sK1))
    | ~ spl9_40
    | ~ spl9_69
    | ~ spl9_196 ),
    inference(unit_resulting_resolution,[],[f508,f328,f1259,f127])).

fof(f1259,plain,
    ( m2_filter_1(sK7(sK2,sK1),sK2,sK1)
    | ~ spl9_196 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f508,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_69 ),
    inference(avatar_component_clause,[],[f507])).

fof(f1528,plain,
    ( spl9_212
    | spl9_143
    | ~ spl9_182 ),
    inference(avatar_split_clause,[],[f1210,f1198,f975,f1526])).

fof(f1526,plain,
    ( spl9_212
  <=> r2_hidden(sK5(sK4(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f1210,plain,
    ( r2_hidden(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_143
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f976,f1199,f119])).

fof(f1521,plain,
    ( spl9_210
    | spl9_143 ),
    inference(avatar_split_clause,[],[f980,f975,f1519])).

fof(f980,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_143 ),
    inference(unit_resulting_resolution,[],[f115,f976,f119])).

fof(f1500,plain,
    ( ~ spl9_209
    | ~ spl9_6
    | spl9_117 ),
    inference(avatar_split_clause,[],[f846,f831,f170,f1498])).

fof(f1498,plain,
    ( spl9_209
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_209])])).

fof(f831,plain,
    ( spl9_117
  <=> ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f846,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl9_6
    | ~ spl9_117 ),
    inference(unit_resulting_resolution,[],[f832,f232])).

fof(f832,plain,
    ( ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl9_117 ),
    inference(avatar_component_clause,[],[f831])).

fof(f1493,plain,
    ( ~ spl9_207
    | spl9_117 ),
    inference(avatar_split_clause,[],[f843,f831,f1491])).

fof(f843,plain,
    ( ~ v1_xboole_0(sK4(sK4(k8_eqrel_1(sK0,sK1))))
    | ~ spl9_117 ),
    inference(unit_resulting_resolution,[],[f114,f832,f110])).

fof(f1486,plain,
    ( ~ spl9_205
    | ~ spl9_6
    | spl9_95 ),
    inference(avatar_split_clause,[],[f728,f721,f170,f1484])).

fof(f1484,plain,
    ( spl9_205
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_205])])).

fof(f721,plain,
    ( spl9_95
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f728,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK0))))
    | ~ spl9_6
    | ~ spl9_95 ),
    inference(unit_resulting_resolution,[],[f722,f232])).

fof(f722,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK0))))
    | ~ spl9_95 ),
    inference(avatar_component_clause,[],[f721])).

fof(f1479,plain,
    ( ~ spl9_203
    | spl9_95 ),
    inference(avatar_split_clause,[],[f725,f721,f1477])).

fof(f725,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl9_95 ),
    inference(unit_resulting_resolution,[],[f114,f722,f110])).

fof(f1409,plain,
    ( spl9_200
    | ~ spl9_6
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f1295,f510,f170,f1407])).

fof(f510,plain,
    ( spl9_68
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f1295,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl9_6
    | ~ spl9_68 ),
    inference(unit_resulting_resolution,[],[f511,f210])).

fof(f511,plain,
    ( v1_xboole_0(sK2)
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f510])).

fof(f1397,plain,
    ( ~ spl9_199
    | ~ spl9_6
    | spl9_67
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f1305,f510,f504,f170,f1395])).

fof(f1395,plain,
    ( spl9_199
  <=> ~ m1_subset_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_199])])).

fof(f504,plain,
    ( spl9_67
  <=> ~ m1_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f1305,plain,
    ( ~ m1_subset_1(sK0,o_0_0_xboole_0)
    | ~ spl9_6
    | ~ spl9_67
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f1295,f505])).

fof(f505,plain,
    ( ~ m1_subset_1(sK0,sK2)
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1342,plain,
    ( ~ spl9_6
    | ~ spl9_68
    | spl9_85
    | ~ spl9_102 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_68
    | ~ spl9_85
    | ~ spl9_102 ),
    inference(subsumption_resolution,[],[f1315,f767])).

fof(f1315,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_68
    | ~ spl9_85 ),
    inference(backward_demodulation,[],[f1295,f672])).

fof(f672,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl9_85
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f1265,plain,
    ( ~ spl9_68
    | ~ spl9_74 ),
    inference(avatar_contradiction_clause,[],[f1264])).

fof(f1264,plain,
    ( $false
    | ~ spl9_68
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f511,f652])).

fof(f652,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_74 ),
    inference(resolution,[],[f546,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t7_boole)).

fof(f546,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f545])).

fof(f545,plain,
    ( spl9_74
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f1263,plain,
    ( spl9_1
    | ~ spl9_76
    | spl9_79 ),
    inference(avatar_contradiction_clause,[],[f1262])).

fof(f1262,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_76
    | ~ spl9_79 ),
    inference(subsumption_resolution,[],[f607,f1261])).

fof(f1261,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl9_1
    | ~ spl9_79 ),
    inference(subsumption_resolution,[],[f634,f150])).

fof(f634,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl9_79 ),
    inference(resolution,[],[f631,f119])).

fof(f631,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK0)
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl9_79
  <=> ~ r2_hidden(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f1260,plain,
    ( spl9_196
    | ~ spl9_40
    | spl9_69 ),
    inference(avatar_split_clause,[],[f612,f507,f327,f1258])).

fof(f612,plain,
    ( m2_filter_1(sK7(sK2,sK1),sK2,sK1)
    | ~ spl9_40
    | ~ spl9_69 ),
    inference(unit_resulting_resolution,[],[f328,f508,f130])).

fof(f1250,plain,
    ( spl9_194
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f834,f225,f184,f163,f156,f1248])).

fof(f1248,plain,
    ( spl9_194
  <=> k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).

fof(f834,plain,
    ( k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f157,f164,f185,f226,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',redefinition_k8_eqrel_1)).

fof(f1243,plain,
    ( ~ spl9_193
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f1097,f1089,f1241])).

fof(f1241,plain,
    ( spl9_193
  <=> ~ r2_hidden(sK4(sK8),sK5(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_193])])).

fof(f1089,plain,
    ( spl9_162
  <=> r2_hidden(sK5(sK4(sK8)),sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f1097,plain,
    ( ~ r2_hidden(sK4(sK8),sK5(sK4(sK8)))
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f1090,f116])).

fof(f1090,plain,
    ( r2_hidden(sK5(sK4(sK8)),sK4(sK8))
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f1089])).

fof(f1236,plain,
    ( spl9_190
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f1092,f1089,f1234])).

fof(f1092,plain,
    ( m1_subset_1(sK5(sK4(sK8)),k1_zfmisc_1(sK8))
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f258,f1090,f142])).

fof(f1229,plain,
    ( ~ spl9_189
    | spl9_57 ),
    inference(avatar_split_clause,[],[f423,f413,f1227])).

fof(f1227,plain,
    ( spl9_189
  <=> ~ r2_hidden(sK8,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).

fof(f423,plain,
    ( ~ r2_hidden(sK8,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_57 ),
    inference(unit_resulting_resolution,[],[f115,f414,f142])).

fof(f1217,plain,
    ( ~ spl9_187
    | spl9_77
    | ~ spl9_182 ),
    inference(avatar_split_clause,[],[f1209,f1198,f603,f1215])).

fof(f1215,plain,
    ( spl9_187
  <=> ~ r2_hidden(o_0_0_xboole_0,sK5(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_187])])).

fof(f603,plain,
    ( spl9_77
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f1209,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(sK4(sK0)))
    | ~ spl9_77
    | ~ spl9_182 ),
    inference(unit_resulting_resolution,[],[f604,f1199,f142])).

fof(f604,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f603])).

fof(f1207,plain,
    ( ~ spl9_185
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f966,f937,f1205])).

fof(f1205,plain,
    ( spl9_185
  <=> ~ r2_hidden(sK4(sK0),sK5(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_185])])).

fof(f937,plain,
    ( spl9_134
  <=> r2_hidden(sK5(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f966,plain,
    ( ~ r2_hidden(sK4(sK0),sK5(sK4(sK0)))
    | ~ spl9_134 ),
    inference(unit_resulting_resolution,[],[f938,f116])).

fof(f938,plain,
    ( r2_hidden(sK5(sK4(sK0)),sK4(sK0))
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f937])).

fof(f1200,plain,
    ( spl9_182
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f961,f937,f1198])).

fof(f961,plain,
    ( m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl9_134 ),
    inference(unit_resulting_resolution,[],[f258,f938,f142])).

fof(f1193,plain,
    ( ~ spl9_181
    | spl9_47 ),
    inference(avatar_split_clause,[],[f421,f370,f1191])).

fof(f1191,plain,
    ( spl9_181
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_181])])).

fof(f421,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f371,f115,f142])).

fof(f1180,plain,
    ( ~ spl9_179
    | ~ spl9_6
    | spl9_167 ),
    inference(avatar_split_clause,[],[f1136,f1121,f170,f1178])).

fof(f1178,plain,
    ( spl9_179
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_179])])).

fof(f1121,plain,
    ( spl9_167
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_167])])).

fof(f1136,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK8)))
    | ~ spl9_6
    | ~ spl9_167 ),
    inference(unit_resulting_resolution,[],[f1122,f232])).

fof(f1122,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK8)))
    | ~ spl9_167 ),
    inference(avatar_component_clause,[],[f1121])).

fof(f1173,plain,
    ( ~ spl9_177
    | spl9_167 ),
    inference(avatar_split_clause,[],[f1132,f1121,f1171])).

fof(f1132,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK8))))
    | ~ spl9_167 ),
    inference(unit_resulting_resolution,[],[f114,f1122,f110])).

fof(f1161,plain,
    ( ~ spl9_175
    | spl9_171 ),
    inference(avatar_split_clause,[],[f1146,f1141,f1159])).

fof(f1159,plain,
    ( spl9_175
  <=> ~ r2_hidden(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_175])])).

fof(f1146,plain,
    ( ~ r2_hidden(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_171 ),
    inference(unit_resulting_resolution,[],[f1142,f117])).

fof(f1154,plain,
    ( ~ spl9_173
    | spl9_171 ),
    inference(avatar_split_clause,[],[f1144,f1141,f1152])).

fof(f1144,plain,
    ( ~ r2_hidden(sK4(sK8),sK4(o_0_0_xboole_0))
    | ~ spl9_171 ),
    inference(unit_resulting_resolution,[],[f258,f1142,f142])).

fof(f1143,plain,
    ( ~ spl9_171
    | ~ spl9_6
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f1093,f1089,f170,f1141])).

fof(f1093,plain,
    ( ~ m1_subset_1(sK4(sK8),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f171,f1090,f143])).

fof(f1130,plain,
    ( ~ spl9_169
    | ~ spl9_6
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1116,f1106,f170,f1128])).

fof(f1128,plain,
    ( spl9_169
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_169])])).

fof(f1116,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK8))
    | ~ spl9_6
    | ~ spl9_165 ),
    inference(unit_resulting_resolution,[],[f1107,f232])).

fof(f1123,plain,
    ( ~ spl9_167
    | spl9_165 ),
    inference(avatar_split_clause,[],[f1110,f1106,f1121])).

fof(f1110,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK8)))
    | ~ spl9_165 ),
    inference(unit_resulting_resolution,[],[f114,f1107,f110])).

fof(f1108,plain,
    ( ~ spl9_165
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f1094,f1089,f1106])).

fof(f1094,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK8))
    | ~ spl9_162 ),
    inference(unit_resulting_resolution,[],[f258,f1090,f143])).

fof(f1091,plain,
    ( spl9_162
    | spl9_27 ),
    inference(avatar_split_clause,[],[f286,f255,f1089])).

fof(f286,plain,
    ( r2_hidden(sK5(sK4(sK8)),sK4(sK8))
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f115,f256,f119])).

fof(f1081,plain,
    ( spl9_160
    | spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(avatar_split_clause,[],[f1074,f951,f327,f177,f1079])).

fof(f1079,plain,
    ( spl9_160
  <=> v1_funct_1(sK7(sK8,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f1074,plain,
    ( v1_funct_1(sK7(sK8,sK1))
    | ~ spl9_9
    | ~ spl9_40
    | ~ spl9_138 ),
    inference(unit_resulting_resolution,[],[f178,f328,f952,f127])).

fof(f1071,plain,
    ( spl9_158
    | spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1061,f944,f327,f149,f1069])).

fof(f1061,plain,
    ( v1_funct_1(sK7(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_40
    | ~ spl9_136 ),
    inference(unit_resulting_resolution,[],[f150,f328,f945,f127])).

fof(f1052,plain,
    ( ~ spl9_157
    | ~ spl9_6
    | spl9_145 ),
    inference(avatar_split_clause,[],[f1005,f990,f170,f1050])).

fof(f1050,plain,
    ( spl9_157
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_157])])).

fof(f990,plain,
    ( spl9_145
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f1005,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK0)))
    | ~ spl9_6
    | ~ spl9_145 ),
    inference(unit_resulting_resolution,[],[f991,f232])).

fof(f991,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl9_145 ),
    inference(avatar_component_clause,[],[f990])).

fof(f1045,plain,
    ( ~ spl9_155
    | spl9_145 ),
    inference(avatar_split_clause,[],[f1001,f990,f1043])).

fof(f1001,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl9_145 ),
    inference(unit_resulting_resolution,[],[f114,f991,f110])).

fof(f1030,plain,
    ( ~ spl9_153
    | spl9_149 ),
    inference(avatar_split_clause,[],[f1015,f1010,f1028])).

fof(f1028,plain,
    ( spl9_153
  <=> ~ r2_hidden(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f1015,plain,
    ( ~ r2_hidden(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_149 ),
    inference(unit_resulting_resolution,[],[f1011,f117])).

fof(f1023,plain,
    ( ~ spl9_151
    | spl9_149 ),
    inference(avatar_split_clause,[],[f1013,f1010,f1021])).

fof(f1013,plain,
    ( ~ r2_hidden(sK4(sK0),sK4(o_0_0_xboole_0))
    | ~ spl9_149 ),
    inference(unit_resulting_resolution,[],[f258,f1011,f142])).

fof(f1012,plain,
    ( ~ spl9_149
    | ~ spl9_6
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f962,f937,f170,f1010])).

fof(f962,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_134 ),
    inference(unit_resulting_resolution,[],[f171,f938,f143])).

fof(f999,plain,
    ( ~ spl9_147
    | ~ spl9_6
    | spl9_143 ),
    inference(avatar_split_clause,[],[f985,f975,f170,f997])).

fof(f997,plain,
    ( spl9_147
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f985,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl9_6
    | ~ spl9_143 ),
    inference(unit_resulting_resolution,[],[f976,f232])).

fof(f992,plain,
    ( ~ spl9_145
    | spl9_143 ),
    inference(avatar_split_clause,[],[f979,f975,f990])).

fof(f979,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl9_143 ),
    inference(unit_resulting_resolution,[],[f114,f976,f110])).

fof(f977,plain,
    ( ~ spl9_143
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f963,f937,f975])).

fof(f963,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl9_134 ),
    inference(unit_resulting_resolution,[],[f258,f938,f143])).

fof(f960,plain,
    ( spl9_140
    | spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f686,f327,f198,f149,f958])).

fof(f686,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f150,f328,f199,f128])).

fof(f953,plain,
    ( spl9_138
    | spl9_9
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f398,f327,f177,f951])).

fof(f398,plain,
    ( m2_filter_1(sK7(sK8,sK1),sK8,sK1)
    | ~ spl9_9
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f178,f328,f130])).

fof(f946,plain,
    ( spl9_136
    | spl9_1
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f397,f327,f149,f944])).

fof(f397,plain,
    ( m2_filter_1(sK7(sK0,sK1),sK0,sK1)
    | ~ spl9_1
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f150,f328,f130])).

fof(f939,plain,
    ( spl9_134
    | spl9_23 ),
    inference(avatar_split_clause,[],[f285,f239,f937])).

fof(f285,plain,
    ( r2_hidden(sK5(sK4(sK0)),sK4(sK0))
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f115,f240,f119])).

fof(f917,plain,
    ( ~ spl9_133
    | spl9_111 ),
    inference(avatar_split_clause,[],[f874,f797,f915])).

fof(f874,plain,
    ( ~ r2_hidden(sK0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_111 ),
    inference(unit_resulting_resolution,[],[f798,f258,f142])).

fof(f910,plain,
    ( ~ spl9_131
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | spl9_63 ),
    inference(avatar_split_clause,[],[f885,f446,f225,f191,f184,f163,f156,f149,f908])).

fof(f446,plain,
    ( spl9_63
  <=> ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f885,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k11_relat_1(sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_63 ),
    inference(backward_demodulation,[],[f882,f447])).

fof(f447,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl9_63 ),
    inference(avatar_component_clause,[],[f446])).

fof(f902,plain,
    ( ~ spl9_129
    | spl9_85 ),
    inference(avatar_split_clause,[],[f873,f671,f900])).

fof(f873,plain,
    ( ~ r2_hidden(sK2,sK4(o_0_0_xboole_0))
    | ~ spl9_85 ),
    inference(unit_resulting_resolution,[],[f672,f258,f142])).

fof(f894,plain,
    ( ~ spl9_127
    | spl9_57 ),
    inference(avatar_split_clause,[],[f872,f413,f892])).

fof(f872,plain,
    ( ~ r2_hidden(sK8,sK4(o_0_0_xboole_0))
    | ~ spl9_57 ),
    inference(unit_resulting_resolution,[],[f414,f258,f142])).

fof(f881,plain,
    ( ~ spl9_125
    | spl9_47 ),
    inference(avatar_split_clause,[],[f871,f370,f879])).

fof(f871,plain,
    ( ~ r2_hidden(sK0,sK4(o_0_0_xboole_0))
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f371,f258,f142])).

fof(f869,plain,
    ( ~ spl9_123
    | spl9_111 ),
    inference(avatar_split_clause,[],[f849,f797,f867])).

fof(f867,plain,
    ( spl9_123
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f849,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_111 ),
    inference(unit_resulting_resolution,[],[f798,f117])).

fof(f858,plain,
    ( ~ spl9_121
    | spl9_111 ),
    inference(avatar_split_clause,[],[f847,f797,f856])).

fof(f856,plain,
    ( spl9_121
  <=> ~ m1_eqrel_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f847,plain,
    ( ~ m1_eqrel_1(sK0,o_0_0_xboole_0)
    | ~ spl9_111 ),
    inference(unit_resulting_resolution,[],[f798,f118])).

fof(f841,plain,
    ( ~ spl9_119
    | ~ spl9_6
    | spl9_115 ),
    inference(avatar_split_clause,[],[f826,f819,f170,f839])).

fof(f839,plain,
    ( spl9_119
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f826,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k8_eqrel_1(sK0,sK1))
    | ~ spl9_6
    | ~ spl9_115 ),
    inference(unit_resulting_resolution,[],[f820,f232])).

fof(f833,plain,
    ( ~ spl9_117
    | spl9_115 ),
    inference(avatar_split_clause,[],[f823,f819,f831])).

fof(f823,plain,
    ( ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl9_115 ),
    inference(unit_resulting_resolution,[],[f114,f820,f110])).

fof(f821,plain,
    ( ~ spl9_115
    | spl9_1
    | ~ spl9_112 ),
    inference(avatar_split_clause,[],[f814,f810,f149,f819])).

fof(f814,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_112 ),
    inference(unit_resulting_resolution,[],[f150,f811,f110])).

fof(f812,plain,
    ( spl9_112
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f805,f225,f184,f163,f156,f810])).

fof(f805,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f157,f164,f185,f226,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_k8_eqrel_1)).

fof(f799,plain,
    ( ~ spl9_111
    | ~ spl9_34
    | spl9_85 ),
    inference(avatar_split_clause,[],[f687,f671,f296,f797])).

fof(f296,plain,
    ( spl9_34
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f687,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_34
    | ~ spl9_85 ),
    inference(unit_resulting_resolution,[],[f297,f672,f142])).

fof(f297,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f792,plain,
    ( ~ spl9_109
    | ~ spl9_6
    | spl9_81 ),
    inference(avatar_split_clause,[],[f685,f657,f170,f790])).

fof(f685,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK2)))
    | ~ spl9_6
    | ~ spl9_81 ),
    inference(unit_resulting_resolution,[],[f658,f232])).

fof(f785,plain,
    ( ~ spl9_107
    | spl9_81 ),
    inference(avatar_split_clause,[],[f682,f657,f783])).

fof(f682,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK2))))
    | ~ spl9_81 ),
    inference(unit_resulting_resolution,[],[f114,f658,f110])).

fof(f776,plain,
    ( ~ spl9_105
    | spl9_67 ),
    inference(avatar_split_clause,[],[f519,f504,f774])).

fof(f774,plain,
    ( spl9_105
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f519,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(sK2)))
    | ~ spl9_67 ),
    inference(unit_resulting_resolution,[],[f115,f505,f142])).

fof(f768,plain,
    ( spl9_102
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f761,f749,f766])).

fof(f749,plain,
    ( spl9_100
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f761,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_100 ),
    inference(superposition,[],[f115,f750])).

fof(f750,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f749])).

fof(f751,plain,
    ( spl9_100
    | ~ spl9_6
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f478,f461,f170,f749])).

fof(f461,plain,
    ( spl9_64
  <=> v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f478,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_64 ),
    inference(unit_resulting_resolution,[],[f462,f210])).

fof(f462,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f461])).

fof(f744,plain,
    ( ~ spl9_99
    | spl9_53 ),
    inference(avatar_split_clause,[],[f419,f394,f742])).

fof(f419,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK8))))
    | ~ spl9_53 ),
    inference(unit_resulting_resolution,[],[f114,f395,f110])).

fof(f737,plain,
    ( ~ spl9_97
    | ~ spl9_6
    | spl9_53 ),
    inference(avatar_split_clause,[],[f418,f394,f170,f735])).

fof(f735,plain,
    ( spl9_97
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f418,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK8)))
    | ~ spl9_6
    | ~ spl9_53 ),
    inference(unit_resulting_resolution,[],[f171,f395,f110])).

fof(f723,plain,
    ( ~ spl9_95
    | spl9_33 ),
    inference(avatar_split_clause,[],[f358,f279,f721])).

fof(f358,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK0))))
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f114,f280,f110])).

fof(f716,plain,
    ( ~ spl9_93
    | ~ spl9_6
    | spl9_33 ),
    inference(avatar_split_clause,[],[f357,f279,f170,f714])).

fof(f714,plain,
    ( spl9_93
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f357,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK0)))
    | ~ spl9_6
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f171,f280,f110])).

fof(f706,plain,
    ( ~ spl9_91
    | spl9_77 ),
    inference(avatar_split_clause,[],[f615,f603,f704])).

fof(f615,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK5(k1_zfmisc_1(sK0)))
    | ~ spl9_77 ),
    inference(unit_resulting_resolution,[],[f115,f604,f142])).

fof(f698,plain,
    ( ~ spl9_89
    | spl9_85 ),
    inference(avatar_split_clause,[],[f689,f671,f696])).

fof(f689,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_85 ),
    inference(unit_resulting_resolution,[],[f672,f117])).

fof(f680,plain,
    ( ~ spl9_87
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f648,f545,f678])).

fof(f648,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl9_74 ),
    inference(unit_resulting_resolution,[],[f546,f116])).

fof(f673,plain,
    ( ~ spl9_85
    | ~ spl9_6
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f645,f545,f170,f671])).

fof(f645,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_74 ),
    inference(unit_resulting_resolution,[],[f171,f546,f143])).

fof(f666,plain,
    ( ~ spl9_83
    | ~ spl9_6
    | spl9_73 ),
    inference(avatar_split_clause,[],[f540,f533,f170,f664])).

fof(f540,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK2))
    | ~ spl9_6
    | ~ spl9_73 ),
    inference(unit_resulting_resolution,[],[f534,f232])).

fof(f659,plain,
    ( ~ spl9_81
    | spl9_73 ),
    inference(avatar_split_clause,[],[f537,f533,f657])).

fof(f537,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK2)))
    | ~ spl9_73 ),
    inference(unit_resulting_resolution,[],[f114,f534,f110])).

fof(f632,plain,
    ( ~ spl9_79
    | spl9_77 ),
    inference(avatar_split_clause,[],[f616,f603,f630])).

fof(f616,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK0)
    | ~ spl9_77 ),
    inference(unit_resulting_resolution,[],[f604,f117])).

fof(f608,plain,
    ( spl9_76
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f569,f510,f191,f170,f606])).

fof(f569,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK0)
    | ~ spl9_6
    | ~ spl9_12
    | ~ spl9_68 ),
    inference(backward_demodulation,[],[f563,f192])).

fof(f563,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl9_6
    | ~ spl9_68 ),
    inference(unit_resulting_resolution,[],[f511,f210])).

fof(f547,plain,
    ( spl9_74
    | spl9_69 ),
    inference(avatar_split_clause,[],[f515,f507,f545])).

fof(f515,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl9_69 ),
    inference(unit_resulting_resolution,[],[f115,f508,f119])).

fof(f535,plain,
    ( ~ spl9_73
    | spl9_69 ),
    inference(avatar_split_clause,[],[f518,f507,f533])).

fof(f518,plain,
    ( ~ v1_xboole_0(sK4(sK2))
    | ~ spl9_69 ),
    inference(unit_resulting_resolution,[],[f114,f508,f110])).

fof(f528,plain,
    ( ~ spl9_71
    | ~ spl9_6
    | spl9_69 ),
    inference(avatar_split_clause,[],[f517,f507,f170,f526])).

fof(f517,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK2)
    | ~ spl9_6
    | ~ spl9_69 ),
    inference(unit_resulting_resolution,[],[f171,f508,f110])).

fof(f512,plain,
    ( ~ spl9_67
    | spl9_68
    | spl9_37 ),
    inference(avatar_split_clause,[],[f313,f310,f510,f504])).

fof(f310,plain,
    ( spl9_37
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f313,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK0,sK2)
    | ~ spl9_37 ),
    inference(resolution,[],[f311,f119])).

fof(f311,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f310])).

fof(f463,plain,
    ( spl9_64
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f455,f170,f461])).

fof(f455,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f115,f354,f119])).

fof(f354,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f171,f115,f143])).

fof(f448,plain,(
    ~ spl9_63 ),
    inference(avatar_split_clause,[],[f108,f446])).

fof(f108,plain,(
    ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ~ r3_binop_1(k8_eqrel_1(sK0,sK1),k9_eqrel_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r3_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f85,f84,f83,f82])).

fof(f82,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r3_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m1_subset_1(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(sK0,X1),k9_eqrel_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r3_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m1_subset_1(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r3_binop_1(k8_eqrel_1(X0,sK1),k9_eqrel_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3))
                & r3_binop_1(X0,X2,X3)
                & m2_filter_1(X3,X0,sK1) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK1)
        & v3_relat_2(sK1)
        & v1_partfun1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
              & r3_binop_1(X0,X2,X3)
              & m2_filter_1(X3,X0,X1) )
          & m1_subset_1(X2,X0) )
     => ( ? [X3] :
            ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,sK2),k3_filter_1(X0,X1,X3))
            & r3_binop_1(X0,sK2,X3)
            & m2_filter_1(X3,X0,X1) )
        & m1_subset_1(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r3_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r3_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r3_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r3_binop_1(X0,X2,X3)
                     => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r3_binop_1(X0,X2,X3)
                   => r3_binop_1(k8_eqrel_1(X0,X1),k9_eqrel_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',t8_filter_1)).

fof(f440,plain,
    ( ~ spl9_61
    | spl9_57 ),
    inference(avatar_split_clause,[],[f424,f413,f438])).

fof(f438,plain,
    ( spl9_61
  <=> ~ r2_hidden(sK8,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f424,plain,
    ( ~ r2_hidden(sK8,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_57 ),
    inference(unit_resulting_resolution,[],[f414,f117])).

fof(f432,plain,
    ( ~ spl9_59
    | spl9_47 ),
    inference(avatar_split_clause,[],[f382,f370,f430])).

fof(f430,plain,
    ( spl9_59
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f382,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f371,f117])).

fof(f415,plain,
    ( ~ spl9_57
    | ~ spl9_6
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f353,f341,f170,f413])).

fof(f353,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f342,f171,f143])).

fof(f408,plain,
    ( ~ spl9_55
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f346,f341,f406])).

fof(f346,plain,
    ( ~ r2_hidden(sK8,sK5(sK8))
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f342,f116])).

fof(f396,plain,
    ( ~ spl9_53
    | spl9_27 ),
    inference(avatar_split_clause,[],[f267,f255,f394])).

fof(f267,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK8)))
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f114,f256,f110])).

fof(f389,plain,
    ( ~ spl9_51
    | ~ spl9_6
    | spl9_27 ),
    inference(avatar_split_clause,[],[f266,f255,f170,f387])).

fof(f387,plain,
    ( spl9_51
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f266,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK8))
    | ~ spl9_6
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f171,f256,f110])).

fof(f381,plain,
    ( spl9_48
    | spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f374,f327,f198,f149,f379])).

fof(f374,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f150,f328,f199,f127])).

fof(f372,plain,
    ( ~ spl9_47
    | ~ spl9_6
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f352,f318,f170,f370])).

fof(f352,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_6
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f319,f171,f143])).

fof(f365,plain,
    ( ~ spl9_45
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f332,f318,f363])).

fof(f332,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f319,f116])).

fof(f343,plain,
    ( spl9_42
    | spl9_9 ),
    inference(avatar_split_clause,[],[f284,f177,f341])).

fof(f284,plain,
    ( r2_hidden(sK5(sK8),sK8)
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f115,f178,f119])).

fof(f329,plain,
    ( spl9_40
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f322,f225,f327])).

fof(f322,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f226,f136])).

fof(f320,plain,
    ( spl9_38
    | spl9_1 ),
    inference(avatar_split_clause,[],[f283,f149,f318])).

fof(f283,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f115,f150,f119])).

fof(f312,plain,
    ( ~ spl9_37
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f301,f296,f310])).

fof(f301,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f297,f116])).

fof(f298,plain,
    ( spl9_34
    | spl9_1
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f282,f191,f149,f296])).

fof(f282,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl9_1
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f192,f150,f119])).

fof(f281,plain,
    ( ~ spl9_33
    | spl9_23 ),
    inference(avatar_split_clause,[],[f250,f239,f279])).

fof(f250,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK0)))
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f114,f240,f110])).

fof(f274,plain,
    ( ~ spl9_31
    | ~ spl9_6
    | spl9_23 ),
    inference(avatar_split_clause,[],[f249,f239,f170,f272])).

fof(f272,plain,
    ( spl9_31
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f249,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK0))
    | ~ spl9_6
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f171,f240,f110])).

fof(f265,plain,
    ( ~ spl9_29
    | ~ spl9_6
    | spl9_9 ),
    inference(avatar_split_clause,[],[f231,f177,f170,f263])).

fof(f263,plain,
    ( spl9_29
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f231,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK8)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f178,f171,f110])).

fof(f257,plain,
    ( ~ spl9_27
    | spl9_9 ),
    inference(avatar_split_clause,[],[f229,f177,f255])).

fof(f229,plain,
    ( ~ v1_xboole_0(sK4(sK8))
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f178,f114,f110])).

fof(f248,plain,
    ( ~ spl9_25
    | spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f230,f170,f149,f246])).

fof(f246,plain,
    ( spl9_25
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f230,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK0)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f150,f171,f110])).

fof(f241,plain,
    ( ~ spl9_23
    | spl9_1 ),
    inference(avatar_split_clause,[],[f228,f149,f239])).

fof(f228,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f150,f114,f110])).

fof(f227,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f104,f225])).

fof(f104,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f86])).

fof(f217,plain,
    ( spl9_18
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f208,f170,f215])).

fof(f215,plain,
    ( spl9_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f207,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f107,f205])).

fof(f107,plain,(
    r3_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f86])).

fof(f200,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f106,f198])).

fof(f106,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f193,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f105,f191])).

fof(f105,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f186,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f101,f184])).

fof(f101,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f179,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f144,f177])).

fof(f144,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f98])).

fof(f98,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',rc7_funct_1)).

fof(f172,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f109,f170])).

fof(f109,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t8_filter_1.p',dt_o_0_0_xboole_0)).

fof(f165,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f103,f163])).

fof(f103,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f158,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f102,f156])).

fof(f102,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f86])).

fof(f151,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f100,f149])).

fof(f100,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------

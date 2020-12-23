%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1759+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:29 EST 2020

% Result     : Theorem 9.35s
% Output     : Refutation 9.96s
% Verified   : 
% Statistics : Number of formulae       : 1249 (5449 expanded)
%              Number of leaves         :  370 (2543 expanded)
%              Depth                    :   11
%              Number of atoms          : 8627 (30488 expanded)
%              Number of equality atoms :   62 ( 679 expanded)
%              Maximal formula depth    :   47 (   9 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f136,f141,f146,f151,f156,f161,f166,f171,f176,f181,f186,f191,f196,f201,f206,f211,f216,f224,f236,f244,f252,f262,f266,f274,f279,f291,f314,f322,f324,f337,f345,f347,f361,f365,f367,f386,f390,f392,f396,f404,f408,f422,f424,f428,f438,f460,f464,f472,f482,f486,f494,f503,f520,f529,f546,f555,f565,f574,f621,f626,f647,f652,f669,f673,f685,f725,f730,f751,f755,f777,f781,f825,f829,f833,f837,f841,f845,f849,f853,f857,f872,f877,f912,f916,f932,f937,f965,f970,f1007,f1011,f1025,f1030,f1050,f1055,f1116,f1120,f1134,f1138,f1200,f1205,f1226,f1231,f1239,f1245,f1266,f1270,f1288,f1310,f1349,f1353,f1363,f1373,f1441,f1445,f1459,f1463,f1478,f1483,f1508,f1513,f1540,f1544,f1560,f1565,f1591,f1595,f1645,f1649,f1659,f1663,f1667,f1671,f1675,f1679,f1683,f1687,f1691,f1695,f1699,f1701,f1716,f1720,f1722,f1725,f1757,f1762,f1809,f1813,f2213,f2217,f2221,f2225,f2229,f2233,f2237,f2241,f2244,f2249,f2251,f2266,f2270,f2272,f2326,f2339,f2344,f2348,f2352,f2356,f2360,f2364,f2368,f2376,f2380,f2384,f2388,f2392,f2396,f2401,f2406,f2414,f2418,f2422,f2426,f2430,f2435,f2439,f2440,f2445,f2449,f2453,f2457,f2461,f2465,f2469,f2474,f2479,f2484,f2489,f2497,f2501,f2505,f2509,f2518,f2527,f2532,f2537,f2541,f2544,f2558,f2562,f2578,f2582,f2598,f2602,f2610,f2611,f2619,f2620,f2641,f2645,f2649,f2651,f2655,f2659,f2674,f2678,f2680,f2689,f2694,f2695,f2717,f2732,f2736,f2740,f2757,f2762,f2781,f2787,f2793,f2799,f2802,f2803,f2860,f2864,f2868,f2872,f2876,f2880,f2884,f2888,f2892,f2896,f2900,f2904,f2908,f2912,f2916,f2920,f2924,f2929,f2933,f2941,f2945,f2949,f2953,f2957,f2961,f2966,f2971,f2976,f2981,f2985,f2989,f2994,f2999,f3003,f3007,f3012,f3017,f3069,f3073,f3078,f3083,f3087,f3091,f3095,f3099,f3103,f3108,f3113,f3118,f3123,f3127,f3131,f3140,f3149,f3153,f3157,f3162,f3167,f3169,f3173,f3178,f3190,f3194,f3204,f3208,f3257,f3261,f3266,f3281])).

fof(f3281,plain,
    ( ~ spl9_37
    | ~ spl9_197
    | ~ spl9_281
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_35
    | spl9_265 ),
    inference(avatar_split_clause,[],[f3280,f2663,f311,f457,f479,f2796,f2246,f319])).

fof(f319,plain,
    ( spl9_37
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f2246,plain,
    ( spl9_197
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_197])])).

fof(f2796,plain,
    ( spl9_281
  <=> m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_281])])).

fof(f479,plain,
    ( spl9_56
  <=> v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f457,plain,
    ( spl9_53
  <=> v1_funct_1(k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f311,plain,
    ( spl9_35
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f2663,plain,
    ( spl9_265
  <=> v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_265])])).

fof(f3280,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl9_265 ),
    inference(resolution,[],[f2665,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f2665,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | spl9_265 ),
    inference(avatar_component_clause,[],[f2663])).

fof(f3266,plain,
    ( spl9_3
    | ~ spl9_281
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | spl9_350
    | ~ spl9_297 ),
    inference(avatar_split_clause,[],[f3262,f2914,f3264,f118,f113,f153,f148,f143,f457,f479,f2796,f123])).

fof(f123,plain,
    ( spl9_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f143,plain,
    ( spl9_7
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f148,plain,
    ( spl9_8
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f153,plain,
    ( spl9_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f113,plain,
    ( spl9_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f118,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f3264,plain,
    ( spl9_350
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X0))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_350])])).

fof(f2914,plain,
    ( spl9_297
  <=> ! [X31] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),X31)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_297])])).

fof(f3262,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_297 ),
    inference(superposition,[],[f2915,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f2915,plain,
    ( ! [X31] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),X31))
    | ~ spl9_297 ),
    inference(avatar_component_clause,[],[f2914])).

fof(f3261,plain,
    ( spl9_3
    | ~ spl9_56
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_53
    | spl9_349
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f3244,f2796,f3259,f457,f118,f113,f153,f148,f143,f479,f123])).

fof(f3259,plain,
    ( spl9_349
  <=> ! [X16,X17] :
        ( ~ m1_subset_1(X16,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X17))
        | ~ m1_pre_topc(X17,sK0)
        | v1_xboole_0(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X17))
        | m1_subset_1(X16,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_349])])).

fof(f3244,plain,
    ( ! [X17,X16] :
        ( ~ m1_subset_1(X16,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X17))
        | m1_subset_1(X16,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | v1_xboole_0(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X17))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X17,sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_281 ),
    inference(resolution,[],[f1332,f2797])).

fof(f2797,plain,
    ( m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ spl9_281 ),
    inference(avatar_component_clause,[],[f2796])).

fof(f1332,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k2_tmap_1(X0,X1,X2,X3))
      | m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | v1_xboole_0(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1331])).

fof(f1331,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_tmap_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | v1_xboole_0(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f656,f88])).

fof(f656,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_partfun1(X1,X2,X0,X4))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(X3,k2_zfmisc_1(X1,X2))
      | v1_xboole_0(k2_partfun1(X1,X2,X0,X4))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f282,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f282,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ r2_hidden(X12,k2_partfun1(X10,X11,X9,X13))
      | ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | m1_subset_1(X12,k2_zfmisc_1(X10,X11)) ) ),
    inference(resolution,[],[f100,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f3257,plain,
    ( spl9_11
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_182
    | spl9_348
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f3242,f2186,f3255,f2182,f249,f221,f138,f133,f128,f2323,f163])).

fof(f163,plain,
    ( spl9_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f2323,plain,
    ( spl9_201
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_201])])).

fof(f128,plain,
    ( spl9_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f133,plain,
    ( spl9_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f138,plain,
    ( spl9_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f221,plain,
    ( spl9_22
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f249,plain,
    ( spl9_27
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f2182,plain,
    ( spl9_182
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f3255,plain,
    ( spl9_348
  <=> ! [X13,X12] :
        ( ~ m1_subset_1(X12,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | ~ m1_pre_topc(X13,sK3)
        | v1_xboole_0(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | m1_subset_1(X12,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_348])])).

fof(f2186,plain,
    ( spl9_183
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_183])])).

fof(f3242,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | m1_subset_1(X12,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | v1_xboole_0(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X13,sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_183 ),
    inference(resolution,[],[f1332,f2187])).

fof(f2187,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl9_183 ),
    inference(avatar_component_clause,[],[f2186])).

fof(f3208,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_347
    | ~ spl9_173 ),
    inference(avatar_split_clause,[],[f3199,f1689,f3206,f123,f118,f113])).

fof(f3206,plain,
    ( spl9_347
  <=> ! [X9,X11,X13,X7,X8,X10,X12] :
        ( v1_funct_1(k2_tmap_1(X7,sK1,k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5),X12))
        | ~ v2_pre_topc(X9)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK0))))
        | v2_struct_0(X9)
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ v1_funct_1(X10)
        | ~ m1_pre_topc(X7,X9)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X9)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5))
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(X12)
        | ~ v1_funct_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7))
        | ~ v1_funct_2(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_347])])).

fof(f1689,plain,
    ( spl9_173
  <=> ! [X96,X98,X93,X95,X97,X92,X94] :
        ( ~ v1_funct_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96))
        | ~ v1_funct_1(X95)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,u1_struct_0(sK0))))
        | ~ v1_funct_1(X96)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X93)))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),u1_struct_0(X92),u1_struct_0(sK0))
        | v1_funct_1(k2_tmap_1(X92,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5),X98))
        | ~ l1_struct_0(X98)
        | ~ l1_struct_0(X92)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X97)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_173])])).

fof(f3199,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( v1_funct_1(k2_tmap_1(X7,sK1,k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5),X12))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_2(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X7)
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5))
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK0))
        | v2_struct_0(X9)
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK0))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ v2_pre_topc(X9) )
    | ~ spl9_173 ),
    inference(duplicate_literal_removal,[],[f3196])).

fof(f3196,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( v1_funct_1(k2_tmap_1(X7,sK1,k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5),X12))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_2(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X7)
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),sK5))
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK0))))
        | v2_struct_0(X9)
        | ~ m1_subset_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK0))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK0),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7))
        | ~ v2_pre_topc(X9)
        | ~ v1_funct_2(k2_tmap_1(X9,sK0,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7)) )
    | ~ spl9_173 ),
    inference(superposition,[],[f1690,f1034])).

fof(f1034,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5) = k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
      | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3))
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_2(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) ) ),
    inference(duplicate_literal_removal,[],[f1031])).

fof(f1031,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
      | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5),u1_struct_0(X3),u1_struct_0(X2))
      | ~ v1_funct_1(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3))
      | k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5) = k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3)
      | ~ v1_funct_2(k2_tmap_1(X0,X2,k5_relat_1(X4,X5),X3),u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) ) ),
    inference(resolution,[],[f448,f356])).

fof(f356,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] :
      ( ~ r2_funct_2(X8,X9,X7,k1_partfun1(X8,X10,X11,X9,X12,X13))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_1(k1_partfun1(X8,X10,X11,X9,X12,X13))
      | ~ v1_funct_2(k1_partfun1(X8,X10,X11,X9,X12,X13),X8,X9)
      | ~ v1_funct_1(X7)
      | k1_partfun1(X8,X10,X11,X9,X12,X13) = X7
      | ~ v1_funct_2(X7,X8,X9)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X8,X10)))
      | ~ v1_funct_1(X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X9)))
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f102,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f448,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k2_tmap_1(X0,X2,k5_relat_1(X3,X4),X5),k1_partfun1(u1_struct_0(X5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X3,X5),X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k2_tmap_1(X0,X2,k5_relat_1(X3,X4),X5),k1_partfun1(u1_struct_0(X5),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X3,X5),X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f84,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                            & v1_funct_1(X5) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X3),k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X0,X1,X4,X3),X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tmap_1)).

fof(f1690,plain,
    ( ! [X94,X92,X97,X95,X93,X98,X96] :
        ( v1_funct_1(k2_tmap_1(X92,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5),X98))
        | ~ v1_funct_1(X95)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,u1_struct_0(sK0))))
        | ~ v1_funct_1(X96)
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X93)))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),u1_struct_0(X92),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96))
        | ~ l1_struct_0(X98)
        | ~ l1_struct_0(X92)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X97)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5)) )
    | ~ spl9_173 ),
    inference(avatar_component_clause,[],[f1689])).

fof(f3204,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_346
    | ~ spl9_173 ),
    inference(avatar_split_clause,[],[f3200,f1689,f3202,f123,f118,f113])).

fof(f3202,plain,
    ( spl9_346
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5),X5))
        | v2_struct_0(X2)
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X5)
        | ~ v1_funct_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_346])])).

fof(f3200,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5),X5))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0))
        | v2_struct_0(X2) )
    | ~ spl9_173 ),
    inference(duplicate_literal_removal,[],[f3195])).

fof(f3195,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5),X5))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),sK5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0))
        | v2_struct_0(X2) )
    | ~ spl9_173 ),
    inference(superposition,[],[f1690,f951])).

fof(f951,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5) = k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4)
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4))
      | ~ v1_funct_2(k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4),u1_struct_0(X5),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5),u1_struct_0(X5),u1_struct_0(X1))
      | ~ m1_subset_1(k2_tmap_1(X0,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X2,X3,X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f942])).

fof(f942,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X1))))
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4))
      | ~ v1_funct_2(k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4),u1_struct_0(X5),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5))
      | k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5) = k1_partfun1(u1_struct_0(X5),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X2,X3,X5),X4)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),X5),u1_struct_0(X5),u1_struct_0(X1))
      | ~ m1_subset_1(k2_tmap_1(X0,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X2,X3,X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X5,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f356,f84])).

fof(f3194,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_345
    | ~ spl9_172 ),
    inference(avatar_split_clause,[],[f3185,f1685,f3192,f138,f133,f128])).

fof(f3192,plain,
    ( spl9_345
  <=> ! [X9,X11,X13,X7,X8,X10,X12] :
        ( v1_funct_1(k2_tmap_1(X7,sK2,k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4),X12))
        | ~ v2_pre_topc(X9)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | v2_struct_0(X9)
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ v1_funct_1(X10)
        | ~ m1_pre_topc(X7,X9)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X8)
        | ~ v2_pre_topc(X8)
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X9)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4))
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(X12)
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_345])])).

fof(f1685,plain,
    ( spl9_172
  <=> ! [X84,X86,X89,X85,X87,X88,X90] :
        ( ~ v1_funct_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88))
        | ~ v1_funct_1(X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,u1_struct_0(sK1))))
        | ~ v1_funct_1(X88)
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X85)))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),u1_struct_0(X84),u1_struct_0(sK1))
        | v1_funct_1(k2_tmap_1(X84,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4),X90))
        | ~ l1_struct_0(X90)
        | ~ l1_struct_0(X84)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X89)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f3185,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( v1_funct_1(k2_tmap_1(X7,sK2,k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4),X12))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X7)
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4))
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK1))
        | v2_struct_0(X9)
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v2_pre_topc(X9) )
    | ~ spl9_172 ),
    inference(duplicate_literal_removal,[],[f3182])).

fof(f3182,plain,
    ( ! [X12,X10,X8,X7,X13,X11,X9] :
        ( v1_funct_1(k2_tmap_1(X7,sK2,k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4),X12))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7))
        | ~ l1_struct_0(X12)
        | ~ l1_struct_0(X7)
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),X13)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),sK4))
        | ~ l1_pre_topc(X9)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,X9)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X8),u1_struct_0(sK1))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))))
        | v2_struct_0(X9)
        | ~ m1_subset_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X8),u1_struct_0(X8),u1_struct_0(sK1),k2_tmap_1(X9,X8,X10,X7),X11),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7))
        | ~ v2_pre_topc(X9)
        | ~ v1_funct_2(k2_tmap_1(X9,sK1,k5_relat_1(X10,X11),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X9,X8,X10,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | ~ v1_funct_1(k2_tmap_1(X9,X8,X10,X7)) )
    | ~ spl9_172 ),
    inference(superposition,[],[f1686,f1034])).

fof(f1686,plain,
    ( ! [X90,X88,X87,X85,X89,X86,X84] :
        ( v1_funct_1(k2_tmap_1(X84,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4),X90))
        | ~ v1_funct_1(X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,u1_struct_0(sK1))))
        | ~ v1_funct_1(X88)
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X85)))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),u1_struct_0(X84),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88))
        | ~ l1_struct_0(X90)
        | ~ l1_struct_0(X84)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X89)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4)) )
    | ~ spl9_172 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f3190,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_344
    | ~ spl9_172 ),
    inference(avatar_split_clause,[],[f3186,f1685,f3188,f138,f133,f128])).

fof(f3188,plain,
    ( spl9_344
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4),X5))
        | v2_struct_0(X2)
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4))
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X5)
        | ~ v1_funct_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0))
        | ~ v1_funct_2(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_344])])).

fof(f3186,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4),X5))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK1))
        | v2_struct_0(X2) )
    | ~ spl9_172 ),
    inference(duplicate_literal_removal,[],[f3181])).

fof(f3181,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4),X5))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),sK4))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X2,X1,X3,X0),X4),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0))
        | ~ m1_subset_1(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X2,sK1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X3,X4),X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK1))
        | v2_struct_0(X2) )
    | ~ spl9_172 ),
    inference(superposition,[],[f1686,f951])).

fof(f3178,plain,
    ( ~ spl9_197
    | ~ spl9_163
    | spl9_266 ),
    inference(avatar_split_clause,[],[f3177,f2667,f1651,f2246])).

fof(f1651,plain,
    ( spl9_163
  <=> ! [X50] :
        ( ~ l1_struct_0(X50)
        | v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X50)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_163])])).

fof(f2667,plain,
    ( spl9_266
  <=> v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_266])])).

fof(f3177,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl9_163
    | spl9_266 ),
    inference(resolution,[],[f2669,f1652])).

fof(f1652,plain,
    ( ! [X50] :
        ( v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X50))
        | ~ l1_struct_0(X50) )
    | ~ spl9_163 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f2669,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | spl9_266 ),
    inference(avatar_component_clause,[],[f2667])).

fof(f3173,plain,
    ( ~ spl9_20
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_266
    | spl9_186 ),
    inference(avatar_split_clause,[],[f3170,f2198,f2667,f198,f178,f168,f208])).

fof(f208,plain,
    ( spl9_20
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f168,plain,
    ( spl9_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f178,plain,
    ( spl9_14
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f198,plain,
    ( spl9_18
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f2198,plain,
    ( spl9_186
  <=> v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f3170,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | spl9_186 ),
    inference(superposition,[],[f2200,f83])).

fof(f2200,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | spl9_186 ),
    inference(avatar_component_clause,[],[f2198])).

fof(f3169,plain,
    ( spl9_9
    | ~ spl9_35
    | ~ spl9_302 ),
    inference(avatar_split_clause,[],[f3168,f2935,f311,f153])).

fof(f2935,plain,
    ( spl9_302
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_302])])).

fof(f3168,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_302 ),
    inference(resolution,[],[f2937,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f2937,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_302 ),
    inference(avatar_component_clause,[],[f2935])).

fof(f3167,plain,
    ( ~ spl9_338
    | ~ spl9_186
    | spl9_343
    | ~ spl9_155
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3061,f2194,f1542,f3164,f2198,f3142])).

fof(f3142,plain,
    ( spl9_338
  <=> v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_338])])).

fof(f3164,plain,
    ( spl9_343
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_343])])).

fof(f1542,plain,
    ( spl9_155
  <=> ! [X3,X5,X4] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(sK5,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_155])])).

fof(f2194,plain,
    ( spl9_185
  <=> m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_185])])).

fof(f3061,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
    | ~ spl9_155
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1543])).

fof(f1543,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,X3)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(sK5,X3)) )
    | ~ spl9_155 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f2195,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ spl9_185 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f3162,plain,
    ( ~ spl9_336
    | ~ spl9_186
    | spl9_342
    | ~ spl9_154
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3060,f2194,f1538,f3159,f2198,f3133])).

fof(f3133,plain,
    ( spl9_336
  <=> v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_336])])).

fof(f3159,plain,
    ( spl9_342
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_342])])).

fof(f1538,plain,
    ( spl9_154
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f3060,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
    | ~ spl9_154
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1539])).

fof(f1539,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(sK4,X0)) )
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f3157,plain,
    ( ~ spl9_186
    | spl9_341
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3059,f2194,f3155,f2198])).

fof(f3155,plain,
    ( spl9_341
  <=> ! [X75,X77,X76,X78] :
        ( ~ m1_subset_1(X75,k5_relat_1(X76,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | v1_xboole_0(k5_relat_1(X76,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | m1_subset_1(X75,k2_zfmisc_1(X77,u1_struct_0(sK2)))
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))
        | ~ v1_funct_1(X76) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_341])])).

fof(f3059,plain,
    ( ! [X78,X76,X77,X75] :
        ( ~ m1_subset_1(X75,k5_relat_1(X76,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X76)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))
        | m1_subset_1(X75,k2_zfmisc_1(X77,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X76,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1523])).

fof(f1523,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X6,k5_relat_1(X4,X5))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(X6,k2_zfmisc_1(X0,X3))
      | v1_xboole_0(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f1522])).

fof(f1522,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(X6,k2_zfmisc_1(X0,X3))
      | v1_xboole_0(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f734,f83])).

fof(f734,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k1_partfun1(X4,X5,X1,X2,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(X6,k2_zfmisc_1(X4,X2))
      | v1_xboole_0(k1_partfun1(X4,X5,X1,X2,X3,X0))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f294,f94])).

fof(f294,plain,(
    ! [X14,X19,X17,X15,X13,X18,X16] :
      ( ~ r2_hidden(X19,k1_partfun1(X14,X15,X17,X18,X13,X16))
      | ~ v1_funct_1(X16)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | m1_subset_1(X19,k2_zfmisc_1(X14,X18)) ) ),
    inference(resolution,[],[f82,f93])).

fof(f3153,plain,
    ( ~ spl9_186
    | spl9_340
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3058,f2194,f3151,f2198])).

fof(f3151,plain,
    ( spl9_340
  <=> ! [X73,X71,X72,X74] :
        ( ~ m1_subset_1(X71,k5_relat_1(X72,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | v1_xboole_0(k5_relat_1(X72,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(X73,u1_struct_0(sK2)))
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
        | ~ v1_funct_1(X72) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_340])])).

fof(f3058,plain,
    ( ! [X74,X72,X71,X73] :
        ( ~ m1_subset_1(X71,k5_relat_1(X72,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X72)
        | ~ m1_subset_1(X72,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
        | ~ v1_xboole_0(k2_zfmisc_1(X73,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X72,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1518])).

fof(f1518,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X6,k5_relat_1(X4,X5))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X3))
      | v1_xboole_0(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f1517])).

fof(f1517,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k5_relat_1(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X3))
      | v1_xboole_0(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f731,f83])).

fof(f731,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k1_partfun1(X4,X5,X1,X2,X3,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_xboole_0(k2_zfmisc_1(X4,X2))
      | v1_xboole_0(k1_partfun1(X4,X5,X1,X2,X3,X0))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f295,f94])).

fof(f295,plain,(
    ! [X26,X24,X23,X21,X25,X22,X20] :
      ( ~ r2_hidden(X26,k1_partfun1(X21,X22,X24,X25,X20,X23))
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ v1_xboole_0(k2_zfmisc_1(X21,X25)) ) ),
    inference(resolution,[],[f82,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f3149,plain,
    ( ~ spl9_338
    | ~ spl9_186
    | spl9_339
    | ~ spl9_149
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3057,f2194,f1461,f3146,f2198,f3142])).

fof(f3146,plain,
    ( spl9_339
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_339])])).

fof(f1461,plain,
    ( spl9_149
  <=> ! [X3,X5,X4] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,X3)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(sK5,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f3057,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
    | ~ spl9_149
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1462])).

fof(f1462,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,X3)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(sK5,X3)) )
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f1461])).

fof(f3140,plain,
    ( ~ spl9_336
    | ~ spl9_186
    | spl9_337
    | ~ spl9_148
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3056,f2194,f1457,f3137,f2198,f3133])).

fof(f3137,plain,
    ( spl9_337
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).

fof(f1457,plain,
    ( spl9_148
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_148])])).

fof(f3056,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
    | ~ spl9_148
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1458])).

fof(f1458,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(sK4,X0)) )
    | ~ spl9_148 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f3131,plain,
    ( ~ spl9_186
    | spl9_335
    | ~ spl9_147
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3055,f2194,f1443,f3129,f2198])).

fof(f3129,plain,
    ( spl9_335
  <=> ! [X69,X68,X70] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X68)))
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X68)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_335])])).

fof(f1443,plain,
    ( spl9_147
  <=> ! [X9,X11,X7,X8,X10,X6] :
        ( ~ v1_funct_1(X6)
        | v1_funct_1(k5_relat_1(sK5,k5_relat_1(X9,X6)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_1(k5_relat_1(X9,X6))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f3055,plain,
    ( ! [X70,X68,X69] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X68)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X68))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
    | ~ spl9_147
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1444])).

fof(f1444,plain,
    ( ! [X6,X10,X8,X7,X11,X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | v1_funct_1(k5_relat_1(sK5,k5_relat_1(X9,X6)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_1(k5_relat_1(X9,X6))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
    | ~ spl9_147 ),
    inference(avatar_component_clause,[],[f1443])).

fof(f3127,plain,
    ( ~ spl9_186
    | spl9_334
    | ~ spl9_146
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3054,f2194,f1439,f3125,f2198])).

fof(f3125,plain,
    ( spl9_334
  <=> ! [X65,X67,X66] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X65)))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X65)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_334])])).

fof(f1439,plain,
    ( spl9_146
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X3,X0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f3054,plain,
    ( ! [X66,X67,X65] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X65)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X65))
        | ~ v1_funct_1(X65)
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
    | ~ spl9_146
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1440])).

fof(f1440,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X3,X0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl9_146 ),
    inference(avatar_component_clause,[],[f1439])).

fof(f3123,plain,
    ( spl9_333
    | ~ spl9_324
    | ~ spl9_186
    | ~ spl9_111
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3051,f2194,f1009,f2198,f3080,f3120])).

fof(f3120,plain,
    ( spl9_333
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_333])])).

fof(f3080,plain,
    ( spl9_324
  <=> v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_324])])).

fof(f1009,plain,
    ( spl9_111
  <=> ! [X3,X5,X4] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK5))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f3051,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5))
    | v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5),sK5))
    | ~ spl9_111
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1010])).

fof(f1010,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK5)) )
    | ~ spl9_111 ),
    inference(avatar_component_clause,[],[f1009])).

fof(f3118,plain,
    ( spl9_332
    | ~ spl9_323
    | ~ spl9_186
    | ~ spl9_110
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3050,f2194,f1005,f2198,f3075,f3115])).

fof(f3115,plain,
    ( spl9_332
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_332])])).

fof(f3075,plain,
    ( spl9_323
  <=> v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_323])])).

fof(f1005,plain,
    ( spl9_110
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK5))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f3050,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4))
    | v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4),sK5))
    | ~ spl9_110
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f1006])).

fof(f1006,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK5)) )
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f3113,plain,
    ( ~ spl9_186
    | ~ spl9_324
    | spl9_331
    | ~ spl9_105
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3049,f2194,f914,f3110,f3080,f2198])).

fof(f3110,plain,
    ( spl9_331
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_331])])).

fof(f914,plain,
    ( spl9_105
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK4))
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | ~ v1_funct_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f3049,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5),sK4))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ spl9_105
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f915])).

fof(f915,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK4))
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | ~ v1_funct_1(X3) )
    | ~ spl9_105 ),
    inference(avatar_component_clause,[],[f914])).

fof(f3108,plain,
    ( ~ spl9_186
    | ~ spl9_323
    | spl9_330
    | ~ spl9_104
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3048,f2194,f910,f3105,f3075,f2198])).

fof(f3105,plain,
    ( spl9_330
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_330])])).

fof(f910,plain,
    ( spl9_104
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK4))
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f3048,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ spl9_104
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f911])).

fof(f911,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK4))
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) )
    | ~ spl9_104 ),
    inference(avatar_component_clause,[],[f910])).

fof(f3103,plain,
    ( ~ spl9_186
    | spl9_329
    | ~ spl9_85
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3047,f2194,f671,f3101,f2198])).

fof(f3101,plain,
    ( spl9_329
  <=> ! [X60,X62,X61] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X60,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)),sK5))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_1(k5_relat_1(X60,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_329])])).

fof(f671,plain,
    ( spl9_85
  <=> ! [X3,X5,X4] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | v1_funct_1(k5_relat_1(X3,sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f3047,plain,
    ( ! [X61,X62,X60] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X60,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)),sK5))
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ v1_funct_1(k5_relat_1(X60,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X60) )
    | ~ spl9_85
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f718])).

fof(f718,plain,
    ( ! [X14,X19,X17,X15,X18,X16] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X14,X15),sK5))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_1(k5_relat_1(X14,X15))
        | ~ v1_funct_1(X14) )
    | ~ spl9_85 ),
    inference(resolution,[],[f672,f297])).

fof(f297,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f82,f83])).

fof(f672,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | v1_funct_1(k5_relat_1(X3,sK5)) )
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f671])).

fof(f3099,plain,
    ( spl9_328
    | ~ spl9_186
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3046,f2194,f2198,f3097])).

fof(f3097,plain,
    ( spl9_328
  <=> ! [X56,X58,X57,X59] :
        ( ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_xboole_0(k2_zfmisc_1(X57,u1_struct_0(sK2)))
        | ~ r2_hidden(X59,k5_relat_1(X56,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X56) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_328])])).

fof(f3046,plain,
    ( ! [X59,X57,X58,X56] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_funct_1(X56)
        | ~ r2_hidden(X59,k5_relat_1(X56,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(X57,u1_struct_0(sK2))) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f712])).

fof(f712,plain,(
    ! [X142,X140,X138,X143,X141,X139,X137] :
      ( ~ m1_subset_1(X140,k1_zfmisc_1(k2_zfmisc_1(X141,X142)))
      | ~ v1_funct_1(X140)
      | ~ m1_subset_1(X137,k1_zfmisc_1(k2_zfmisc_1(X138,X139)))
      | ~ v1_funct_1(X137)
      | ~ r2_hidden(X143,k5_relat_1(X137,X140))
      | ~ v1_xboole_0(k2_zfmisc_1(X138,X142)) ) ),
    inference(resolution,[],[f297,f92])).

fof(f3095,plain,
    ( spl9_327
    | ~ spl9_186
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3045,f2194,f2198,f3093])).

fof(f3093,plain,
    ( spl9_327
  <=> ! [X53,X55,X52,X54] :
        ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | m1_subset_1(X55,k2_zfmisc_1(X53,u1_struct_0(sK2)))
        | ~ r2_hidden(X55,k5_relat_1(X52,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X52) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_327])])).

fof(f3045,plain,
    ( ! [X54,X52,X55,X53] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X52)
        | ~ r2_hidden(X55,k5_relat_1(X52,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | m1_subset_1(X55,k2_zfmisc_1(X53,u1_struct_0(sK2))) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f711])).

fof(f711,plain,(
    ! [X134,X132,X130,X136,X135,X133,X131] :
      ( ~ m1_subset_1(X133,k1_zfmisc_1(k2_zfmisc_1(X134,X135)))
      | ~ v1_funct_1(X133)
      | ~ m1_subset_1(X130,k1_zfmisc_1(k2_zfmisc_1(X131,X132)))
      | ~ v1_funct_1(X130)
      | ~ r2_hidden(X136,k5_relat_1(X130,X133))
      | m1_subset_1(X136,k2_zfmisc_1(X131,X135)) ) ),
    inference(resolution,[],[f297,f93])).

fof(f3091,plain,
    ( spl9_326
    | ~ spl9_186
    | ~ spl9_84
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3044,f2194,f667,f2198,f3089])).

fof(f3089,plain,
    ( spl9_326
  <=> ! [X49,X51,X50] :
        ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X49,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)),sK4))
        | ~ v1_funct_1(k5_relat_1(X49,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_326])])).

fof(f667,plain,
    ( spl9_84
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(X0,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f3044,plain,
    ( ! [X50,X51,X49] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_1(k5_relat_1(X49,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X49,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)),sK4)) )
    | ~ spl9_84
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f697])).

fof(f697,plain,
    ( ! [X57,X54,X52,X56,X55,X53] :
        ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X55)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_1(k5_relat_1(X52,X55))
        | v1_funct_1(k5_relat_1(k5_relat_1(X52,X55),sK4)) )
    | ~ spl9_84 ),
    inference(resolution,[],[f297,f668])).

fof(f668,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(X0,sK4)) )
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f667])).

fof(f3087,plain,
    ( ~ spl9_186
    | spl9_325
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3043,f2194,f3085,f2198])).

fof(f3085,plain,
    ( spl9_325
  <=> ! [X44,X46,X48,X43,X45,X47] :
        ( ~ v1_funct_1(X43)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k5_relat_1(X46,X43)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_1(k5_relat_1(X46,X43))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_325])])).

fof(f3043,plain,
    ( ! [X47,X45,X43,X48,X46,X44] :
        ( ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
        | ~ v1_funct_1(k5_relat_1(X46,X43))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k5_relat_1(X46,X43)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f696])).

fof(f696,plain,(
    ! [X47,X45,X43,X50,X48,X46,X44,X51,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | ~ v1_funct_1(k5_relat_1(X43,X46))
      | v1_funct_1(k5_relat_1(X49,k5_relat_1(X43,X46)))
      | ~ v1_funct_1(X49) ) ),
    inference(resolution,[],[f297,f286])).

fof(f286,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | v1_funct_1(k5_relat_1(X4,X5))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k5_relat_1(X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f81,f83])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3083,plain,
    ( spl9_324
    | ~ spl9_186
    | ~ spl9_85
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3041,f2194,f671,f2198,f3080])).

fof(f3041,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK5))
    | ~ spl9_85
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f672])).

fof(f3078,plain,
    ( spl9_323
    | ~ spl9_186
    | ~ spl9_84
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3040,f2194,f667,f2198,f3075])).

fof(f3040,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK4))
    | ~ spl9_84
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f668])).

fof(f3073,plain,
    ( ~ spl9_186
    | spl9_322
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3039,f2194,f3071,f2198])).

fof(f3071,plain,
    ( spl9_322
  <=> ! [X36,X35,X37] :
        ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v1_funct_1(X35)
        | v1_funct_1(k5_relat_1(X35,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).

fof(f3039,plain,
    ( ! [X37,X35,X36] :
        ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | v1_funct_1(k5_relat_1(X35,k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3)))
        | ~ v1_funct_1(X35) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f286])).

fof(f3069,plain,
    ( spl9_321
    | ~ spl9_186
    | ~ spl9_185 ),
    inference(avatar_split_clause,[],[f3035,f2194,f2198,f3067])).

fof(f3067,plain,
    ( spl9_321
  <=> ! [X32] : v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X32)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_321])])).

fof(f3035,plain,
    ( ! [X32] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
        | v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),X32)) )
    | ~ spl9_185 ),
    inference(resolution,[],[f2195,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3017,plain,
    ( ~ spl9_178
    | ~ spl9_53
    | spl9_320
    | ~ spl9_155
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2850,f2796,f1542,f3014,f457,f1754])).

fof(f1754,plain,
    ( spl9_178
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_178])])).

fof(f3014,plain,
    ( spl9_320
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k5_relat_1(sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_320])])).

fof(f2850,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k5_relat_1(sK5,sK4))))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK4)))
    | ~ spl9_155
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1543])).

fof(f3012,plain,
    ( ~ spl9_152
    | ~ spl9_53
    | spl9_319
    | ~ spl9_154
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2849,f2796,f1538,f3009,f457,f1505])).

fof(f1505,plain,
    ( spl9_152
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_152])])).

fof(f3009,plain,
    ( spl9_319
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k5_relat_1(sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).

fof(f2849,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k5_relat_1(sK5,sK4))))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK4)))
    | ~ spl9_154
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1539])).

fof(f3007,plain,
    ( ~ spl9_53
    | spl9_318
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2848,f2796,f3005,f457])).

fof(f3005,plain,
    ( spl9_318
  <=> ! [X75,X77,X74,X76] :
        ( ~ m1_subset_1(X74,k5_relat_1(X75,k5_relat_1(sK5,sK4)))
        | v1_xboole_0(k5_relat_1(X75,k5_relat_1(sK5,sK4)))
        | m1_subset_1(X74,k2_zfmisc_1(X76,u1_struct_0(sK2)))
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
        | ~ v1_funct_1(X75) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_318])])).

fof(f2848,plain,
    ( ! [X76,X74,X77,X75] :
        ( ~ m1_subset_1(X74,k5_relat_1(X75,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X76,X77)))
        | m1_subset_1(X74,k2_zfmisc_1(X76,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X75,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1523])).

fof(f3003,plain,
    ( ~ spl9_53
    | spl9_317
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2847,f2796,f3001,f457])).

fof(f3001,plain,
    ( spl9_317
  <=> ! [X73,X71,X72,X70] :
        ( ~ m1_subset_1(X70,k5_relat_1(X71,k5_relat_1(sK5,sK4)))
        | v1_xboole_0(k5_relat_1(X71,k5_relat_1(sK5,sK4)))
        | ~ v1_xboole_0(k2_zfmisc_1(X72,u1_struct_0(sK2)))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
        | ~ v1_funct_1(X71) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_317])])).

fof(f2847,plain,
    ( ! [X70,X72,X71,X73] :
        ( ~ m1_subset_1(X70,k5_relat_1(X71,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
        | ~ v1_xboole_0(k2_zfmisc_1(X72,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X71,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1518])).

fof(f2999,plain,
    ( ~ spl9_178
    | ~ spl9_53
    | spl9_316
    | ~ spl9_149
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2846,f2796,f1461,f2996,f457,f1754])).

fof(f2996,plain,
    ( spl9_316
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k5_relat_1(sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_316])])).

fof(f2846,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k5_relat_1(sK5,sK4))))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK4)))
    | ~ spl9_149
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1462])).

fof(f2994,plain,
    ( ~ spl9_152
    | ~ spl9_53
    | spl9_315
    | ~ spl9_148
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2845,f2796,f1457,f2991,f457,f1505])).

fof(f2991,plain,
    ( spl9_315
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k5_relat_1(sK5,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f2845,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k5_relat_1(sK5,sK4))))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK4)))
    | ~ spl9_148
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1458])).

fof(f2989,plain,
    ( ~ spl9_53
    | spl9_314
    | ~ spl9_147
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2844,f2796,f1443,f2987,f457])).

fof(f2987,plain,
    ( spl9_314
  <=> ! [X67,X69,X68] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k5_relat_1(sK5,sK4),X67)))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),X67)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_314])])).

fof(f2844,plain,
    ( ! [X68,X69,X67] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k5_relat_1(sK5,sK4),X67)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),X67))
        | ~ v1_funct_1(X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
    | ~ spl9_147
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1444])).

fof(f2985,plain,
    ( ~ spl9_53
    | spl9_313
    | ~ spl9_146
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2843,f2796,f1439,f2983,f457])).

fof(f2983,plain,
    ( spl9_313
  <=> ! [X65,X64,X66] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k5_relat_1(sK5,sK4),X64)))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
        | ~ v1_funct_1(X64)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),X64)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_313])])).

fof(f2843,plain,
    ( ! [X66,X64,X65] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k5_relat_1(sK5,sK4),X64)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),X64))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X65,X66))) )
    | ~ spl9_146
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1440])).

fof(f2981,plain,
    ( spl9_312
    | ~ spl9_113
    | ~ spl9_53
    | ~ spl9_111
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2840,f2796,f1009,f457,f1027,f2978])).

fof(f2978,plain,
    ( spl9_312
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_312])])).

fof(f1027,plain,
    ( spl9_113
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f2840,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5))
    | v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5),sK5))
    | ~ spl9_111
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1010])).

fof(f2976,plain,
    ( spl9_311
    | ~ spl9_107
    | ~ spl9_53
    | ~ spl9_110
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2839,f2796,f1005,f457,f934,f2973])).

fof(f2973,plain,
    ( spl9_311
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_311])])).

fof(f934,plain,
    ( spl9_107
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f2839,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4))
    | v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4),sK5))
    | ~ spl9_110
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f1006])).

fof(f2971,plain,
    ( ~ spl9_53
    | ~ spl9_113
    | spl9_310
    | ~ spl9_105
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2838,f2796,f914,f2968,f1027,f457])).

fof(f2968,plain,
    ( spl9_310
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_310])])).

fof(f2838,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5),sK4))
    | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ spl9_105
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f915])).

fof(f2966,plain,
    ( ~ spl9_53
    | ~ spl9_107
    | spl9_309
    | ~ spl9_104
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2837,f2796,f910,f2963,f934,f457])).

fof(f2963,plain,
    ( spl9_309
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_309])])).

fof(f2837,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ spl9_104
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f911])).

fof(f2961,plain,
    ( ~ spl9_53
    | spl9_308
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2836,f2796,f671,f2959,f457])).

fof(f2959,plain,
    ( spl9_308
  <=> ! [X60,X59,X61] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X59,k5_relat_1(sK5,sK4)),sK5))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_1(k5_relat_1(X59,k5_relat_1(sK5,sK4)))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_308])])).

fof(f2836,plain,
    ( ! [X61,X59,X60] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X59,k5_relat_1(sK5,sK4)),sK5))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_1(k5_relat_1(X59,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X59) )
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f718])).

fof(f2957,plain,
    ( spl9_307
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2835,f2796,f457,f2955])).

fof(f2955,plain,
    ( spl9_307
  <=> ! [X55,X56,X58,X57] :
        ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_xboole_0(k2_zfmisc_1(X56,u1_struct_0(sK2)))
        | ~ r2_hidden(X58,k5_relat_1(X55,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X55) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_307])])).

fof(f2835,plain,
    ( ! [X57,X58,X56,X55] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ v1_funct_1(X55)
        | ~ r2_hidden(X58,k5_relat_1(X55,k5_relat_1(sK5,sK4)))
        | ~ v1_xboole_0(k2_zfmisc_1(X56,u1_struct_0(sK2))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f712])).

fof(f2953,plain,
    ( spl9_306
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2834,f2796,f457,f2951])).

fof(f2951,plain,
    ( spl9_306
  <=> ! [X51,X53,X52,X54] :
        ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | m1_subset_1(X54,k2_zfmisc_1(X52,u1_struct_0(sK2)))
        | ~ r2_hidden(X54,k5_relat_1(X51,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X51) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_306])])).

fof(f2834,plain,
    ( ! [X54,X52,X53,X51] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ v1_funct_1(X51)
        | ~ r2_hidden(X54,k5_relat_1(X51,k5_relat_1(sK5,sK4)))
        | m1_subset_1(X54,k2_zfmisc_1(X52,u1_struct_0(sK2))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f711])).

fof(f2949,plain,
    ( spl9_305
    | ~ spl9_53
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2833,f2796,f667,f457,f2947])).

fof(f2947,plain,
    ( spl9_305
  <=> ! [X49,X48,X50] :
        ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X48,k5_relat_1(sK5,sK4)),sK4))
        | ~ v1_funct_1(k5_relat_1(X48,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X48) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_305])])).

fof(f2833,plain,
    ( ! [X50,X48,X49] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_1(k5_relat_1(X48,k5_relat_1(sK5,sK4)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X48,k5_relat_1(sK5,sK4)),sK4)) )
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f697])).

fof(f2945,plain,
    ( ~ spl9_53
    | spl9_304
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2832,f2796,f2943,f457])).

fof(f2943,plain,
    ( spl9_304
  <=> ! [X42,X44,X46,X43,X45,X47] :
        ( ~ v1_funct_1(X42)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),k5_relat_1(X45,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_1(k5_relat_1(X45,X42))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_304])])).

fof(f2832,plain,
    ( ! [X47,X45,X43,X46,X44,X42] :
        ( ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
        | ~ v1_funct_1(k5_relat_1(X45,X42))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),k5_relat_1(X45,X42)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f696])).

fof(f2941,plain,
    ( spl9_302
    | ~ spl9_56
    | ~ spl9_53
    | spl9_303
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2831,f2796,f2939,f457,f479,f2935])).

fof(f2939,plain,
    ( spl9_303
  <=> ! [X40,X38,X41,X37,X39] :
        ( ~ v1_funct_1(X37)
        | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),k5_relat_1(X40,X37)))
        | ~ v1_funct_2(k5_relat_1(X40,X37),u1_struct_0(sK2),X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_1(k5_relat_1(X40,X37))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X41)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_303])])).

fof(f2831,plain,
    ( ! [X39,X37,X41,X38,X40] :
        ( ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X41)))
        | ~ v1_funct_1(k5_relat_1(X40,X37))
        | ~ v1_funct_2(k5_relat_1(X40,X37),u1_struct_0(sK2),X39)
        | v1_xboole_0(u1_struct_0(sK2))
        | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),k5_relat_1(X40,X37))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f690])).

fof(f690,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,X7,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(k5_relat_1(X0,X3))
      | ~ v1_funct_2(k5_relat_1(X0,X3),X1,X5)
      | v1_xboole_0(X1)
      | v1_funct_1(k5_relat_1(X6,k5_relat_1(X0,X3))) ) ),
    inference(resolution,[],[f297,f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | v1_xboole_0(X1)
      | v1_funct_1(k5_relat_1(X3,X4)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X4,X1,X2)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X1) )
     => ( v1_funct_2(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(f2933,plain,
    ( ~ spl9_53
    | spl9_301
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2828,f2796,f2931,f457])).

fof(f2931,plain,
    ( spl9_301
  <=> ! [X34,X36,X35] :
        ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X34)
        | v1_funct_1(k5_relat_1(X34,k5_relat_1(sK5,sK4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_301])])).

fof(f2828,plain,
    ( ! [X35,X36,X34] :
        ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | v1_funct_1(k5_relat_1(X34,k5_relat_1(sK5,sK4)))
        | ~ v1_funct_1(X34) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f286])).

fof(f2929,plain,
    ( spl9_300
    | ~ spl9_53
    | ~ spl9_56
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2827,f2796,f479,f457,f2926])).

fof(f2926,plain,
    ( spl9_300
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_300])])).

fof(f2827,plain,
    ( ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),k5_relat_1(sK5,sK4))
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2924,plain,
    ( ~ spl9_56
    | ~ spl9_53
    | spl9_299
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2826,f2796,f2922,f457,f479])).

fof(f2922,plain,
    ( spl9_299
  <=> ! [X33] :
        ( ~ v1_funct_2(X33,u1_struct_0(sK0),u1_struct_0(sK2))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),X33)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),X33,k5_relat_1(sK5,sK4))
        | ~ v1_funct_1(X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).

fof(f2826,plain,
    ( ! [X33] :
        ( ~ v1_funct_2(X33,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(X33)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),X33,k5_relat_1(sK5,sK4))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),X33) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | r2_funct_2(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X3,X2)
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
       => r2_funct_2(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r2_funct_2)).

fof(f2920,plain,
    ( ~ spl9_56
    | ~ spl9_53
    | spl9_298
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2825,f2796,f2918,f457,f479])).

fof(f2918,plain,
    ( spl9_298
  <=> ! [X32] :
        ( ~ v1_funct_2(X32,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),X32,k5_relat_1(sK5,sK4))
        | k5_relat_1(sK5,sK4) = X32
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_298])])).

fof(f2825,plain,
    ( ! [X32] :
        ( ~ v1_funct_2(X32,u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(X32)
        | k5_relat_1(sK5,sK4) = X32
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK2),X32,k5_relat_1(sK5,sK4)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f102])).

fof(f2916,plain,
    ( spl9_297
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2824,f2796,f457,f2914])).

fof(f2824,plain,
    ( ! [X31] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK2),k5_relat_1(sK5,sK4),X31)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f99])).

fof(f2912,plain,
    ( spl9_40
    | ~ spl9_56
    | ~ spl9_53
    | spl9_296
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2823,f2796,f2910,f457,f479,f339])).

fof(f339,plain,
    ( spl9_40
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f2910,plain,
    ( spl9_296
  <=> ! [X29,X30] :
        ( ~ v1_funct_1(X29)
        | v1_funct_2(k5_relat_1(X29,k5_relat_1(sK5,sK4)),X30,u1_struct_0(sK2))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X30,u1_struct_0(sK0))))
        | ~ v1_funct_2(X29,X30,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_296])])).

fof(f2823,plain,
    ( ! [X30,X29] :
        ( ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X30,u1_struct_0(sK0))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X30,u1_struct_0(sK0))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_2(k5_relat_1(X29,k5_relat_1(sK5,sK4)),X30,u1_struct_0(sK2)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | v1_xboole_0(X1)
      | v1_funct_2(k5_relat_1(X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2908,plain,
    ( spl9_40
    | ~ spl9_56
    | ~ spl9_53
    | spl9_295
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2822,f2796,f2906,f457,f479,f339])).

fof(f2906,plain,
    ( spl9_295
  <=> ! [X27,X28] :
        ( ~ v1_funct_1(X27)
        | v1_funct_1(k5_relat_1(X27,k5_relat_1(sK5,sK4)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,u1_struct_0(sK0))))
        | ~ v1_funct_2(X27,X28,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_295])])).

fof(f2822,plain,
    ( ! [X28,X27] :
        ( ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X28,u1_struct_0(sK0))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,u1_struct_0(sK0))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_1(k5_relat_1(X27,k5_relat_1(sK5,sK4))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f97])).

fof(f2904,plain,
    ( spl9_3
    | spl9_294
    | ~ spl9_56
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_53
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2821,f2796,f671,f457,f118,f113,f153,f148,f143,f479,f2902,f123])).

fof(f2902,plain,
    ( spl9_294
  <=> ! [X26] :
        ( ~ m1_pre_topc(X26,sK0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X26),sK5))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X26)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_294])])).

fof(f2821,plain,
    ( ! [X26] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X26,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X26))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X26),sK5)) )
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f815])).

fof(f815,plain,
    ( ! [X103,X101,X102,X100] :
        ( ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X101),u1_struct_0(X102))))
        | ~ v1_funct_1(X100)
        | ~ v2_pre_topc(X101)
        | ~ l1_pre_topc(X101)
        | v2_struct_0(X102)
        | ~ v2_pre_topc(X102)
        | ~ l1_pre_topc(X102)
        | ~ v1_funct_2(X100,u1_struct_0(X101),u1_struct_0(X102))
        | ~ m1_pre_topc(X103,X101)
        | v2_struct_0(X101)
        | ~ v1_funct_1(k2_tmap_1(X101,X102,X100,X103))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X101,X102,X100,X103),sK5)) )
    | ~ spl9_85 ),
    inference(resolution,[],[f400,f672])).

fof(f400,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k2_tmap_1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X5,X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f399])).

fof(f399,plain,(
    ! [X4,X2,X5,X3] :
      ( m1_subset_1(k2_tmap_1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ m1_pre_topc(X5,X2)
      | v2_struct_0(X2) ) ),
    inference(superposition,[],[f100,f88])).

fof(f2900,plain,
    ( spl9_3
    | spl9_293
    | ~ spl9_56
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_53
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2820,f2796,f667,f457,f118,f113,f153,f148,f143,f479,f2898,f123])).

fof(f2898,plain,
    ( spl9_293
  <=> ! [X25] :
        ( ~ m1_pre_topc(X25,sK0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X25),sK4))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).

fof(f2820,plain,
    ( ! [X25] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X25,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X25))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X25),sK4)) )
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f814])).

fof(f814,plain,
    ( ! [X99,X97,X98,X96] :
        ( ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X97),u1_struct_0(X98))))
        | ~ v1_funct_1(X96)
        | ~ v2_pre_topc(X97)
        | ~ l1_pre_topc(X97)
        | v2_struct_0(X98)
        | ~ v2_pre_topc(X98)
        | ~ l1_pre_topc(X98)
        | ~ v1_funct_2(X96,u1_struct_0(X97),u1_struct_0(X98))
        | ~ m1_pre_topc(X99,X97)
        | v2_struct_0(X97)
        | ~ v1_funct_1(k2_tmap_1(X97,X98,X96,X99))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X97,X98,X96,X99),sK4)) )
    | ~ spl9_84 ),
    inference(resolution,[],[f400,f668])).

fof(f2896,plain,
    ( spl9_3
    | spl9_292
    | ~ spl9_56
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2819,f2796,f457,f118,f113,f153,f148,f143,f479,f2894,f123])).

fof(f2894,plain,
    ( spl9_292
  <=> ! [X22,X21,X23,X24] :
        ( ~ m1_pre_topc(X21,sK0)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | v1_funct_1(k5_relat_1(X22,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X21))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_292])])).

fof(f2819,plain,
    ( ! [X24,X23,X21,X22] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X21,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X21))
        | v1_funct_1(k5_relat_1(X22,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X21)))
        | ~ v1_funct_1(X22) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f813])).

fof(f813,plain,(
    ! [X94,X92,X90,X95,X93,X91,X89] :
      ( ~ m1_subset_1(X89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X90),u1_struct_0(X91))))
      | ~ v1_funct_1(X89)
      | ~ v2_pre_topc(X90)
      | ~ l1_pre_topc(X90)
      | v2_struct_0(X91)
      | ~ v2_pre_topc(X91)
      | ~ l1_pre_topc(X91)
      | ~ v1_funct_2(X89,u1_struct_0(X90),u1_struct_0(X91))
      | ~ m1_pre_topc(X92,X90)
      | v2_struct_0(X90)
      | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(X94,X95)))
      | ~ v1_funct_1(k2_tmap_1(X90,X91,X89,X92))
      | v1_funct_1(k5_relat_1(X93,k2_tmap_1(X90,X91,X89,X92)))
      | ~ v1_funct_1(X93) ) ),
    inference(resolution,[],[f400,f286])).

fof(f2892,plain,
    ( ~ spl9_37
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_35
    | spl9_291
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2818,f2796,f671,f2890,f311,f457,f479,f319])).

fof(f2890,plain,
    ( spl9_291
  <=> ! [X20] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X20),sK5))
        | ~ l1_struct_0(X20)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X20)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_291])])).

fof(f2818,plain,
    ( ! [X20] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X20),sK5))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X20))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_85
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f715])).

fof(f715,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,X1,X2,X3),sK5))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
        | ~ l1_struct_0(X3)
        | ~ l1_struct_0(X0) )
    | ~ spl9_85 ),
    inference(resolution,[],[f672,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2888,plain,
    ( ~ spl9_37
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_35
    | spl9_290
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2817,f2796,f667,f2886,f311,f457,f479,f319])).

fof(f2886,plain,
    ( spl9_290
  <=> ! [X19] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X19),sK4))
        | ~ l1_struct_0(X19)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_290])])).

fof(f2817,plain,
    ( ! [X19] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X19),sK4))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X19))
        | ~ l1_struct_0(X19)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_84
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f676])).

fof(f676,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,X1,X2,X3),sK4))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
        | ~ l1_struct_0(X3)
        | ~ l1_struct_0(X0) )
    | ~ spl9_84 ),
    inference(resolution,[],[f668,f87])).

fof(f2884,plain,
    ( ~ spl9_37
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_35
    | spl9_289
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2816,f2796,f2882,f311,f457,f479,f319])).

fof(f2882,plain,
    ( spl9_289
  <=> ! [X16,X18,X15,X17] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X15))
        | ~ l1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X16)
        | v1_funct_1(k5_relat_1(X16,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X15))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_289])])).

fof(f2816,plain,
    ( ! [X17,X15,X18,X16] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X15))
        | v1_funct_1(k5_relat_1(X16,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X15)))
        | ~ v1_funct_1(X16)
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ l1_struct_0(X15)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f661])).

fof(f661,plain,(
    ! [X6,X12,X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
      | ~ v1_funct_1(k2_tmap_1(X9,X10,X11,X12))
      | v1_funct_1(k5_relat_1(X6,k2_tmap_1(X9,X10,X11,X12)))
      | ~ v1_funct_1(X6)
      | ~ l1_struct_0(X10)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ l1_struct_0(X12)
      | ~ l1_struct_0(X9) ) ),
    inference(resolution,[],[f286,f87])).

fof(f2880,plain,
    ( spl9_3
    | ~ spl9_56
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | spl9_288
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2815,f2796,f457,f2878,f118,f113,f153,f148,f143,f479,f123])).

fof(f2878,plain,
    ( spl9_288
  <=> ! [X13,X14] :
        ( ~ r2_hidden(X13,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X14))
        | ~ m1_pre_topc(X14,sK0)
        | m1_subset_1(X13,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_288])])).

fof(f2815,plain,
    ( ! [X14,X13] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ r2_hidden(X13,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X14))
        | m1_subset_1(X13,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X14,sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f658])).

fof(f658,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k2_tmap_1(X0,X1,X2,X3))
      | m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f657])).

fof(f657,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(X4,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f282,f88])).

fof(f2876,plain,
    ( ~ spl9_37
    | spl9_287
    | ~ spl9_35
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2813,f2796,f457,f479,f311,f2874,f319])).

fof(f2874,plain,
    ( spl9_287
  <=> ! [X9,X10] :
        ( ~ l1_struct_0(X9)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK2)))
        | ~ r2_hidden(X10,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_287])])).

fof(f2813,plain,
    ( ! [X10,X9] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X9)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(X10,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X9))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK2))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f375])).

fof(f375,plain,(
    ! [X39,X37,X38,X36,X40] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36))))
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,u1_struct_0(X38),u1_struct_0(X36))
      | ~ l1_struct_0(X36)
      | ~ l1_struct_0(X39)
      | ~ l1_struct_0(X38)
      | ~ r2_hidden(X40,k2_tmap_1(X38,X36,X37,X39))
      | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X36))) ) ),
    inference(resolution,[],[f87,f92])).

fof(f2872,plain,
    ( ~ spl9_37
    | spl9_286
    | ~ spl9_35
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2812,f2796,f457,f479,f311,f2870,f319])).

fof(f2870,plain,
    ( spl9_286
  <=> ! [X7,X8] :
        ( ~ l1_struct_0(X7)
        | m1_subset_1(X8,k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK2)))
        | ~ r2_hidden(X8,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_286])])).

fof(f2812,plain,
    ( ! [X8,X7] :
        ( ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X7)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(X8,k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X7))
        | m1_subset_1(X8,k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK2))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f374])).

fof(f374,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X33),u1_struct_0(X31))
      | ~ l1_struct_0(X31)
      | ~ l1_struct_0(X34)
      | ~ l1_struct_0(X33)
      | ~ r2_hidden(X35,k2_tmap_1(X33,X31,X32,X34))
      | m1_subset_1(X35,k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X31))) ) ),
    inference(resolution,[],[f87,f93])).

fof(f2868,plain,
    ( ~ spl9_282
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_285
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2811,f2796,f2866,f123,f118,f113,f153,f148,f143,f457,f479,f2854])).

fof(f2854,plain,
    ( spl9_282
  <=> v5_pre_topc(k5_relat_1(sK5,sK4),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_282])])).

fof(f2866,plain,
    ( spl9_285
  <=> ! [X5,X6] :
        ( ~ v2_pre_topc(X5)
        | v5_pre_topc(k5_relat_1(X6,k5_relat_1(sK5,sK4)),X5,sK2)
        | v2_struct_0(X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X6,X5,sK0)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
        | ~ l1_pre_topc(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_285])])).

fof(f2811,plain,
    ( ! [X6,X5] :
        ( ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(sK0))
        | ~ v5_pre_topc(X6,X5,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK0))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v5_pre_topc(k5_relat_1(sK5,sK4),sK0,sK2)
        | v2_struct_0(X5)
        | v5_pre_topc(k5_relat_1(X6,k5_relat_1(sK5,sK4)),X5,sK2) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v5_pre_topc(X4,X1,X2)
      | v2_struct_0(X0)
      | v5_pre_topc(k5_relat_1(X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v5_pre_topc(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_2(k5_relat_1(X3,X4),u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v5_pre_topc(X4,X1,X2)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v5_pre_topc(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_2(k5_relat_1(X3,X4),u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(k5_relat_1(X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v5_pre_topc(X4,X1,X2)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & v5_pre_topc(X4,X1,X2)
        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X3,X0,X1)
        & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X3)
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k5_relat_1(X3,X4),X0,X2)
        & v1_funct_2(k5_relat_1(X3,X4),u1_struct_0(X0),u1_struct_0(X2))
        & v1_funct_1(k5_relat_1(X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_borsuk_1)).

fof(f2864,plain,
    ( ~ spl9_282
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_284
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2810,f2796,f2862,f123,f118,f113,f153,f148,f143,f457,f479,f2854])).

fof(f2862,plain,
    ( spl9_284
  <=> ! [X3,X4] :
        ( ~ v2_pre_topc(X3)
        | v1_funct_2(k5_relat_1(X4,k5_relat_1(sK5,sK4)),u1_struct_0(X3),u1_struct_0(sK2))
        | v2_struct_0(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X4,X3,sK0)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_284])])).

fof(f2810,plain,
    ( ! [X4,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v5_pre_topc(X4,X3,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v5_pre_topc(k5_relat_1(sK5,sK4),sK0,sK2)
        | v2_struct_0(X3)
        | v1_funct_2(k5_relat_1(X4,k5_relat_1(sK5,sK4)),u1_struct_0(X3),u1_struct_0(sK2)) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v5_pre_topc(X4,X1,X2)
      | v2_struct_0(X0)
      | v1_funct_2(k5_relat_1(X3,X4),u1_struct_0(X0),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2860,plain,
    ( ~ spl9_282
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_283
    | ~ spl9_281 ),
    inference(avatar_split_clause,[],[f2809,f2796,f2858,f123,f118,f113,f153,f148,f143,f457,f479,f2854])).

fof(f2858,plain,
    ( spl9_283
  <=> ! [X1,X2] :
        ( ~ v2_pre_topc(X1)
        | v1_funct_1(k5_relat_1(X2,k5_relat_1(sK5,sK4)))
        | v2_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X2,X1,sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_283])])).

fof(f2809,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v5_pre_topc(X2,X1,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
        | ~ v5_pre_topc(k5_relat_1(sK5,sK4),sK0,sK2)
        | v2_struct_0(X1)
        | v1_funct_1(k5_relat_1(X2,k5_relat_1(sK5,sK4))) )
    | ~ spl9_281 ),
    inference(resolution,[],[f2797,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v5_pre_topc(X4,X1,X2)
      | v2_struct_0(X0)
      | v1_funct_1(k5_relat_1(X3,X4)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2803,plain,
    ( ~ spl9_20
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_267
    | spl9_185 ),
    inference(avatar_split_clause,[],[f2703,f2194,f2671,f198,f178,f168,f208])).

fof(f2671,plain,
    ( spl9_267
  <=> m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_267])])).

fof(f2703,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | spl9_185 ),
    inference(superposition,[],[f2196,f83])).

fof(f2196,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | spl9_185 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f2802,plain,
    ( ~ spl9_20
    | spl9_165
    | ~ spl9_14
    | spl9_164
    | spl9_281 ),
    inference(avatar_split_clause,[],[f2801,f2796,f1654,f178,f1657,f208])).

fof(f1657,plain,
    ( spl9_165
  <=> ! [X48] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X48,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_165])])).

fof(f1654,plain,
    ( spl9_164
  <=> ! [X49] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X49))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_164])])).

fof(f2801,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK2))))
        | ~ v1_funct_1(sK5) )
    | spl9_281 ),
    inference(resolution,[],[f2798,f297])).

fof(f2798,plain,
    ( ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | spl9_281 ),
    inference(avatar_component_clause,[],[f2796])).

fof(f2799,plain,
    ( ~ spl9_37
    | ~ spl9_197
    | ~ spl9_281
    | ~ spl9_56
    | ~ spl9_53
    | ~ spl9_35
    | spl9_267 ),
    inference(avatar_split_clause,[],[f2794,f2671,f311,f457,f479,f2796,f2246,f319])).

fof(f2794,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ m1_subset_1(k5_relat_1(sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl9_267 ),
    inference(resolution,[],[f2673,f87])).

fof(f2673,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | spl9_267 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f2793,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_280
    | ~ spl9_167 ),
    inference(avatar_split_clause,[],[f2789,f1665,f2791,f138,f133,f128])).

fof(f2791,plain,
    ( spl9_280
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4),X5))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X5)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X4,X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).

fof(f1665,plain,
    ( spl9_167
  <=> ! [X58,X60,X62,X59,X61] :
        ( ~ v1_funct_1(k2_tmap_1(X58,sK1,X59,X60))
        | ~ v1_funct_1(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(sK1))
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X58,sK1,X59,X60),u1_struct_0(X58),u1_struct_0(sK1))
        | v1_funct_1(k2_tmap_1(X58,sK2,k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4),X62))
        | ~ l1_struct_0(X62)
        | ~ l1_struct_0(X58)
        | ~ m1_subset_1(k2_tmap_1(X58,sK1,X59,X60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),X61)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_167])])).

fof(f2789,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4),X5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X4,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4))
        | ~ m1_subset_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1)) )
    | ~ spl9_167 ),
    inference(duplicate_literal_removal,[],[f2788])).

fof(f2788,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4),X5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X4,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),sK4))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4))
        | ~ m1_subset_1(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK1),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1))
        | v2_struct_0(X0) )
    | ~ spl9_167 ),
    inference(superposition,[],[f1666,f951])).

fof(f1666,plain,
    ( ! [X61,X59,X62,X60,X58] :
        ( v1_funct_1(k2_tmap_1(X58,sK2,k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4),X62))
        | ~ v1_funct_1(X59)
        | ~ v2_pre_topc(X58)
        | ~ l1_pre_topc(X58)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(sK1))
        | ~ m1_pre_topc(X60,X58)
        | v2_struct_0(X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X58,sK1,X59,X60),u1_struct_0(X58),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X58,sK1,X59,X60))
        | ~ l1_struct_0(X62)
        | ~ l1_struct_0(X58)
        | ~ m1_subset_1(k2_tmap_1(X58,sK1,X59,X60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),X61)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4)) )
    | ~ spl9_167 ),
    inference(avatar_component_clause,[],[f1665])).

fof(f2787,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_279
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f2783,f1647,f2785,f123,f118,f113])).

fof(f2785,plain,
    ( spl9_279
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5),X5))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X5)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X4,X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_279])])).

fof(f1647,plain,
    ( spl9_162
  <=> ! [X44,X46,X43,X45,X47] :
        ( ~ v1_funct_1(k2_tmap_1(X43,sK0,X44,X45))
        | ~ v1_funct_1(X44)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v1_funct_2(X44,u1_struct_0(X43),u1_struct_0(sK0))
        | ~ m1_pre_topc(X45,X43)
        | v2_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X43,sK0,X44,X45),u1_struct_0(X43),u1_struct_0(sK0))
        | v1_funct_1(k2_tmap_1(X43,sK1,k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5),X47))
        | ~ l1_struct_0(X47)
        | ~ l1_struct_0(X43)
        | ~ m1_subset_1(k2_tmap_1(X43,sK0,X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),X46)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f2783,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5),X5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(X4,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) )
    | ~ spl9_162 ),
    inference(duplicate_literal_removal,[],[f2782])).

fof(f2782,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_funct_1(k2_tmap_1(X0,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5),X5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(X4,X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ l1_struct_0(X5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),X6)))
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),sK5))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X4),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),k2_tmap_1(X0,X1,X2,X4),X3),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4))
        | ~ m1_subset_1(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,X3),X4),u1_struct_0(X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
        | v2_struct_0(X0) )
    | ~ spl9_162 ),
    inference(superposition,[],[f1648,f951])).

fof(f1648,plain,
    ( ! [X47,X45,X43,X46,X44] :
        ( v1_funct_1(k2_tmap_1(X43,sK1,k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5),X47))
        | ~ v1_funct_1(X44)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ v1_funct_2(X44,u1_struct_0(X43),u1_struct_0(sK0))
        | ~ m1_pre_topc(X45,X43)
        | v2_struct_0(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X43,sK0,X44,X45),u1_struct_0(X43),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X43,sK0,X44,X45))
        | ~ l1_struct_0(X47)
        | ~ l1_struct_0(X43)
        | ~ m1_subset_1(k2_tmap_1(X43,sK0,X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),X46)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5)) )
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f2781,plain,
    ( spl9_277
    | spl9_278
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2773,f2186,f2779,f2775])).

fof(f2775,plain,
    ( spl9_277
  <=> v1_xboole_0(k2_tmap_1(sK0,sK1,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_277])])).

fof(f2779,plain,
    ( spl9_278
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k2_tmap_1(sK0,sK1,sK5,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_278])])).

fof(f2773,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | v1_xboole_0(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(X0,k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2317,f94])).

fof(f2317,plain,
    ( ! [X69] :
        ( ~ r2_hidden(X69,k2_tmap_1(sK0,sK1,sK5,sK3))
        | m1_subset_1(X69,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f93])).

fof(f2762,plain,
    ( ~ spl9_183
    | ~ spl9_276 ),
    inference(avatar_contradiction_clause,[],[f2761])).

fof(f2761,plain,
    ( $false
    | ~ spl9_183
    | ~ spl9_276 ),
    inference(resolution,[],[f2756,f2187])).

fof(f2756,plain,
    ( ! [X1] : ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1)))
    | ~ spl9_276 ),
    inference(avatar_component_clause,[],[f2755])).

fof(f2755,plain,
    ( spl9_276
  <=> ! [X1] : ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_276])])).

fof(f2757,plain,
    ( spl9_275
    | ~ spl9_197
    | spl9_276
    | ~ spl9_220
    | ~ spl9_35
    | ~ spl9_182
    | spl9_165
    | ~ spl9_14
    | ~ spl9_219 ),
    inference(avatar_split_clause,[],[f2750,f2398,f178,f1657,f2182,f311,f2403,f2755,f2246,f2752])).

fof(f2752,plain,
    ( spl9_275
  <=> ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK3,sK2,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_275])])).

fof(f2403,plain,
    ( spl9_220
  <=> v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_220])])).

fof(f2398,plain,
    ( spl9_219
  <=> v1_funct_2(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_219])])).

fof(f2750,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1)))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK3,sK2,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),X2)) )
    | ~ spl9_219 ),
    inference(resolution,[],[f2400,f705])).

fof(f705,plain,(
    ! [X103,X107,X105,X102,X108,X106,X104] :
      ( ~ v1_funct_2(k5_relat_1(X102,X105),u1_struct_0(X103),u1_struct_0(X107))
      | ~ v1_funct_1(X105)
      | ~ m1_subset_1(X105,k1_zfmisc_1(k2_zfmisc_1(X106,u1_struct_0(X107))))
      | ~ v1_funct_1(X102)
      | ~ l1_struct_0(X107)
      | ~ v1_funct_1(k5_relat_1(X102,X105))
      | ~ m1_subset_1(X102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X103),X104)))
      | ~ l1_struct_0(X103)
      | ~ l1_struct_0(X108)
      | v1_funct_1(k2_tmap_1(X103,X107,k5_relat_1(X102,X105),X108)) ) ),
    inference(resolution,[],[f297,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2400,plain,
    ( v1_funct_2(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl9_219 ),
    inference(avatar_component_clause,[],[f2398])).

fof(f2740,plain,
    ( ~ spl9_182
    | spl9_274
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2722,f2186,f2738,f2182])).

fof(f2738,plain,
    ( spl9_274
  <=> ! [X25,X27,X24,X26] :
        ( ~ m1_subset_1(X24,k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | v1_xboole_0(k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | m1_subset_1(X24,k2_zfmisc_1(X26,u1_struct_0(sK1)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X25) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_274])])).

fof(f2722,plain,
    ( ! [X26,X24,X27,X25] :
        ( ~ m1_subset_1(X24,k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | m1_subset_1(X24,k2_zfmisc_1(X26,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f1523,f2187])).

fof(f2736,plain,
    ( ~ spl9_20
    | spl9_273
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f2719,f198,f2734,f208])).

fof(f2734,plain,
    ( spl9_273
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_subset_1(X4,k5_relat_1(X5,sK5))
        | v1_xboole_0(k5_relat_1(X5,sK5))
        | m1_subset_1(X4,k2_zfmisc_1(X6,u1_struct_0(sK1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_273])])).

fof(f2719,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k5_relat_1(X5,sK5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | m1_subset_1(X4,k2_zfmisc_1(X6,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X5,sK5))
        | ~ v1_funct_1(sK5) )
    | ~ spl9_18 ),
    inference(resolution,[],[f1523,f200])).

fof(f200,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f2732,plain,
    ( ~ spl9_14
    | spl9_272
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2718,f168,f2730,f178])).

fof(f2730,plain,
    ( spl9_272
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k5_relat_1(X1,sK4))
        | v1_xboole_0(k5_relat_1(X1,sK4))
        | m1_subset_1(X0,k2_zfmisc_1(X2,u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f2718,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k5_relat_1(X1,sK4))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(X0,k2_zfmisc_1(X2,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X1,sK4))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1523,f170])).

fof(f170,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f2717,plain,
    ( ~ spl9_37
    | ~ spl9_197
    | ~ spl9_269
    | ~ spl9_270
    | ~ spl9_271
    | ~ spl9_35
    | spl9_185 ),
    inference(avatar_split_clause,[],[f2702,f2194,f311,f2714,f2710,f2706,f2246,f319])).

fof(f2706,plain,
    ( spl9_269
  <=> m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_269])])).

fof(f2710,plain,
    ( spl9_270
  <=> v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_270])])).

fof(f2714,plain,
    ( spl9_271
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_271])])).

fof(f2702,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4))
    | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl9_185 ),
    inference(resolution,[],[f2196,f87])).

fof(f2695,plain,
    ( ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | ~ spl9_220
    | spl9_188 ),
    inference(avatar_split_clause,[],[f2692,f2206,f2403,f2186,f178,f168,f2182])).

fof(f2206,plain,
    ( spl9_188
  <=> v1_funct_1(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_188])])).

fof(f2692,plain,
    ( ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | spl9_188 ),
    inference(superposition,[],[f2208,f83])).

fof(f2208,plain,
    ( ~ v1_funct_1(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | spl9_188 ),
    inference(avatar_component_clause,[],[f2206])).

fof(f2694,plain,
    ( ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | spl9_188 ),
    inference(avatar_split_clause,[],[f2690,f2206,f2186,f178,f168,f2182])).

fof(f2690,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | spl9_188 ),
    inference(resolution,[],[f2208,f81])).

fof(f2689,plain,
    ( ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | spl9_268
    | ~ spl9_197
    | ~ spl9_35
    | ~ spl9_188
    | ~ spl9_187 ),
    inference(avatar_split_clause,[],[f2682,f2202,f2206,f311,f2246,f2687,f2186,f178,f168,f2182])).

fof(f2687,plain,
    ( spl9_268
  <=> ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK3,sK2,k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_268])])).

fof(f2202,plain,
    ( spl9_187
  <=> v1_funct_2(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_187])])).

fof(f2682,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X2)
        | v1_funct_1(k2_tmap_1(sK3,sK2,k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),X2))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_187 ),
    inference(resolution,[],[f2203,f301])).

fof(f301,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] :
      ( ~ v1_funct_2(k1_partfun1(u1_struct_0(X8),X9,X10,u1_struct_0(X7),X11,X12),u1_struct_0(X8),u1_struct_0(X7))
      | ~ v1_funct_1(k1_partfun1(u1_struct_0(X8),X9,X10,u1_struct_0(X7),X11,X12))
      | ~ l1_struct_0(X7)
      | ~ l1_struct_0(X8)
      | ~ l1_struct_0(X13)
      | v1_funct_1(k2_tmap_1(X8,X7,k1_partfun1(u1_struct_0(X8),X9,X10,u1_struct_0(X7),X11,X12),X13))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),X9)))
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,u1_struct_0(X7))))
      | ~ v1_funct_1(X11) ) ),
    inference(resolution,[],[f85,f82])).

fof(f2203,plain,
    ( v1_funct_2(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl9_187 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2680,plain,
    ( spl9_11
    | ~ spl9_197
    | ~ spl9_221 ),
    inference(avatar_split_clause,[],[f2679,f2408,f2246,f163])).

fof(f2408,plain,
    ( spl9_221
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_221])])).

fof(f2679,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_221 ),
    inference(resolution,[],[f2410,f104])).

fof(f2410,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_221 ),
    inference(avatar_component_clause,[],[f2408])).

fof(f2678,plain,
    ( ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | ~ spl9_219
    | spl9_187 ),
    inference(avatar_split_clause,[],[f2676,f2202,f2398,f2186,f178,f168,f2182])).

fof(f2676,plain,
    ( ~ v1_funct_2(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | spl9_187 ),
    inference(superposition,[],[f2204,f83])).

fof(f2204,plain,
    ( ~ v1_funct_2(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | spl9_187 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2674,plain,
    ( ~ spl9_182
    | ~ spl9_183
    | ~ spl9_265
    | ~ spl9_2
    | ~ spl9_266
    | ~ spl9_187
    | ~ spl9_188
    | ~ spl9_267
    | spl9_3
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_10
    | spl9_11
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | spl9_32
    | ~ spl9_189 ),
    inference(avatar_split_clause,[],[f2660,f2210,f288,f113,f138,f133,f128,f153,f148,f143,f163,f158,f208,f203,f198,f178,f173,f168,f123,f2671,f2206,f2202,f2667,f118,f2663,f2186,f2182])).

fof(f173,plain,
    ( spl9_13
  <=> v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f203,plain,
    ( spl9_19
  <=> v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f158,plain,
    ( spl9_10
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f288,plain,
    ( spl9_32
  <=> v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f2210,plain,
    ( spl9_189
  <=> v5_pre_topc(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_189])])).

fof(f2660,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3))
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ spl9_189 ),
    inference(superposition,[],[f2211,f1034])).

fof(f2211,plain,
    ( v5_pre_topc(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2)
    | ~ spl9_189 ),
    inference(avatar_component_clause,[],[f2210])).

fof(f2659,plain,
    ( spl9_11
    | spl9_264
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_182
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2567,f2186,f667,f2182,f249,f221,f138,f133,f128,f2323,f2657,f163])).

fof(f2657,plain,
    ( spl9_264
  <=> ! [X12] :
        ( ~ m1_pre_topc(X12,sK3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12),sK4))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_264])])).

fof(f2567,plain,
    ( ! [X12] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X12,sK3)
        | v2_struct_0(sK3)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12),sK4)) )
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(resolution,[],[f814,f2187])).

fof(f2655,plain,
    ( spl9_11
    | spl9_263
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_182
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2587,f2186,f671,f2182,f249,f221,f138,f133,f128,f2323,f2653,f163])).

fof(f2653,plain,
    ( spl9_263
  <=> ! [X12] :
        ( ~ m1_pre_topc(X12,sK3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12),sK5))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_263])])).

fof(f2587,plain,
    ( ! [X12] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X12,sK3)
        | v2_struct_0(sK3)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X12),sK5)) )
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(resolution,[],[f815,f2187])).

fof(f2651,plain,
    ( ~ spl9_37
    | ~ spl9_197
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | spl9_201 ),
    inference(avatar_split_clause,[],[f2650,f2323,f307,f208,f203,f198,f2246,f319])).

fof(f307,plain,
    ( spl9_34
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f2650,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl9_201 ),
    inference(resolution,[],[f2325,f86])).

fof(f2325,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl9_201 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2649,plain,
    ( ~ spl9_182
    | spl9_262
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2631,f2186,f2647,f2182])).

fof(f2647,plain,
    ( spl9_262
  <=> ! [X25,X27,X24,X26] :
        ( ~ m1_subset_1(X24,k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | v1_xboole_0(k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(X26,u1_struct_0(sK1)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X25) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_262])])).

fof(f2631,plain,
    ( ! [X26,X24,X27,X25] :
        ( ~ m1_subset_1(X24,k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_xboole_0(k2_zfmisc_1(X26,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X25,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f1518,f2187])).

fof(f2645,plain,
    ( ~ spl9_20
    | spl9_261
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f2628,f198,f2643,f208])).

fof(f2643,plain,
    ( spl9_261
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_subset_1(X4,k5_relat_1(X5,sK5))
        | v1_xboole_0(k5_relat_1(X5,sK5))
        | ~ v1_xboole_0(k2_zfmisc_1(X6,u1_struct_0(sK1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_261])])).

fof(f2628,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k5_relat_1(X5,sK5))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_xboole_0(k2_zfmisc_1(X6,u1_struct_0(sK1)))
        | v1_xboole_0(k5_relat_1(X5,sK5))
        | ~ v1_funct_1(sK5) )
    | ~ spl9_18 ),
    inference(resolution,[],[f1518,f200])).

fof(f2641,plain,
    ( ~ spl9_14
    | spl9_260
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f2627,f168,f2639,f178])).

fof(f2639,plain,
    ( spl9_260
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k5_relat_1(X1,sK4))
        | v1_xboole_0(k5_relat_1(X1,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(X2,u1_struct_0(sK2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_260])])).

fof(f2627,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k5_relat_1(X1,sK4))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_xboole_0(k2_zfmisc_1(X2,u1_struct_0(sK2)))
        | v1_xboole_0(k5_relat_1(X1,sK4))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_12 ),
    inference(resolution,[],[f1518,f170])).

fof(f2620,plain,
    ( ~ spl9_182
    | ~ spl9_20
    | spl9_259
    | ~ spl9_197
    | ~ spl9_159
    | spl9_247 ),
    inference(avatar_split_clause,[],[f2615,f2520,f1593,f2246,f2617,f208,f2182])).

fof(f2617,plain,
    ( spl9_259
  <=> ! [X1,X0] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_259])])).

fof(f1593,plain,
    ( spl9_159
  <=> ! [X5,X7,X4,X6] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4))
        | ~ l1_struct_0(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X5)
        | v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_159])])).

fof(f2520,plain,
    ( spl9_247
  <=> v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_247])])).

fof(f2615,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_159
    | spl9_247 ),
    inference(resolution,[],[f2522,f1594])).

fof(f1594,plain,
    ( ! [X6,X4,X7,X5] :
        ( v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4)))
        | ~ l1_struct_0(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4)) )
    | ~ spl9_159 ),
    inference(avatar_component_clause,[],[f1593])).

fof(f2522,plain,
    ( ~ v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | spl9_247 ),
    inference(avatar_component_clause,[],[f2520])).

fof(f2619,plain,
    ( ~ spl9_10
    | spl9_259
    | ~ spl9_182
    | ~ spl9_20
    | ~ spl9_181
    | spl9_247 ),
    inference(avatar_split_clause,[],[f2614,f2520,f1811,f208,f2182,f2617,f158])).

fof(f1811,plain,
    ( spl9_181
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_181])])).

fof(f2614,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl9_181
    | spl9_247 ),
    inference(resolution,[],[f2522,f1812])).

fof(f1812,plain,
    ( ! [X6,X4,X7,X5] :
        ( v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4)))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl9_181 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f2611,plain,
    ( ~ spl9_182
    | ~ spl9_14
    | spl9_258
    | ~ spl9_197
    | ~ spl9_159
    | spl9_245 ),
    inference(avatar_split_clause,[],[f2606,f2511,f1593,f2246,f2608,f178,f2182])).

fof(f2608,plain,
    ( spl9_258
  <=> ! [X1,X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f2511,plain,
    ( spl9_245
  <=> v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_245])])).

fof(f2606,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_159
    | spl9_245 ),
    inference(resolution,[],[f2513,f1594])).

fof(f2513,plain,
    ( ~ v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | spl9_245 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f2610,plain,
    ( ~ spl9_10
    | spl9_258
    | ~ spl9_182
    | ~ spl9_14
    | ~ spl9_181
    | spl9_245 ),
    inference(avatar_split_clause,[],[f2605,f2511,f1811,f178,f2182,f2608,f158])).

fof(f2605,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl9_181
    | spl9_245 ),
    inference(resolution,[],[f2513,f1812])).

fof(f2602,plain,
    ( spl9_3
    | spl9_257
    | ~ spl9_19
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f2584,f671,f198,f208,f118,f113,f138,f133,f128,f203,f2600,f123])).

fof(f2600,plain,
    ( spl9_257
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK5))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_257])])).

fof(f2584,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK5)) )
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(resolution,[],[f815,f200])).

fof(f2598,plain,
    ( spl9_6
    | spl9_256
    | ~ spl9_13
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f2583,f671,f168,f178,f133,f128,f153,f148,f143,f173,f2596,f138])).

fof(f2596,plain,
    ( spl9_256
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK5))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_256])])).

fof(f2583,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK5)) )
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(resolution,[],[f815,f170])).

fof(f2582,plain,
    ( spl9_3
    | spl9_255
    | ~ spl9_19
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f2564,f667,f198,f208,f118,f113,f138,f133,f128,f203,f2580,f123])).

fof(f2580,plain,
    ( spl9_255
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK4))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_255])])).

fof(f2564,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK4)) )
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(resolution,[],[f814,f200])).

fof(f2578,plain,
    ( spl9_6
    | spl9_254
    | ~ spl9_13
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f2563,f667,f168,f178,f133,f128,f153,f148,f143,f173,f2576,f138])).

fof(f2576,plain,
    ( spl9_254
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK4))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_254])])).

fof(f2563,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK4)) )
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(resolution,[],[f814,f170])).

fof(f2562,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_253
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f2553,f1243,f2560,f123,f118,f113])).

fof(f2560,plain,
    ( spl9_253
  <=> ! [X3,X5,X4] :
        ( ~ l1_struct_0(X3)
        | ~ m1_pre_topc(X5,X3)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3),sK5))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X4,X5),u1_struct_0(X3),u1_struct_0(sK0))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_253])])).

fof(f1243,plain,
    ( spl9_133
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_pre_topc(X1,X1)
        | v2_struct_0(X1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK0,X0,X1),sK5))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f2553,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X4,X5))
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X4,X5),u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_pre_topc(X3,X3)
        | v2_struct_0(X3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3),sK5))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_1(X4)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_pre_topc(X5,X3) )
    | ~ spl9_133 ),
    inference(duplicate_literal_removal,[],[f2546])).

fof(f2546,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,X4,X5))
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK0,X4,X5),u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_pre_topc(X3,X3)
        | v2_struct_0(X3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3),sK5))
        | ~ v1_funct_1(k2_tmap_1(X3,sK0,k2_tmap_1(X3,sK0,X4,X5),X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
        | ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
        | ~ m1_pre_topc(X5,X3)
        | v2_struct_0(X3) )
    | ~ spl9_133 ),
    inference(resolution,[],[f1244,f400])).

fof(f1244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_pre_topc(X1,X1)
        | v2_struct_0(X1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK0,X0,X1),sK5))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,X1)) )
    | ~ spl9_133 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f2558,plain,
    ( ~ spl9_37
    | spl9_252
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f2554,f1243,f2556,f319])).

fof(f2556,plain,
    ( spl9_252
  <=> ! [X1,X0,X2] :
        ( ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0),sK5))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X2,X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_252])])).

fof(f2554,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X2,X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X2,X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(X0,X0)
        | v2_struct_0(X0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0),sK5))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0))
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1) )
    | ~ spl9_133 ),
    inference(duplicate_literal_removal,[],[f2545])).

fof(f2545,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X2,X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK0,X2,X0),u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_pre_topc(X0,X0)
        | v2_struct_0(X0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0),sK5))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,k2_tmap_1(X1,sK0,X2,X0),X0))
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1) )
    | ~ spl9_133 ),
    inference(resolution,[],[f1244,f87])).

fof(f2544,plain,
    ( ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | ~ spl9_205
    | spl9_189 ),
    inference(avatar_split_clause,[],[f2543,f2210,f2341,f2186,f178,f168,f2182])).

fof(f2341,plain,
    ( spl9_205
  <=> v5_pre_topc(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_205])])).

fof(f2543,plain,
    ( ~ v5_pre_topc(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | spl9_189 ),
    inference(superposition,[],[f2212,f83])).

fof(f2212,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2)
    | spl9_189 ),
    inference(avatar_component_clause,[],[f2210])).

fof(f2541,plain,
    ( ~ spl9_212
    | spl9_251
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2318,f2186,f2539,f2370])).

fof(f2370,plain,
    ( spl9_212
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f2539,plain,
    ( spl9_251
  <=> ! [X70] : ~ r2_hidden(X70,k2_tmap_1(sK0,sK1,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_251])])).

fof(f2318,plain,
    ( ! [X70] :
        ( ~ r2_hidden(X70,k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f92])).

fof(f2537,plain,
    ( ~ spl9_247
    | ~ spl9_182
    | spl9_250
    | ~ spl9_155
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2316,f2186,f1542,f2534,f2182,f2520])).

fof(f2534,plain,
    ( spl9_250
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_250])])).

fof(f2316,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | ~ spl9_155
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1543])).

fof(f2532,plain,
    ( ~ spl9_245
    | ~ spl9_182
    | spl9_249
    | ~ spl9_154
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2315,f2186,f1538,f2529,f2182,f2511])).

fof(f2529,plain,
    ( spl9_249
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_249])])).

fof(f2315,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | ~ spl9_154
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1539])).

fof(f2527,plain,
    ( ~ spl9_247
    | ~ spl9_182
    | spl9_248
    | ~ spl9_149
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2314,f2186,f1461,f2524,f2182,f2520])).

fof(f2524,plain,
    ( spl9_248
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f2314,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(sK5,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | ~ spl9_149
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1462])).

fof(f2518,plain,
    ( ~ spl9_245
    | ~ spl9_182
    | spl9_246
    | ~ spl9_148
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2313,f2186,f1457,f2515,f2182,f2511])).

fof(f2515,plain,
    ( spl9_246
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).

fof(f2313,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(sK4,k2_tmap_1(sK0,sK1,sK5,sK3)))
    | ~ spl9_148
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1458])).

fof(f2509,plain,
    ( ~ spl9_182
    | spl9_244
    | ~ spl9_147
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2312,f2186,f1443,f2507,f2182])).

fof(f2507,plain,
    ( spl9_244
  <=> ! [X67,X66,X68] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X66)))
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
        | ~ v1_funct_1(X66)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X66)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f2312,plain,
    ( ! [X68,X66,X67] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X66)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X66))
        | ~ v1_funct_1(X66)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X67,X68))) )
    | ~ spl9_147
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1444])).

fof(f2505,plain,
    ( ~ spl9_182
    | spl9_243
    | ~ spl9_146
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2311,f2186,f1439,f2503,f2182])).

fof(f2503,plain,
    ( spl9_243
  <=> ! [X63,X65,X64] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X63)))
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
        | ~ v1_funct_1(X63)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X63)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_243])])).

fof(f2311,plain,
    ( ! [X64,X65,X63] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X63)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),X63))
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
    | ~ spl9_146
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1440])).

fof(f2501,plain,
    ( ~ spl9_182
    | spl9_242
    | ~ spl9_212
    | ~ spl9_135
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2310,f2186,f1268,f2370,f2499,f2182])).

fof(f2499,plain,
    ( spl9_242
  <=> ! [X62] : ~ r2_hidden(X62,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f1268,plain,
    ( spl9_135
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_xboole_0(k2_zfmisc_1(X5,u1_struct_0(sK1)))
        | ~ r2_hidden(X7,k5_relat_1(X4,sK5))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f2310,plain,
    ( ! [X62] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | ~ r2_hidden(X62,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_135
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1269])).

fof(f1269,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_xboole_0(k2_zfmisc_1(X5,u1_struct_0(sK1)))
        | ~ r2_hidden(X7,k5_relat_1(X4,sK5))
        | ~ v1_funct_1(X4) )
    | ~ spl9_135 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f2497,plain,
    ( ~ spl9_182
    | spl9_240
    | ~ spl9_241
    | ~ spl9_134
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2309,f2186,f1264,f2494,f2491,f2182])).

fof(f2491,plain,
    ( spl9_240
  <=> ! [X61] : ~ r2_hidden(X61,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f2494,plain,
    ( spl9_241
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_241])])).

fof(f1264,plain,
    ( spl9_134
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(sK2)))
        | ~ r2_hidden(X3,k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f2309,plain,
    ( ! [X61] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))
        | ~ r2_hidden(X61,k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_134
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1265])).

fof(f1265,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(sK2)))
        | ~ r2_hidden(X3,k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) )
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f2489,plain,
    ( spl9_239
    | ~ spl9_229
    | ~ spl9_182
    | ~ spl9_111
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2308,f2186,f1009,f2182,f2442,f2486])).

fof(f2486,plain,
    ( spl9_239
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_239])])).

fof(f2442,plain,
    ( spl9_229
  <=> v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_229])])).

fof(f2308,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5))
    | v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5),sK5))
    | ~ spl9_111
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1010])).

fof(f2484,plain,
    ( spl9_238
    | ~ spl9_220
    | ~ spl9_182
    | ~ spl9_110
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2307,f2186,f1005,f2182,f2403,f2481])).

fof(f2481,plain,
    ( spl9_238
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f2307,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK5))
    | ~ spl9_110
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1006])).

fof(f2479,plain,
    ( ~ spl9_182
    | ~ spl9_229
    | spl9_237
    | ~ spl9_105
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2306,f2186,f914,f2476,f2442,f2182])).

fof(f2476,plain,
    ( spl9_237
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_237])])).

fof(f2306,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5),sK4))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ spl9_105
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f915])).

fof(f2474,plain,
    ( ~ spl9_182
    | ~ spl9_220
    | spl9_236
    | ~ spl9_104
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2305,f2186,f910,f2471,f2403,f2182])).

fof(f2471,plain,
    ( spl9_236
  <=> v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_236])])).

fof(f2305,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ spl9_104
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f911])).

fof(f2469,plain,
    ( ~ spl9_182
    | spl9_235
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2304,f2186,f671,f2467,f2182])).

fof(f2467,plain,
    ( spl9_235
  <=> ! [X58,X60,X59] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X58,k2_tmap_1(sK0,sK1,sK5,sK3)),sK5))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_1(k5_relat_1(X58,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_235])])).

fof(f2304,plain,
    ( ! [X59,X60,X58] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X58,k2_tmap_1(sK0,sK1,sK5,sK3)),sK5))
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_1(k5_relat_1(X58,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X58) )
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f718])).

fof(f2465,plain,
    ( spl9_234
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2303,f2186,f2182,f2463])).

fof(f2463,plain,
    ( spl9_234
  <=> ! [X55,X56,X54,X57] :
        ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
        | ~ v1_xboole_0(k2_zfmisc_1(X55,u1_struct_0(sK1)))
        | ~ r2_hidden(X57,k5_relat_1(X54,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X54) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_234])])).

fof(f2303,plain,
    ( ! [X57,X54,X56,X55] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))
        | ~ v1_funct_1(X54)
        | ~ r2_hidden(X57,k5_relat_1(X54,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_xboole_0(k2_zfmisc_1(X55,u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f712])).

fof(f2461,plain,
    ( spl9_233
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2302,f2186,f2182,f2459])).

fof(f2459,plain,
    ( spl9_233
  <=> ! [X51,X53,X50,X52] :
        ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | m1_subset_1(X53,k2_zfmisc_1(X51,u1_struct_0(sK1)))
        | ~ r2_hidden(X53,k5_relat_1(X50,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X50) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_233])])).

fof(f2302,plain,
    ( ! [X52,X50,X53,X51] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ v1_funct_1(X50)
        | ~ r2_hidden(X53,k5_relat_1(X50,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | m1_subset_1(X53,k2_zfmisc_1(X51,u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f711])).

fof(f2457,plain,
    ( spl9_232
    | ~ spl9_182
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2301,f2186,f667,f2182,f2455])).

fof(f2455,plain,
    ( spl9_232
  <=> ! [X49,X48,X47] :
        ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X47,k2_tmap_1(sK0,sK1,sK5,sK3)),sK4))
        | ~ v1_funct_1(k5_relat_1(X47,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X47) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_232])])).

fof(f2301,plain,
    ( ! [X47,X48,X49] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_1(k5_relat_1(X47,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | v1_funct_1(k5_relat_1(k5_relat_1(X47,k2_tmap_1(sK0,sK1,sK5,sK3)),sK4)) )
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f697])).

fof(f2453,plain,
    ( ~ spl9_182
    | spl9_231
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2300,f2186,f2451,f2182])).

fof(f2451,plain,
    ( spl9_231
  <=> ! [X42,X44,X46,X41,X43,X45] :
        ( ~ v1_funct_1(X41)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),k5_relat_1(X44,X41)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_1(k5_relat_1(X44,X41))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_231])])).

fof(f2300,plain,
    ( ! [X45,X43,X41,X46,X44,X42] :
        ( ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ v1_funct_1(k5_relat_1(X44,X41))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),k5_relat_1(X44,X41)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f696])).

fof(f2449,plain,
    ( spl9_38
    | ~ spl9_201
    | ~ spl9_182
    | spl9_230
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2299,f2186,f2447,f2182,f2323,f331])).

fof(f331,plain,
    ( spl9_38
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f2447,plain,
    ( spl9_230
  <=> ! [X40,X36,X38,X37,X39] :
        ( ~ v1_funct_1(X36)
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),k5_relat_1(X39,X36)))
        | ~ v1_funct_2(k5_relat_1(X39,X36),u1_struct_0(sK1),X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_1(k5_relat_1(X39,X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X40)))
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_230])])).

fof(f2299,plain,
    ( ! [X39,X37,X38,X36,X40] :
        ( ~ v1_funct_1(X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X40)))
        | ~ v1_funct_1(k5_relat_1(X39,X36))
        | ~ v1_funct_2(k5_relat_1(X39,X36),u1_struct_0(sK1),X38)
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),k5_relat_1(X39,X36))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f690])).

fof(f2445,plain,
    ( spl9_229
    | ~ spl9_182
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2298,f2186,f671,f2182,f2442])).

fof(f2298,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK5))
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f672])).

fof(f2440,plain,
    ( spl9_220
    | ~ spl9_182
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2297,f2186,f667,f2182,f2403])).

fof(f2297,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f668])).

fof(f2439,plain,
    ( ~ spl9_182
    | spl9_228
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2296,f2186,f2437,f2182])).

fof(f2437,plain,
    ( spl9_228
  <=> ! [X34,X33,X35] :
        ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X33)
        | v1_funct_1(k5_relat_1(X33,k2_tmap_1(sK0,sK1,sK5,sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).

fof(f2296,plain,
    ( ! [X35,X33,X34] :
        ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | v1_funct_1(k5_relat_1(X33,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ v1_funct_1(X33) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f286])).

fof(f2435,plain,
    ( spl9_227
    | ~ spl9_182
    | ~ spl9_201
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2295,f2186,f2323,f2182,f2432])).

fof(f2432,plain,
    ( spl9_227
  <=> r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),k2_tmap_1(sK0,sK1,sK5,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_227])])).

fof(f2295,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f111])).

fof(f2430,plain,
    ( ~ spl9_201
    | ~ spl9_182
    | spl9_226
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2294,f2186,f2428,f2182,f2323])).

fof(f2428,plain,
    ( spl9_226
  <=> ! [X32] :
        ( ~ v1_funct_2(X32,u1_struct_0(sK3),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),X32)
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X32,k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_1(X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).

fof(f2294,plain,
    ( ! [X32] :
        ( ~ v1_funct_2(X32,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X32)
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X32,k2_tmap_1(sK0,sK1,sK5,sK3))
        | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),X32) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f103])).

fof(f2426,plain,
    ( ~ spl9_201
    | ~ spl9_182
    | spl9_225
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2293,f2186,f2424,f2182,f2323])).

fof(f2424,plain,
    ( spl9_225
  <=> ! [X31] :
        ( ~ v1_funct_2(X31,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X31,k2_tmap_1(sK0,sK1,sK5,sK3))
        | k2_tmap_1(sK0,sK1,sK5,sK3) = X31
        | ~ v1_funct_1(X31)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_225])])).

fof(f2293,plain,
    ( ! [X31] :
        ( ~ v1_funct_2(X31,u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(X31)
        | k2_tmap_1(sK0,sK1,sK5,sK3) = X31
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),X31,k2_tmap_1(sK0,sK1,sK5,sK3)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f102])).

fof(f2422,plain,
    ( spl9_224
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2292,f2186,f2182,f2420])).

fof(f2420,plain,
    ( spl9_224
  <=> ! [X30] : v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),X30)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_224])])).

fof(f2292,plain,
    ( ! [X30] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | v1_funct_1(k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK5,sK3),X30)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f99])).

fof(f2418,plain,
    ( spl9_221
    | ~ spl9_201
    | ~ spl9_182
    | spl9_223
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2291,f2186,f2416,f2182,f2323,f2408])).

fof(f2416,plain,
    ( spl9_223
  <=> ! [X29,X28] :
        ( ~ v1_funct_1(X28)
        | v1_funct_2(k5_relat_1(X28,k2_tmap_1(sK0,sK1,sK5,sK3)),X29,u1_struct_0(sK1))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X29,u1_struct_0(sK3))))
        | ~ v1_funct_2(X28,X29,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_223])])).

fof(f2291,plain,
    ( ! [X28,X29] :
        ( ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X29,u1_struct_0(sK3))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X29,u1_struct_0(sK3))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK3))
        | v1_funct_2(k5_relat_1(X28,k2_tmap_1(sK0,sK1,sK5,sK3)),X29,u1_struct_0(sK1)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f98])).

fof(f2414,plain,
    ( spl9_221
    | ~ spl9_201
    | ~ spl9_182
    | spl9_222
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2290,f2186,f2412,f2182,f2323,f2408])).

fof(f2412,plain,
    ( spl9_222
  <=> ! [X27,X26] :
        ( ~ v1_funct_1(X26)
        | v1_funct_1(k5_relat_1(X26,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X27,u1_struct_0(sK3))))
        | ~ v1_funct_2(X26,X27,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f2290,plain,
    ( ! [X26,X27] :
        ( ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X27,u1_struct_0(sK3))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X27,u1_struct_0(sK3))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK3))
        | v1_funct_1(k5_relat_1(X26,k2_tmap_1(sK0,sK1,sK5,sK3))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f97])).

fof(f2406,plain,
    ( ~ spl9_201
    | ~ spl9_182
    | spl9_220
    | ~ spl9_39
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2289,f2186,f335,f2403,f2182,f2323])).

fof(f335,plain,
    ( spl9_39
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v1_funct_1(k5_relat_1(X0,sK4))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f2289,plain,
    ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl9_39
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f336])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | v1_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1)) )
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f335])).

fof(f2401,plain,
    ( ~ spl9_201
    | ~ spl9_182
    | spl9_219
    | ~ spl9_46
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2288,f2186,f394,f2398,f2182,f2323])).

fof(f394,plain,
    ( spl9_46
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v1_funct_2(k5_relat_1(X0,sK4),X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2288,plain,
    ( v1_funct_2(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl9_46
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f395])).

fof(f395,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | v1_funct_2(k5_relat_1(X0,sK4),X1,u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f394])).

fof(f2396,plain,
    ( spl9_11
    | spl9_218
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2287,f2186,f2182,f249,f221,f138,f133,f128,f2323,f2394,f163])).

fof(f2394,plain,
    ( spl9_218
  <=> ! [X22,X25,X23,X24] :
        ( ~ m1_pre_topc(X22,sK3)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | v1_funct_1(k5_relat_1(X23,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X22))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).

fof(f2287,plain,
    ( ! [X24,X23,X25,X22] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X22,sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X22))
        | v1_funct_1(k5_relat_1(X23,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X22)))
        | ~ v1_funct_1(X23) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f813])).

fof(f2392,plain,
    ( ~ spl9_197
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_34
    | spl9_217
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2286,f2186,f671,f2390,f307,f2182,f2323,f2246])).

fof(f2390,plain,
    ( spl9_217
  <=> ! [X21] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X21),sK5))
        | ~ l1_struct_0(X21)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X21)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_217])])).

fof(f2286,plain,
    ( ! [X21] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X21),sK5))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X21))
        | ~ l1_struct_0(X21)
        | ~ l1_struct_0(sK3) )
    | ~ spl9_85
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f715])).

fof(f2388,plain,
    ( ~ spl9_197
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_34
    | spl9_216
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2285,f2186,f667,f2386,f307,f2182,f2323,f2246])).

fof(f2386,plain,
    ( spl9_216
  <=> ! [X20] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X20),sK4))
        | ~ l1_struct_0(X20)
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X20)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f2285,plain,
    ( ! [X20] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X20),sK4))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X20))
        | ~ l1_struct_0(X20)
        | ~ l1_struct_0(sK3) )
    | ~ spl9_84
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f676])).

fof(f2384,plain,
    ( ~ spl9_197
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_34
    | spl9_215
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2284,f2186,f2382,f307,f2182,f2323,f2246])).

fof(f2382,plain,
    ( spl9_215
  <=> ! [X16,X18,X17,X19] :
        ( ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X16))
        | ~ l1_struct_0(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X17)
        | v1_funct_1(k5_relat_1(X17,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X16))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_215])])).

fof(f2284,plain,
    ( ! [X19,X17,X18,X16] :
        ( ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X16))
        | v1_funct_1(k5_relat_1(X17,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X16)))
        | ~ v1_funct_1(X17)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(sK3) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f661])).

fof(f2380,plain,
    ( spl9_11
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | spl9_214
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2283,f2186,f2182,f2378,f249,f221,f138,f133,f128,f2323,f163])).

fof(f2378,plain,
    ( spl9_214
  <=> ! [X15,X14] :
        ( ~ r2_hidden(X14,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X15))
        | ~ m1_pre_topc(X15,sK3)
        | m1_subset_1(X14,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f2283,plain,
    ( ! [X14,X15] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ r2_hidden(X14,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X15))
        | m1_subset_1(X14,k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X15,sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f658])).

fof(f2376,plain,
    ( spl9_11
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_212
    | spl9_213
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2282,f2186,f2182,f2374,f2370,f249,f221,f138,f133,f128,f2323,f163])).

fof(f2374,plain,
    ( spl9_213
  <=> ! [X13,X12] :
        ( ~ r2_hidden(X12,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | ~ m1_pre_topc(X13,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_213])])).

fof(f2282,plain,
    ( ! [X12,X13] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ r2_hidden(X12,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X13))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X13,sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f655])).

fof(f655,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X4,k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f283,f88])).

fof(f283,plain,(
    ! [X14,X17,X15,X18,X16] :
      ( ~ r2_hidden(X17,k2_partfun1(X15,X16,X14,X18))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | ~ v1_xboole_0(k2_zfmisc_1(X15,X16)) ) ),
    inference(resolution,[],[f100,f92])).

fof(f2368,plain,
    ( ~ spl9_197
    | spl9_211
    | ~ spl9_34
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2281,f2186,f2182,f2323,f307,f2366,f2246])).

fof(f2366,plain,
    ( spl9_211
  <=> ! [X11,X10] :
        ( ~ l1_struct_0(X10)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK1)))
        | ~ r2_hidden(X11,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_211])])).

fof(f2281,plain,
    ( ! [X10,X11] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X10)
        | ~ l1_struct_0(sK3)
        | ~ r2_hidden(X11,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X10))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f375])).

fof(f2364,plain,
    ( ~ spl9_197
    | spl9_210
    | ~ spl9_34
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2280,f2186,f2182,f2323,f307,f2362,f2246])).

fof(f2362,plain,
    ( spl9_210
  <=> ! [X9,X8] :
        ( ~ l1_struct_0(X8)
        | m1_subset_1(X9,k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1)))
        | ~ r2_hidden(X9,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f2280,plain,
    ( ! [X8,X9] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X8)
        | ~ l1_struct_0(sK3)
        | ~ r2_hidden(X9,k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X8))
        | m1_subset_1(X9,k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(sK1))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f374])).

fof(f2360,plain,
    ( ~ spl9_16
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | spl9_11
    | spl9_209
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2279,f2186,f2358,f163,f249,f221,f138,f133,f128,f2182,f2323,f188])).

fof(f188,plain,
    ( spl9_16
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f2358,plain,
    ( spl9_209
  <=> ! [X7,X6] :
        ( ~ v2_pre_topc(X6)
        | v5_pre_topc(k5_relat_1(X7,k2_tmap_1(sK0,sK1,sK5,sK3)),X6,sK1)
        | v2_struct_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X7,X6,sK3)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK3))
        | ~ l1_pre_topc(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_209])])).

fof(f2279,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(sK3))
        | ~ v5_pre_topc(X7,X6,sK3)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(sK3))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
        | v2_struct_0(X6)
        | v5_pre_topc(k5_relat_1(X7,k2_tmap_1(sK0,sK1,sK5,sK3)),X6,sK1) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f91])).

fof(f2356,plain,
    ( ~ spl9_16
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | spl9_11
    | spl9_208
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2278,f2186,f2354,f163,f249,f221,f138,f133,f128,f2182,f2323,f188])).

fof(f2354,plain,
    ( spl9_208
  <=> ! [X5,X4] :
        ( ~ v2_pre_topc(X4)
        | v1_funct_2(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,sK3)),u1_struct_0(X4),u1_struct_0(sK1))
        | v2_struct_0(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X5,X4,sK3)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ l1_pre_topc(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_208])])).

fof(f2278,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK3))
        | ~ v5_pre_topc(X5,X4,sK3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
        | v2_struct_0(X4)
        | v1_funct_2(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,sK3)),u1_struct_0(X4),u1_struct_0(sK1)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f90])).

fof(f2352,plain,
    ( ~ spl9_16
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | spl9_11
    | spl9_207
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2277,f2186,f2350,f163,f249,f221,f138,f133,f128,f2182,f2323,f188])).

fof(f2350,plain,
    ( spl9_207
  <=> ! [X3,X2] :
        ( ~ v2_pre_topc(X2)
        | v1_funct_1(k5_relat_1(X3,k2_tmap_1(sK0,sK1,sK5,sK3)))
        | v2_struct_0(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(X3,X2,sK3)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK3))
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_207])])).

fof(f2277,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK3))
        | ~ v5_pre_topc(X3,X2,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
        | v2_struct_0(X2)
        | v1_funct_1(k5_relat_1(X3,k2_tmap_1(sK0,sK1,sK5,sK3))) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f89])).

fof(f2348,plain,
    ( spl9_206
    | ~ spl9_197
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_34
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2276,f2186,f307,f2182,f2323,f2246,f2346])).

fof(f2346,plain,
    ( spl9_206
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_206])])).

fof(f2276,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ l1_struct_0(sK3)
        | ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X1)) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f85])).

fof(f2344,plain,
    ( ~ spl9_22
    | ~ spl9_201
    | ~ spl9_182
    | ~ spl9_16
    | ~ spl9_27
    | spl9_11
    | spl9_205
    | ~ spl9_52
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2275,f2186,f436,f2341,f163,f249,f188,f2182,f2323,f221])).

fof(f436,plain,
    ( spl9_52
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | v5_pre_topc(k5_relat_1(X1,sK4),X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f2275,plain,
    ( v5_pre_topc(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK3)
    | ~ spl9_52
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f437])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v5_pre_topc(k5_relat_1(X1,sK4),X0,sK2)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0) )
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f436])).

fof(f2339,plain,
    ( ~ spl9_202
    | spl9_203
    | spl9_11
    | ~ spl9_204
    | ~ spl9_201
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_182
    | ~ spl9_197
    | ~ spl9_132
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2274,f2186,f1237,f2246,f2182,f249,f221,f2323,f2336,f163,f2332,f2328])).

fof(f2328,plain,
    ( spl9_202
  <=> v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_202])])).

fof(f2332,plain,
    ( spl9_203
  <=> v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_203])])).

fof(f2336,plain,
    ( spl9_204
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).

fof(f1237,plain,
    ( spl9_132
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,X1)
        | v2_struct_0(X1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK1,X0,X1),sK4))
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f2274,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK3)
    | v2_struct_0(sK3)
    | v1_funct_1(k5_relat_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),sK3),sK4))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),sK3))
    | ~ spl9_132
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f1238])).

fof(f1238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,X1)
        | v2_struct_0(X1)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK1,X0,X1),sK4))
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X0,X1)) )
    | ~ spl9_132 ),
    inference(avatar_component_clause,[],[f1237])).

fof(f2326,plain,
    ( spl9_11
    | spl9_200
    | ~ spl9_201
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_22
    | ~ spl9_27
    | ~ spl9_34
    | ~ spl9_182
    | ~ spl9_37
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_183 ),
    inference(avatar_split_clause,[],[f2273,f2186,f208,f203,f198,f319,f2182,f307,f249,f221,f138,f133,f128,f2323,f2320,f163])).

fof(f2320,plain,
    ( spl9_200
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X0))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_200])])).

fof(f2273,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
        | ~ l1_struct_0(sK1)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | v1_funct_1(k2_tmap_1(sK3,sK1,k2_tmap_1(sK0,sK1,sK5,sK3),X0))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_183 ),
    inference(resolution,[],[f2187,f787])).

fof(f787,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ l1_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(k2_tmap_1(X2,X1,X3,X0),u1_struct_0(X0),u1_struct_0(X1))
      | v1_funct_1(k2_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f109,f786])).

fof(f786,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ l1_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(k2_tmap_1(X2,X1,X3,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f785])).

fof(f785,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,k2_tmap_1(X2,X1,X3,X0),X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ l1_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(k2_tmap_1(X2,X1,X3,X0))
      | ~ v1_funct_2(k2_tmap_1(X2,X1,X3,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(k2_tmap_1(X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f373,f88])).

fof(f373,plain,(
    ! [X30,X28,X26,X29,X27] :
      ( v1_funct_1(k2_partfun1(u1_struct_0(X29),u1_struct_0(X26),k2_tmap_1(X28,X26,X27,X29),X30))
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X28),u1_struct_0(X26))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
      | ~ l1_struct_0(X29)
      | ~ l1_struct_0(X28)
      | ~ v1_funct_1(k2_tmap_1(X28,X26,X27,X29))
      | ~ l1_struct_0(X26) ) ),
    inference(resolution,[],[f87,f99])).

fof(f109,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2272,plain,
    ( ~ spl9_22
    | spl9_197 ),
    inference(avatar_split_clause,[],[f2271,f2246,f221])).

fof(f2271,plain,
    ( ~ l1_pre_topc(sK3)
    | spl9_197 ),
    inference(resolution,[],[f2248,f109])).

fof(f2248,plain,
    ( ~ l1_struct_0(sK3)
    | spl9_197 ),
    inference(avatar_component_clause,[],[f2246])).

fof(f2270,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_199
    | ~ spl9_132 ),
    inference(avatar_split_clause,[],[f2261,f1237,f2268,f138,f133,f128])).

fof(f2268,plain,
    ( spl9_199
  <=> ! [X3,X5,X4] :
        ( ~ l1_struct_0(X3)
        | ~ m1_pre_topc(X5,X3)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3),sK4))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,X5),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_199])])).

fof(f2261,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,X5))
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,X5),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,X3)
        | v2_struct_0(X3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3),sK4))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X5,X3) )
    | ~ spl9_132 ),
    inference(duplicate_literal_removal,[],[f2254])).

fof(f2254,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_struct_0(X3)
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,X4,X5))
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_funct_2(k2_tmap_1(X3,sK1,X4,X5),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,X3)
        | v2_struct_0(X3)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3),sK4))
        | ~ v1_funct_1(k2_tmap_1(X3,sK1,k2_tmap_1(X3,sK1,X4,X5),X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(X4)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_pre_topc(X5,X3)
        | v2_struct_0(X3) )
    | ~ spl9_132 ),
    inference(resolution,[],[f1238,f400])).

fof(f2266,plain,
    ( ~ spl9_34
    | spl9_198
    | ~ spl9_132 ),
    inference(avatar_split_clause,[],[f2262,f1237,f2264,f307])).

fof(f2264,plain,
    ( spl9_198
  <=> ! [X1,X0,X2] :
        ( ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0),sK4))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK1,X2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).

fof(f2262,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X2,X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK1,X2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,X0)
        | v2_struct_0(X0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0),sK4))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ l1_struct_0(X1) )
    | ~ spl9_132 ),
    inference(duplicate_literal_removal,[],[f2253])).

fof(f2253,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X2,X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k2_tmap_1(X1,sK1,X2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,X0)
        | v2_struct_0(X0)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0),sK4))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,k2_tmap_1(X1,sK1,X2,X0),X0))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1) )
    | ~ spl9_132 ),
    inference(resolution,[],[f1238,f87])).

fof(f2251,plain,
    ( ~ spl9_37
    | ~ spl9_197
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | spl9_183 ),
    inference(avatar_split_clause,[],[f2250,f2186,f307,f208,f203,f198,f2246,f319])).

fof(f2250,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl9_183 ),
    inference(resolution,[],[f2188,f87])).

fof(f2188,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl9_183 ),
    inference(avatar_component_clause,[],[f2186])).

fof(f2249,plain,
    ( ~ spl9_197
    | ~ spl9_36
    | spl9_182 ),
    inference(avatar_split_clause,[],[f2243,f2182,f316,f2246])).

fof(f316,plain,
    ( spl9_36
  <=> ! [X1] :
        ( ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f2243,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl9_36
    | spl9_182 ),
    inference(resolution,[],[f2184,f317])).

fof(f317,plain,
    ( ! [X1] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ l1_struct_0(X1) )
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f316])).

fof(f2184,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | spl9_182 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2244,plain,
    ( ~ spl9_10
    | ~ spl9_48
    | spl9_182 ),
    inference(avatar_split_clause,[],[f2242,f2182,f406,f158])).

fof(f406,plain,
    ( spl9_48
  <=> ! [X1] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f2242,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl9_48
    | spl9_182 ),
    inference(resolution,[],[f2184,f407])).

fof(f407,plain,
    ( ! [X1] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f406])).

fof(f2241,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_196
    | ~ spl9_95 ),
    inference(avatar_split_clause,[],[f2123,f831,f2239,f133,f128,f153,f148,f143,f138])).

fof(f2239,plain,
    ( spl9_196
  <=> ! [X359,X357,X358,X356] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),sK4)
        | ~ v1_funct_2(X358,u1_struct_0(X356),u1_struct_0(sK2))
        | ~ m1_subset_1(X357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X356))))
        | ~ v1_funct_2(X357,u1_struct_0(sK1),u1_struct_0(X356))
        | ~ v1_funct_1(X357)
        | v2_struct_0(X359)
        | ~ l1_pre_topc(X356)
        | ~ v2_pre_topc(X356)
        | v2_struct_0(X356)
        | ~ v1_funct_1(k2_tmap_1(sK1,X356,X357,X359))
        | ~ m1_subset_1(X358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X356),u1_struct_0(sK2))))
        | ~ v1_funct_1(X358)
        | ~ m1_subset_1(k2_tmap_1(sK1,X356,X357,X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(X356))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X359,sK1)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | sK4 = k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(sK1),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_196])])).

fof(f831,plain,
    ( spl9_95
  <=> ! [X40,X41] :
        ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X40,X41),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X40,X41))
        | sK4 = k2_tmap_1(sK1,sK2,X40,X41)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X40,X41),sK4)
        | ~ m1_pre_topc(X41,sK1)
        | ~ v1_funct_2(X40,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X40) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f2123,plain,
    ( ! [X356,X358,X357,X359] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),sK4)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358))
        | sK4 = k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X359,sK1)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,X356,X357,X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(X356))))
        | ~ v1_funct_1(X358)
        | ~ m1_subset_1(X358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X356),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,X356,X357,X359))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X356)
        | ~ v2_pre_topc(X356)
        | ~ l1_pre_topc(X356)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(X359)
        | ~ v1_funct_1(X357)
        | ~ v1_funct_2(X357,u1_struct_0(sK1),u1_struct_0(X356))
        | ~ m1_subset_1(X357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X356))))
        | ~ v1_funct_2(X358,u1_struct_0(X356),u1_struct_0(sK2))
        | v2_struct_0(sK1) )
    | ~ spl9_95 ),
    inference(duplicate_literal_removal,[],[f2048])).

fof(f2048,plain,
    ( ! [X356,X358,X357,X359] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),sK4)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358))
        | sK4 = k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X359,sK1)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X359),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),k2_tmap_1(sK1,X356,X357,X359),X358),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X356),u1_struct_0(X356),u1_struct_0(sK2),X357,X358),X359),u1_struct_0(X359),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,X356,X357,X359),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X359),u1_struct_0(X356))))
        | ~ v1_funct_1(X358)
        | ~ m1_subset_1(X358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X356),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,X356,X357,X359))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X356)
        | ~ v2_pre_topc(X356)
        | ~ l1_pre_topc(X356)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(X359)
        | ~ m1_pre_topc(X359,sK1)
        | ~ v1_funct_1(X357)
        | ~ v1_funct_2(X357,u1_struct_0(sK1),u1_struct_0(X356))
        | ~ m1_subset_1(X357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X356))))
        | ~ v1_funct_2(X358,u1_struct_0(X356),u1_struct_0(sK2))
        | v2_struct_0(sK1) )
    | ~ spl9_95 ),
    inference(superposition,[],[f832,f951])).

fof(f832,plain,
    ( ! [X41,X40] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X40,X41),sK4)
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X40,X41),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X40,X41))
        | sK4 = k2_tmap_1(sK1,sK2,X40,X41)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X41,sK1)
        | ~ v1_funct_2(X40,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X40) )
    | ~ spl9_95 ),
    inference(avatar_component_clause,[],[f831])).

fof(f2237,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_195
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f2124,f827,f2235,f133,f128,f153,f148,f143,f138])).

fof(f2235,plain,
    ( spl9_195
  <=> ! [X355,X353,X354,X352] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ v1_funct_2(X354,u1_struct_0(X352),u1_struct_0(sK2))
        | ~ m1_subset_1(X353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X352))))
        | ~ v1_funct_2(X353,u1_struct_0(sK1),u1_struct_0(X352))
        | ~ v1_funct_1(X353)
        | v2_struct_0(X355)
        | ~ l1_pre_topc(X352)
        | ~ v2_pre_topc(X352)
        | v2_struct_0(X352)
        | ~ v1_funct_1(k2_tmap_1(sK1,X352,X353,X355))
        | ~ m1_subset_1(X354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X352),u1_struct_0(sK2))))
        | ~ v1_funct_1(X354)
        | ~ m1_subset_1(k2_tmap_1(sK1,X352,X353,X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(X352))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X355,sK1)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),sK4)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(sK1),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_195])])).

fof(f827,plain,
    ( spl9_94
  <=> ! [X38,X39] :
        ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X38,X39),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X38,X39))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X38,X39),sK4)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X38,X39))
        | ~ m1_pre_topc(X39,sK1)
        | ~ v1_funct_2(X38,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X38) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f2124,plain,
    ( ! [X352,X354,X353,X355] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),sK4)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X355,sK1)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,X352,X353,X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(X352))))
        | ~ v1_funct_1(X354)
        | ~ m1_subset_1(X354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X352),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,X352,X353,X355))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X352)
        | ~ v2_pre_topc(X352)
        | ~ l1_pre_topc(X352)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(X355)
        | ~ v1_funct_1(X353)
        | ~ v1_funct_2(X353,u1_struct_0(sK1),u1_struct_0(X352))
        | ~ m1_subset_1(X353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X352))))
        | ~ v1_funct_2(X354,u1_struct_0(X352),u1_struct_0(sK2))
        | v2_struct_0(sK1) )
    | ~ spl9_94 ),
    inference(duplicate_literal_removal,[],[f2047])).

fof(f2047,plain,
    ( ! [X352,X354,X353,X355] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),sK4)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X355,sK1)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X355),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),k2_tmap_1(sK1,X352,X353,X355),X354),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355))
        | ~ m1_subset_1(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(sK2))))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,k1_partfun1(u1_struct_0(sK1),u1_struct_0(X352),u1_struct_0(X352),u1_struct_0(sK2),X353,X354),X355),u1_struct_0(X355),u1_struct_0(sK2))
        | ~ m1_subset_1(k2_tmap_1(sK1,X352,X353,X355),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X355),u1_struct_0(X352))))
        | ~ v1_funct_1(X354)
        | ~ m1_subset_1(X354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X352),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,X352,X353,X355))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X352)
        | ~ v2_pre_topc(X352)
        | ~ l1_pre_topc(X352)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | v2_struct_0(X355)
        | ~ m1_pre_topc(X355,sK1)
        | ~ v1_funct_1(X353)
        | ~ v1_funct_2(X353,u1_struct_0(sK1),u1_struct_0(X352))
        | ~ m1_subset_1(X353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X352))))
        | ~ v1_funct_2(X354,u1_struct_0(X352),u1_struct_0(sK2))
        | v2_struct_0(sK1) )
    | ~ spl9_94 ),
    inference(superposition,[],[f828,f951])).

fof(f828,plain,
    ( ! [X39,X38] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X38,X39))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X38,X39),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X38,X39))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X38,X39),sK4)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X39,sK1)
        | ~ v1_funct_2(X38,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X38) )
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f827])).

fof(f2233,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_194
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f2132,f843,f2231,f138,f133,f128])).

fof(f2231,plain,
    ( spl9_194
  <=> ! [X319,X317,X320,X318,X316] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),sK4),u1_struct_0(X316),u1_struct_0(sK2))
        | ~ v1_funct_2(X319,u1_struct_0(X317),u1_struct_0(sK1))
        | ~ m1_subset_1(X318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(X317))))
        | ~ v1_funct_2(X318,u1_struct_0(X316),u1_struct_0(X317))
        | ~ v1_funct_1(X318)
        | v2_struct_0(X320)
        | ~ l1_pre_topc(X317)
        | ~ v2_pre_topc(X317)
        | v2_struct_0(X317)
        | ~ v1_funct_1(k2_tmap_1(X316,X317,X318,X320))
        | ~ m1_subset_1(X319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X317),u1_struct_0(sK1))))
        | ~ v1_funct_1(X319)
        | ~ m1_subset_1(k2_tmap_1(X316,X317,X318,X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(X317))))
        | ~ v1_funct_2(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319))
        | ~ v2_pre_topc(X316)
        | ~ l1_pre_topc(X316)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),u1_struct_0(X316),u1_struct_0(sK1))
        | ~ m1_pre_topc(X320,X316)
        | v2_struct_0(X316)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(sK1))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X316),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_194])])).

fof(f843,plain,
    ( spl9_98
  <=> ! [X46,X48,X47] :
        ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X47,sK1,X46,X48),u1_struct_0(X47),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X47,sK1,X46,X48))
        | v1_funct_2(k5_relat_1(k2_tmap_1(X47,sK1,X46,X48),sK4),u1_struct_0(X47),u1_struct_0(sK2))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X48,X47)
        | ~ v1_funct_2(X46,u1_struct_0(X47),u1_struct_0(sK1))
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X47)
        | ~ v1_funct_1(X46) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f2132,plain,
    ( ! [X316,X318,X320,X317,X319] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),sK4),u1_struct_0(X316),u1_struct_0(sK2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X316),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(sK1))))
        | v2_struct_0(X316)
        | ~ m1_pre_topc(X320,X316)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),u1_struct_0(X316),u1_struct_0(sK1))
        | ~ l1_pre_topc(X316)
        | ~ v2_pre_topc(X316)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320))
        | ~ m1_subset_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X316,X317,X318,X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(X317))))
        | ~ v1_funct_1(X319)
        | ~ m1_subset_1(X319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X317),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X316,X317,X318,X320))
        | v2_struct_0(X317)
        | ~ v2_pre_topc(X317)
        | ~ l1_pre_topc(X317)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X320)
        | ~ v1_funct_1(X318)
        | ~ v1_funct_2(X318,u1_struct_0(X316),u1_struct_0(X317))
        | ~ m1_subset_1(X318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(X317))))
        | ~ v1_funct_2(X319,u1_struct_0(X317),u1_struct_0(sK1)) )
    | ~ spl9_98 ),
    inference(duplicate_literal_removal,[],[f2039])).

fof(f2039,plain,
    ( ! [X316,X318,X320,X317,X319] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),sK4),u1_struct_0(X316),u1_struct_0(sK2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X316),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(sK1))))
        | v2_struct_0(X316)
        | ~ m1_pre_topc(X320,X316)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),u1_struct_0(X316),u1_struct_0(sK1))
        | ~ l1_pre_topc(X316)
        | ~ v2_pre_topc(X316)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X320),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),k2_tmap_1(X316,X317,X318,X320),X319),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320))
        | ~ m1_subset_1(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X316,sK1,k1_partfun1(u1_struct_0(X316),u1_struct_0(X317),u1_struct_0(X317),u1_struct_0(sK1),X318,X319),X320),u1_struct_0(X320),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X316,X317,X318,X320),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X320),u1_struct_0(X317))))
        | ~ v1_funct_1(X319)
        | ~ m1_subset_1(X319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X317),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X316,X317,X318,X320))
        | ~ v2_pre_topc(X316)
        | ~ l1_pre_topc(X316)
        | v2_struct_0(X317)
        | ~ v2_pre_topc(X317)
        | ~ l1_pre_topc(X317)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X320)
        | ~ m1_pre_topc(X320,X316)
        | ~ v1_funct_1(X318)
        | ~ v1_funct_2(X318,u1_struct_0(X316),u1_struct_0(X317))
        | ~ m1_subset_1(X318,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X316),u1_struct_0(X317))))
        | ~ v1_funct_2(X319,u1_struct_0(X317),u1_struct_0(sK1))
        | v2_struct_0(X316) )
    | ~ spl9_98 ),
    inference(superposition,[],[f844,f951])).

fof(f844,plain,
    ( ! [X47,X48,X46] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X47,sK1,X46,X48),sK4),u1_struct_0(X47),u1_struct_0(sK2))
        | ~ v1_funct_2(k2_tmap_1(X47,sK1,X46,X48),u1_struct_0(X47),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X47,sK1,X46,X48))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK1))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X48,X47)
        | ~ v1_funct_2(X46,u1_struct_0(X47),u1_struct_0(sK1))
        | ~ l1_pre_topc(X47)
        | ~ v2_pre_topc(X47)
        | ~ v1_funct_1(X46) )
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f843])).

fof(f2229,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_193
    | ~ spl9_93 ),
    inference(avatar_split_clause,[],[f2133,f823,f2227,f138,f133,f128])).

fof(f2227,plain,
    ( spl9_193
  <=> ! [X311,X314,X312,X315,X313] :
        ( v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),sK4),X311,sK2)
        | ~ v1_funct_2(X314,u1_struct_0(X312),u1_struct_0(sK1))
        | ~ m1_subset_1(X313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(X312))))
        | ~ v1_funct_2(X313,u1_struct_0(X311),u1_struct_0(X312))
        | ~ v1_funct_1(X313)
        | v2_struct_0(X315)
        | ~ l1_pre_topc(X312)
        | ~ v2_pre_topc(X312)
        | v2_struct_0(X312)
        | ~ v1_funct_1(k2_tmap_1(X311,X312,X313,X315))
        | ~ m1_subset_1(X314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X312),u1_struct_0(sK1))))
        | ~ v1_funct_1(X314)
        | ~ m1_subset_1(k2_tmap_1(X311,X312,X313,X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(X312))))
        | ~ v1_funct_2(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314))
        | ~ v2_pre_topc(X311)
        | ~ l1_pre_topc(X311)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),u1_struct_0(X311),u1_struct_0(sK1))
        | ~ m1_pre_topc(X315,X311)
        | v2_struct_0(X311)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),X311,sK1)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X311),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_193])])).

fof(f823,plain,
    ( spl9_93
  <=> ! [X36,X35,X37] :
        ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X36,sK1,X35,X37),u1_struct_0(X36),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X36,sK1,X35,X37))
        | ~ v5_pre_topc(k2_tmap_1(X36,sK1,X35,X37),X36,sK1)
        | v5_pre_topc(k5_relat_1(k2_tmap_1(X36,sK1,X35,X37),sK4),X36,sK2)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v1_funct_2(X35,u1_struct_0(X36),u1_struct_0(sK1))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X36)
        | ~ v1_funct_1(X35) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f2133,plain,
    ( ! [X313,X315,X312,X314,X311] :
        ( v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),sK4),X311,sK2)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X311),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314))
        | ~ v5_pre_topc(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),X311,sK1)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(sK1))))
        | v2_struct_0(X311)
        | ~ m1_pre_topc(X315,X311)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),u1_struct_0(X311),u1_struct_0(sK1))
        | ~ l1_pre_topc(X311)
        | ~ v2_pre_topc(X311)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315))
        | ~ m1_subset_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X311,X312,X313,X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(X312))))
        | ~ v1_funct_1(X314)
        | ~ m1_subset_1(X314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X312),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X311,X312,X313,X315))
        | v2_struct_0(X312)
        | ~ v2_pre_topc(X312)
        | ~ l1_pre_topc(X312)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X315)
        | ~ v1_funct_1(X313)
        | ~ v1_funct_2(X313,u1_struct_0(X311),u1_struct_0(X312))
        | ~ m1_subset_1(X313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(X312))))
        | ~ v1_funct_2(X314,u1_struct_0(X312),u1_struct_0(sK1)) )
    | ~ spl9_93 ),
    inference(duplicate_literal_removal,[],[f2038])).

fof(f2038,plain,
    ( ! [X313,X315,X312,X314,X311] :
        ( v5_pre_topc(k5_relat_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),sK4),X311,sK2)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X311),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314))
        | ~ v5_pre_topc(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),X311,sK1)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(sK1))))
        | v2_struct_0(X311)
        | ~ m1_pre_topc(X315,X311)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),u1_struct_0(X311),u1_struct_0(sK1))
        | ~ l1_pre_topc(X311)
        | ~ v2_pre_topc(X311)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X315),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),k2_tmap_1(X311,X312,X313,X315),X314),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315))
        | ~ m1_subset_1(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X311,sK1,k1_partfun1(u1_struct_0(X311),u1_struct_0(X312),u1_struct_0(X312),u1_struct_0(sK1),X313,X314),X315),u1_struct_0(X315),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(X311,X312,X313,X315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X315),u1_struct_0(X312))))
        | ~ v1_funct_1(X314)
        | ~ m1_subset_1(X314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X312),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X311,X312,X313,X315))
        | ~ v2_pre_topc(X311)
        | ~ l1_pre_topc(X311)
        | v2_struct_0(X312)
        | ~ v2_pre_topc(X312)
        | ~ l1_pre_topc(X312)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X315)
        | ~ m1_pre_topc(X315,X311)
        | ~ v1_funct_1(X313)
        | ~ v1_funct_2(X313,u1_struct_0(X311),u1_struct_0(X312))
        | ~ m1_subset_1(X313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X311),u1_struct_0(X312))))
        | ~ v1_funct_2(X314,u1_struct_0(X312),u1_struct_0(sK1))
        | v2_struct_0(X311) )
    | ~ spl9_93 ),
    inference(superposition,[],[f824,f951])).

fof(f824,plain,
    ( ! [X37,X35,X36] :
        ( v5_pre_topc(k5_relat_1(k2_tmap_1(X36,sK1,X35,X37),sK4),X36,sK2)
        | ~ v1_funct_2(k2_tmap_1(X36,sK1,X35,X37),u1_struct_0(X36),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X36,sK1,X35,X37))
        | ~ v5_pre_topc(k2_tmap_1(X36,sK1,X35,X37),X36,sK1)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(sK1))))
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v1_funct_2(X35,u1_struct_0(X36),u1_struct_0(sK1))
        | ~ l1_pre_topc(X36)
        | ~ v2_pre_topc(X36)
        | ~ v1_funct_1(X35) )
    | ~ spl9_93 ),
    inference(avatar_component_clause,[],[f823])).

fof(f2225,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_192
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f2138,f851,f2223,f123,f118,f113])).

fof(f2223,plain,
    ( spl9_192
  <=> ! [X286,X289,X287,X290,X288] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),sK5),u1_struct_0(X286),u1_struct_0(sK1))
        | ~ v1_funct_2(X289,u1_struct_0(X287),u1_struct_0(sK0))
        | ~ m1_subset_1(X288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(X287))))
        | ~ v1_funct_2(X288,u1_struct_0(X286),u1_struct_0(X287))
        | ~ v1_funct_1(X288)
        | v2_struct_0(X290)
        | ~ l1_pre_topc(X287)
        | ~ v2_pre_topc(X287)
        | v2_struct_0(X287)
        | ~ v1_funct_1(k2_tmap_1(X286,X287,X288,X290))
        | ~ m1_subset_1(X289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X287),u1_struct_0(sK0))))
        | ~ v1_funct_1(X289)
        | ~ m1_subset_1(k2_tmap_1(X286,X287,X288,X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(X287))))
        | ~ v1_funct_2(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289))
        | ~ v2_pre_topc(X286)
        | ~ l1_pre_topc(X286)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),u1_struct_0(X286),u1_struct_0(sK0))
        | ~ m1_pre_topc(X290,X286)
        | v2_struct_0(X286)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(sK0))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X286),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_192])])).

fof(f851,plain,
    ( spl9_100
  <=> ! [X53,X52,X54] :
        ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X53,sK0,X52,X54),u1_struct_0(X53),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X53,sK0,X52,X54))
        | v1_funct_2(k5_relat_1(k2_tmap_1(X53,sK0,X52,X54),sK5),u1_struct_0(X53),u1_struct_0(sK1))
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X54,X53)
        | ~ v1_funct_2(X52,u1_struct_0(X53),u1_struct_0(sK0))
        | ~ l1_pre_topc(X53)
        | ~ v2_pre_topc(X53)
        | ~ v1_funct_1(X52) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f2138,plain,
    ( ! [X288,X290,X287,X289,X286] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),sK5),u1_struct_0(X286),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X286),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(sK0))))
        | v2_struct_0(X286)
        | ~ m1_pre_topc(X290,X286)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),u1_struct_0(X286),u1_struct_0(sK0))
        | ~ l1_pre_topc(X286)
        | ~ v2_pre_topc(X286)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290))
        | ~ m1_subset_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X286,X287,X288,X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(X287))))
        | ~ v1_funct_1(X289)
        | ~ m1_subset_1(X289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X287),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X286,X287,X288,X290))
        | v2_struct_0(X287)
        | ~ v2_pre_topc(X287)
        | ~ l1_pre_topc(X287)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X290)
        | ~ v1_funct_1(X288)
        | ~ v1_funct_2(X288,u1_struct_0(X286),u1_struct_0(X287))
        | ~ m1_subset_1(X288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(X287))))
        | ~ v1_funct_2(X289,u1_struct_0(X287),u1_struct_0(sK0)) )
    | ~ spl9_100 ),
    inference(duplicate_literal_removal,[],[f2033])).

fof(f2033,plain,
    ( ! [X288,X290,X287,X289,X286] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),sK5),u1_struct_0(X286),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X286),u1_struct_0(sK0))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(sK0))))
        | v2_struct_0(X286)
        | ~ m1_pre_topc(X290,X286)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),u1_struct_0(X286),u1_struct_0(sK0))
        | ~ l1_pre_topc(X286)
        | ~ v2_pre_topc(X286)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X290),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),k2_tmap_1(X286,X287,X288,X290),X289),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290))
        | ~ m1_subset_1(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X286,sK0,k1_partfun1(u1_struct_0(X286),u1_struct_0(X287),u1_struct_0(X287),u1_struct_0(sK0),X288,X289),X290),u1_struct_0(X290),u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tmap_1(X286,X287,X288,X290),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X290),u1_struct_0(X287))))
        | ~ v1_funct_1(X289)
        | ~ m1_subset_1(X289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X287),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X286,X287,X288,X290))
        | ~ v2_pre_topc(X286)
        | ~ l1_pre_topc(X286)
        | v2_struct_0(X287)
        | ~ v2_pre_topc(X287)
        | ~ l1_pre_topc(X287)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X290)
        | ~ m1_pre_topc(X290,X286)
        | ~ v1_funct_1(X288)
        | ~ v1_funct_2(X288,u1_struct_0(X286),u1_struct_0(X287))
        | ~ m1_subset_1(X288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X286),u1_struct_0(X287))))
        | ~ v1_funct_2(X289,u1_struct_0(X287),u1_struct_0(sK0))
        | v2_struct_0(X286) )
    | ~ spl9_100 ),
    inference(superposition,[],[f852,f951])).

fof(f852,plain,
    ( ! [X54,X52,X53] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X53,sK0,X52,X54),sK5),u1_struct_0(X53),u1_struct_0(sK1))
        | ~ v1_funct_2(k2_tmap_1(X53,sK0,X52,X54),u1_struct_0(X53),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X53,sK0,X52,X54))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(sK0))))
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X54,X53)
        | ~ v1_funct_2(X52,u1_struct_0(X53),u1_struct_0(sK0))
        | ~ l1_pre_topc(X53)
        | ~ v2_pre_topc(X53)
        | ~ v1_funct_1(X52) )
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f851])).

fof(f2221,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_191
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f2173,f839,f2219,f118,f113,f138,f133,f128,f123])).

fof(f2219,plain,
    ( spl9_191
  <=> ! [X5,X7,X4,X6] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),sK5)
        | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ v1_funct_1(X5)
        | v2_struct_0(X7)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,X7))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X4))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X7,sK0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | sK5 = k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(sK0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_191])])).

fof(f839,plain,
    ( spl9_97
  <=> ! [X44,X45] :
        ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X44,X45),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X44,X45))
        | sK5 = k2_tmap_1(sK0,sK1,X44,X45)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X44,X45),sK5)
        | ~ m1_pre_topc(X45,sK0)
        | ~ v1_funct_2(X44,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X44) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f2173,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),sK5)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6))
        | sK5 = k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X7,sK0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X4))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,X7))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl9_97 ),
    inference(duplicate_literal_removal,[],[f1994])).

fof(f1994,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),sK5)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6))
        | sK5 = k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X7,sK0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X7),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),k2_tmap_1(sK0,X4,X5,X7),X6),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X4),u1_struct_0(X4),u1_struct_0(sK1),X5,X6),X7),u1_struct_0(X7),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,X4,X5,X7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X4))))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X4,X5,X7))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl9_97 ),
    inference(superposition,[],[f840,f951])).

fof(f840,plain,
    ( ! [X45,X44] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X44,X45),sK5)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X44,X45),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X44,X45))
        | sK5 = k2_tmap_1(sK0,sK1,X44,X45)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X45,sK0)
        | ~ v1_funct_2(X44,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X44) )
    | ~ spl9_97 ),
    inference(avatar_component_clause,[],[f839])).

fof(f2217,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_190
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f2174,f835,f2215,f118,f113,f138,f133,f128,f123])).

fof(f2215,plain,
    ( spl9_190
  <=> ! [X1,X3,X0,X2] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | v2_struct_0(X3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),sK5)
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(sK0),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_190])])).

fof(f835,plain,
    ( spl9_96
  <=> ! [X42,X43] :
        ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X42,X43),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X42,X43))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X42,X43),sK5)
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X42,X43))
        | ~ m1_pre_topc(X43,sK0)
        | ~ v1_funct_2(X42,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X42) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f2174,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),sK5)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,X3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X3)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl9_96 ),
    inference(duplicate_literal_removal,[],[f1993])).

fof(f1993,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),sK5)
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X3),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK0,X0,X1,X3),X2),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,k1_partfun1(u1_struct_0(sK0),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(sK1),X1,X2),X3),u1_struct_0(X3),u1_struct_0(sK1))
        | ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,X3))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
        | v2_struct_0(sK0) )
    | ~ spl9_96 ),
    inference(superposition,[],[f836,f951])).

fof(f836,plain,
    ( ! [X43,X42] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X42,X43))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X42,X43),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X42,X43))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X42,X43),sK5)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X43,sK0)
        | ~ v1_funct_2(X42,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X42) )
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f835])).

fof(f2213,plain,
    ( spl9_3
    | ~ spl9_13
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_10
    | spl9_11
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_182
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_183
    | ~ spl9_184
    | ~ spl9_185
    | ~ spl9_186
    | ~ spl9_187
    | ~ spl9_188
    | ~ spl9_189
    | spl9_15 ),
    inference(avatar_split_clause,[],[f1992,f183,f2210,f2206,f2202,f2198,f2194,f2190,f2186,f178,f168,f2182,f118,f113,f138,f133,f128,f153,f148,f143,f163,f158,f208,f203,f198,f173,f123])).

fof(f2190,plain,
    ( spl9_184
  <=> v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f183,plain,
    ( spl9_15
  <=> v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f1992,plain,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),sK3,sK2)
    | ~ v1_funct_1(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4))
    | ~ v1_funct_2(k1_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK0,sK1,sK5,sK3),sK4),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,sK3))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | v2_struct_0(sK0)
    | spl9_15 ),
    inference(superposition,[],[f185,f951])).

fof(f185,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f1813,plain,
    ( spl9_3
    | spl9_181
    | ~ spl9_19
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1796,f198,f208,f118,f113,f138,f133,f128,f203,f1811,f123])).

fof(f1796,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_1(sK5)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4))
        | v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4)))
        | ~ v1_funct_1(X5) )
    | ~ spl9_18 ),
    inference(resolution,[],[f813,f200])).

fof(f1809,plain,
    ( spl9_6
    | spl9_180
    | ~ spl9_13
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1795,f168,f178,f133,f128,f153,f148,f143,f173,f1807,f138])).

fof(f1807,plain,
    ( spl9_180
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_pre_topc(X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_funct_1(k5_relat_1(X1,k2_tmap_1(sK1,sK2,sK4,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f1795,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | v1_funct_1(k5_relat_1(X1,k2_tmap_1(sK1,sK2,sK4,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl9_12 ),
    inference(resolution,[],[f813,f170])).

fof(f1762,plain,
    ( ~ spl9_88
    | ~ spl9_20
    | spl9_179
    | ~ spl9_18
    | ~ spl9_155 ),
    inference(avatar_split_clause,[],[f1744,f1542,f198,f1759,f208,f727])).

fof(f727,plain,
    ( spl9_88
  <=> v1_funct_1(k5_relat_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f1759,plain,
    ( spl9_179
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_179])])).

fof(f1744,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK5,sK5))
    | ~ spl9_18
    | ~ spl9_155 ),
    inference(resolution,[],[f1543,f200])).

fof(f1757,plain,
    ( ~ spl9_53
    | ~ spl9_14
    | spl9_178
    | ~ spl9_12
    | ~ spl9_155 ),
    inference(avatar_split_clause,[],[f1743,f1542,f168,f1754,f178,f457])).

fof(f1743,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ spl9_12
    | ~ spl9_155 ),
    inference(resolution,[],[f1543,f170])).

fof(f1725,plain,
    ( ~ spl9_18
    | ~ spl9_164 ),
    inference(avatar_contradiction_clause,[],[f1724])).

fof(f1724,plain,
    ( $false
    | ~ spl9_18
    | ~ spl9_164 ),
    inference(resolution,[],[f1655,f200])).

fof(f1655,plain,
    ( ! [X49] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X49)))
    | ~ spl9_164 ),
    inference(avatar_component_clause,[],[f1654])).

fof(f1722,plain,
    ( ~ spl9_12
    | ~ spl9_165 ),
    inference(avatar_contradiction_clause,[],[f1721])).

fof(f1721,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_165 ),
    inference(resolution,[],[f1658,f170])).

fof(f1658,plain,
    ( ! [X48] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X48,u1_struct_0(sK2))))
    | ~ spl9_165 ),
    inference(avatar_component_clause,[],[f1657])).

fof(f1720,plain,
    ( spl9_3
    | ~ spl9_19
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_177
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1703,f198,f208,f1718,f118,f113,f138,f133,f128,f203,f123])).

fof(f1718,plain,
    ( spl9_177
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k2_tmap_1(sK0,sK1,sK5,X3))
        | ~ m1_pre_topc(X3,sK0)
        | m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_177])])).

fof(f1703,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(sK5)
        | ~ r2_hidden(X2,k2_tmap_1(sK0,sK1,sK5,X3))
        | m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f658,f200])).

fof(f1716,plain,
    ( spl9_6
    | ~ spl9_13
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_176
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1702,f168,f178,f1714,f133,f128,f153,f148,f143,f173,f138])).

fof(f1714,plain,
    ( spl9_176
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_tmap_1(sK1,sK2,sK4,X1))
        | ~ m1_pre_topc(X1,sK1)
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_176])])).

fof(f1702,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k2_tmap_1(sK1,sK2,sK4,X1))
        | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X1,sK1)
        | v2_struct_0(sK1) )
    | ~ spl9_12 ),
    inference(resolution,[],[f658,f170])).

fof(f1701,plain,
    ( ~ spl9_18
    | ~ spl9_161 ),
    inference(avatar_contradiction_clause,[],[f1700])).

fof(f1700,plain,
    ( $false
    | ~ spl9_18
    | ~ spl9_161 ),
    inference(resolution,[],[f1644,f200])).

fof(f1644,plain,
    ( ! [X36] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X36,u1_struct_0(sK1))))
    | ~ spl9_161 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f1643,plain,
    ( spl9_161
  <=> ! [X36] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X36,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_161])])).

fof(f1699,plain,
    ( ~ spl9_34
    | spl9_175
    | spl9_161
    | ~ spl9_20
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f1622,f426,f208,f1643,f1697,f307])).

fof(f1697,plain,
    ( spl9_175
  <=> ! [X113,X108,X110,X112,X114,X109,X111] :
        ( ~ v1_funct_1(k5_relat_1(X108,X109))
        | ~ v1_funct_2(k5_relat_1(X108,X109),u1_struct_0(X110),u1_struct_0(sK0))
        | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X114)))
        | ~ v1_funct_1(X108)
        | ~ m1_subset_1(X109,k1_zfmisc_1(k2_zfmisc_1(X113,u1_struct_0(sK0))))
        | ~ v1_funct_1(X109)
        | v1_funct_1(k2_tmap_1(X110,sK1,k5_relat_1(k5_relat_1(X108,X109),sK5),X112))
        | ~ l1_struct_0(X112)
        | ~ l1_struct_0(X110)
        | ~ m1_subset_1(k5_relat_1(X108,X109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X111)))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X108,X109),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_175])])).

fof(f426,plain,
    ( spl9_51
  <=> ! [X3,X2] :
        ( ~ v1_funct_1(X2)
        | v1_funct_2(k5_relat_1(X2,sK5),X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f1622,plain,
    ( ! [X111,X109,X107,X114,X112,X110,X108,X113] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X107,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(X108,X109))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X108,X109),sK5))
        | ~ m1_subset_1(k5_relat_1(X108,X109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X111)))
        | ~ l1_struct_0(X110)
        | ~ l1_struct_0(X112)
        | v1_funct_1(k2_tmap_1(X110,sK1,k5_relat_1(k5_relat_1(X108,X109),sK5),X112))
        | ~ v1_funct_1(X109)
        | ~ m1_subset_1(X109,k1_zfmisc_1(k2_zfmisc_1(X113,u1_struct_0(sK0))))
        | ~ v1_funct_1(X108)
        | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X114)))
        | ~ v1_funct_2(k5_relat_1(X108,X109),u1_struct_0(X110),u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(duplicate_literal_removal,[],[f1613])).

fof(f1613,plain,
    ( ! [X111,X109,X107,X114,X112,X110,X108,X113] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X107,u1_struct_0(sK1))))
        | ~ v1_funct_1(k5_relat_1(X108,X109))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X108,X109),sK5))
        | ~ m1_subset_1(k5_relat_1(X108,X109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X111)))
        | ~ l1_struct_0(X110)
        | ~ l1_struct_0(X112)
        | v1_funct_1(k2_tmap_1(X110,sK1,k5_relat_1(k5_relat_1(X108,X109),sK5),X112))
        | ~ v1_funct_1(X109)
        | ~ m1_subset_1(X109,k1_zfmisc_1(k2_zfmisc_1(X113,u1_struct_0(sK0))))
        | ~ v1_funct_1(X108)
        | ~ m1_subset_1(X108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X110),X114)))
        | ~ v1_funct_1(k5_relat_1(X108,X109))
        | ~ v1_funct_2(k5_relat_1(X108,X109),u1_struct_0(X110),u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(resolution,[],[f705,f700])).

fof(f700,plain,
    ( ! [X70,X68,X72,X71,X69] :
        ( v1_funct_2(k5_relat_1(k5_relat_1(X68,X71),sK5),X69,u1_struct_0(sK1))
        | ~ v1_funct_1(X71)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X72,u1_struct_0(sK0))))
        | ~ v1_funct_1(X68)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
        | ~ v1_funct_1(k5_relat_1(X68,X71))
        | ~ v1_funct_2(k5_relat_1(X68,X71),X69,u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(resolution,[],[f297,f427])).

fof(f427,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | v1_funct_2(k5_relat_1(X2,sK5),X3,u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f426])).

fof(f1695,plain,
    ( ~ spl9_35
    | spl9_174
    | spl9_165
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f1623,f394,f178,f1657,f1693,f311])).

fof(f1693,plain,
    ( spl9_174
  <=> ! [X104,X106,X100,X102,X105,X101,X103] :
        ( ~ v1_funct_1(k5_relat_1(X100,X101))
        | ~ v1_funct_2(k5_relat_1(X100,X101),u1_struct_0(X102),u1_struct_0(sK1))
        | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X106)))
        | ~ v1_funct_1(X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X105,u1_struct_0(sK1))))
        | ~ v1_funct_1(X101)
        | v1_funct_1(k2_tmap_1(X102,sK2,k5_relat_1(k5_relat_1(X100,X101),sK4),X104))
        | ~ l1_struct_0(X104)
        | ~ l1_struct_0(X102)
        | ~ m1_subset_1(k5_relat_1(X100,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X103)))
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X100,X101),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_174])])).

fof(f1623,plain,
    ( ! [X103,X101,X99,X105,X102,X100,X106,X104] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X99,u1_struct_0(sK2))))
        | ~ v1_funct_1(k5_relat_1(X100,X101))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X100,X101),sK4))
        | ~ m1_subset_1(k5_relat_1(X100,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X103)))
        | ~ l1_struct_0(X102)
        | ~ l1_struct_0(X104)
        | v1_funct_1(k2_tmap_1(X102,sK2,k5_relat_1(k5_relat_1(X100,X101),sK4),X104))
        | ~ v1_funct_1(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X105,u1_struct_0(sK1))))
        | ~ v1_funct_1(X100)
        | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X106)))
        | ~ v1_funct_2(k5_relat_1(X100,X101),u1_struct_0(X102),u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(duplicate_literal_removal,[],[f1612])).

fof(f1612,plain,
    ( ! [X103,X101,X99,X105,X102,X100,X106,X104] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X99,u1_struct_0(sK2))))
        | ~ v1_funct_1(k5_relat_1(X100,X101))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k5_relat_1(X100,X101),sK4))
        | ~ m1_subset_1(k5_relat_1(X100,X101),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X103)))
        | ~ l1_struct_0(X102)
        | ~ l1_struct_0(X104)
        | v1_funct_1(k2_tmap_1(X102,sK2,k5_relat_1(k5_relat_1(X100,X101),sK4),X104))
        | ~ v1_funct_1(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X105,u1_struct_0(sK1))))
        | ~ v1_funct_1(X100)
        | ~ m1_subset_1(X100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X102),X106)))
        | ~ v1_funct_1(k5_relat_1(X100,X101))
        | ~ v1_funct_2(k5_relat_1(X100,X101),u1_struct_0(X102),u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f705,f698])).

fof(f698,plain,
    ( ! [X61,X59,X62,X60,X58] :
        ( v1_funct_2(k5_relat_1(k5_relat_1(X58,X61),sK4),X59,u1_struct_0(sK2))
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X62,u1_struct_0(sK1))))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(k5_relat_1(X58,X61))
        | ~ v1_funct_2(k5_relat_1(X58,X61),X59,u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f297,f395])).

fof(f1691,plain,
    ( ~ spl9_34
    | spl9_173
    | spl9_161
    | ~ spl9_20
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f1624,f426,f208,f1643,f1689,f307])).

fof(f1624,plain,
    ( ! [X94,X92,X97,X95,X93,X91,X98,X96] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X91,u1_struct_0(sK1))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X97)))
        | ~ l1_struct_0(X92)
        | ~ l1_struct_0(X98)
        | v1_funct_1(k2_tmap_1(X92,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5),X98))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),u1_struct_0(X92),u1_struct_0(sK0))
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X93)))
        | ~ v1_funct_1(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,u1_struct_0(sK0))))
        | ~ v1_funct_1(X95) )
    | ~ spl9_51 ),
    inference(duplicate_literal_removal,[],[f1611])).

fof(f1611,plain,
    ( ! [X94,X92,X97,X95,X93,X91,X98,X96] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X91,u1_struct_0(sK1))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X97)))
        | ~ l1_struct_0(X92)
        | ~ l1_struct_0(X98)
        | v1_funct_1(k2_tmap_1(X92,sK1,k5_relat_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),sK5),X98))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X92),X93,X94,u1_struct_0(sK0),X95,X96),u1_struct_0(X92),u1_struct_0(sK0))
        | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X92),X93)))
        | ~ v1_funct_1(X96)
        | ~ m1_subset_1(X96,k1_zfmisc_1(k2_zfmisc_1(X94,u1_struct_0(sK0))))
        | ~ v1_funct_1(X95) )
    | ~ spl9_51 ),
    inference(resolution,[],[f705,f489])).

fof(f489,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(X6,X7,X8,u1_struct_0(sK0),X9,X10),sK5),X6,u1_struct_0(sK1))
        | ~ v1_funct_1(k1_partfun1(X6,X7,X8,u1_struct_0(sK0),X9,X10))
        | ~ v1_funct_2(k1_partfun1(X6,X7,X8,u1_struct_0(sK0),X9,X10),X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK0))))
        | ~ v1_funct_1(X9) )
    | ~ spl9_51 ),
    inference(resolution,[],[f427,f82])).

fof(f1687,plain,
    ( ~ spl9_35
    | spl9_172
    | spl9_165
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f1625,f394,f178,f1657,f1685,f311])).

fof(f1625,plain,
    ( ! [X90,X88,X87,X85,X83,X89,X86,X84] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X83,u1_struct_0(sK2))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X89)))
        | ~ l1_struct_0(X84)
        | ~ l1_struct_0(X90)
        | v1_funct_1(k2_tmap_1(X84,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4),X90))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),u1_struct_0(X84),u1_struct_0(sK1))
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X85)))
        | ~ v1_funct_1(X88)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,u1_struct_0(sK1))))
        | ~ v1_funct_1(X87) )
    | ~ spl9_46 ),
    inference(duplicate_literal_removal,[],[f1610])).

fof(f1610,plain,
    ( ! [X90,X88,X87,X85,X83,X89,X86,X84] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X83,u1_struct_0(sK2))))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4))
        | ~ m1_subset_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X89)))
        | ~ l1_struct_0(X84)
        | ~ l1_struct_0(X90)
        | v1_funct_1(k2_tmap_1(X84,sK2,k5_relat_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),sK4),X90))
        | ~ v1_funct_1(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88))
        | ~ v1_funct_2(k1_partfun1(u1_struct_0(X84),X85,X86,u1_struct_0(sK1),X87,X88),u1_struct_0(X84),u1_struct_0(sK1))
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X84),X85)))
        | ~ v1_funct_1(X88)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X86,u1_struct_0(sK1))))
        | ~ v1_funct_1(X87) )
    | ~ spl9_46 ),
    inference(resolution,[],[f705,f476])).

fof(f476,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( v1_funct_2(k5_relat_1(k1_partfun1(X6,X7,X8,u1_struct_0(sK1),X9,X10),sK4),X6,u1_struct_0(sK2))
        | ~ v1_funct_1(k1_partfun1(X6,X7,X8,u1_struct_0(sK1),X9,X10))
        | ~ v1_funct_2(k1_partfun1(X6,X7,X8,u1_struct_0(sK1),X9,X10),X6,u1_struct_0(sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,u1_struct_0(sK1))))
        | ~ v1_funct_1(X9) )
    | ~ spl9_46 ),
    inference(resolution,[],[f395,f82])).

fof(f1683,plain,
    ( ~ spl9_34
    | spl9_171
    | spl9_161
    | ~ spl9_20
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f1626,f426,f208,f1643,f1681,f307])).

fof(f1681,plain,
    ( spl9_171
  <=> ! [X82,X79,X81,X78,X80] :
        ( ~ v1_funct_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80))
        | ~ v1_funct_1(X79)
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),u1_struct_0(X78),u1_struct_0(sK0))
        | v1_funct_1(k2_tmap_1(X78,sK1,k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5),X82))
        | ~ l1_struct_0(X82)
        | ~ l1_struct_0(X78)
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),X81)))
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_171])])).

fof(f1626,plain,
    ( ! [X80,X78,X81,X79,X77,X82] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X77,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5))
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),X81)))
        | ~ l1_struct_0(X78)
        | ~ l1_struct_0(X82)
        | v1_funct_1(k2_tmap_1(X78,sK1,k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5),X82))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),u1_struct_0(X78),u1_struct_0(sK0))
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(sK0))))
        | ~ v1_funct_1(X79) )
    | ~ spl9_51 ),
    inference(duplicate_literal_removal,[],[f1609])).

fof(f1609,plain,
    ( ! [X80,X78,X81,X79,X77,X82] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X77,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5))
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),X81)))
        | ~ l1_struct_0(X78)
        | ~ l1_struct_0(X82)
        | v1_funct_1(k2_tmap_1(X78,sK1,k5_relat_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),sK5),X82))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X78),u1_struct_0(sK0),X79,X80),u1_struct_0(X78),u1_struct_0(sK0))
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(sK0))))
        | ~ v1_funct_1(X79) )
    | ~ spl9_51 ),
    inference(resolution,[],[f705,f488])).

fof(f488,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k5_relat_1(k2_partfun1(X3,u1_struct_0(sK0),X4,X5),sK5),X3,u1_struct_0(sK1))
        | ~ v1_funct_1(k2_partfun1(X3,u1_struct_0(sK0),X4,X5))
        | ~ v1_funct_2(k2_partfun1(X3,u1_struct_0(sK0),X4,X5),X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ v1_funct_1(X4) )
    | ~ spl9_51 ),
    inference(resolution,[],[f427,f100])).

fof(f1679,plain,
    ( ~ spl9_35
    | spl9_170
    | spl9_165
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f1627,f394,f178,f1657,f1677,f311])).

fof(f1677,plain,
    ( spl9_170
  <=> ! [X73,X75,X72,X74,X76] :
        ( ~ v1_funct_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74))
        | ~ v1_funct_1(X73)
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),u1_struct_0(X72),u1_struct_0(sK1))
        | v1_funct_1(k2_tmap_1(X72,sK2,k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4),X76))
        | ~ l1_struct_0(X76)
        | ~ l1_struct_0(X72)
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),X75)))
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).

fof(f1627,plain,
    ( ! [X76,X74,X72,X71,X75,X73] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X71,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4))
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),X75)))
        | ~ l1_struct_0(X72)
        | ~ l1_struct_0(X76)
        | v1_funct_1(k2_tmap_1(X72,sK2,k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4),X76))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),u1_struct_0(X72),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(sK1))))
        | ~ v1_funct_1(X73) )
    | ~ spl9_46 ),
    inference(duplicate_literal_removal,[],[f1608])).

fof(f1608,plain,
    ( ! [X76,X74,X72,X71,X75,X73] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X71,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4))
        | ~ m1_subset_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),X75)))
        | ~ l1_struct_0(X72)
        | ~ l1_struct_0(X76)
        | v1_funct_1(k2_tmap_1(X72,sK2,k5_relat_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),sK4),X76))
        | ~ v1_funct_1(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74))
        | ~ v1_funct_2(k2_partfun1(u1_struct_0(X72),u1_struct_0(sK1),X73,X74),u1_struct_0(X72),u1_struct_0(sK1))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X72),u1_struct_0(sK1))))
        | ~ v1_funct_1(X73) )
    | ~ spl9_46 ),
    inference(resolution,[],[f705,f475])).

fof(f475,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_2(k5_relat_1(k2_partfun1(X3,u1_struct_0(sK1),X4,X5),sK4),X3,u1_struct_0(sK2))
        | ~ v1_funct_1(k2_partfun1(X3,u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_2(k2_partfun1(X3,u1_struct_0(sK1),X4,X5),X3,u1_struct_0(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK1))))
        | ~ v1_funct_1(X4) )
    | ~ spl9_46 ),
    inference(resolution,[],[f395,f100])).

fof(f1675,plain,
    ( ~ spl9_34
    | spl9_169
    | spl9_161
    | ~ spl9_20
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f1628,f426,f208,f1643,f1673,f307])).

fof(f1673,plain,
    ( spl9_169
  <=> ! [X69,X68,X70] :
        ( ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),u1_struct_0(X68),u1_struct_0(sK0))
        | v1_funct_1(k2_tmap_1(X68,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5),X70))
        | ~ l1_struct_0(X70)
        | ~ l1_struct_0(X68)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),X69)))
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_169])])).

fof(f1628,plain,
    ( ! [X70,X68,X69,X67] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X67,u1_struct_0(sK1))))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5))
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),X69)))
        | ~ l1_struct_0(X68)
        | ~ l1_struct_0(X70)
        | v1_funct_1(k2_tmap_1(X68,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5),X70))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),u1_struct_0(X68),u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(duplicate_literal_removal,[],[f1607])).

fof(f1607,plain,
    ( ! [X70,X68,X69,X67] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X67,u1_struct_0(sK1))))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5))
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),X69)))
        | ~ l1_struct_0(X68)
        | ~ l1_struct_0(X70)
        | v1_funct_1(k2_tmap_1(X68,sK1,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),sK5),X70))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X68),u1_struct_0(sK0)))),u1_struct_0(X68),u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(resolution,[],[f705,f490])).

fof(f490,plain,
    ( ! [X11] :
        ( v1_funct_2(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK0)))),sK5),X11,u1_struct_0(sK1))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK0)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK0)))),X11,u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(resolution,[],[f427,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f1671,plain,
    ( ~ spl9_35
    | spl9_168
    | spl9_165
    | ~ spl9_14
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f1629,f394,f178,f1657,f1669,f311])).

fof(f1669,plain,
    ( spl9_168
  <=> ! [X65,X64,X66] :
        ( ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),u1_struct_0(X64),u1_struct_0(sK1))
        | v1_funct_1(k2_tmap_1(X64,sK2,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4),X66))
        | ~ l1_struct_0(X66)
        | ~ l1_struct_0(X64)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),X65)))
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).

fof(f1629,plain,
    ( ! [X66,X64,X65,X63] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X63,u1_struct_0(sK2))))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4))
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),X65)))
        | ~ l1_struct_0(X64)
        | ~ l1_struct_0(X66)
        | v1_funct_1(k2_tmap_1(X64,sK2,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4),X66))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),u1_struct_0(X64),u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(duplicate_literal_removal,[],[f1606])).

fof(f1606,plain,
    ( ! [X66,X64,X65,X63] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X63,u1_struct_0(sK2))))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4))
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),X65)))
        | ~ l1_struct_0(X64)
        | ~ l1_struct_0(X66)
        | v1_funct_1(k2_tmap_1(X64,sK2,k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),sK4),X66))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(sK1)))),u1_struct_0(X64),u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f705,f477])).

fof(f477,plain,
    ( ! [X11] :
        ( v1_funct_2(k5_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK1)))),sK4),X11,u1_struct_0(sK2))
        | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK1)))))
        | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(X11,u1_struct_0(sK1)))),X11,u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f395,f96])).

fof(f1667,plain,
    ( ~ spl9_35
    | spl9_167
    | spl9_165
    | ~ spl9_14
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f1630,f843,f178,f1657,f1665,f311])).

fof(f1630,plain,
    ( ! [X61,X59,X57,X62,X60,X58] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X57,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(X58,sK1,X59,X60))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4))
        | ~ m1_subset_1(k2_tmap_1(X58,sK1,X59,X60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),X61)))
        | ~ l1_struct_0(X58)
        | ~ l1_struct_0(X62)
        | v1_funct_1(k2_tmap_1(X58,sK2,k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4),X62))
        | ~ v1_funct_2(k2_tmap_1(X58,sK1,X59,X60),u1_struct_0(X58),u1_struct_0(sK1))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(sK1))))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X60,X58)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(sK1))
        | ~ l1_pre_topc(X58)
        | ~ v2_pre_topc(X58)
        | ~ v1_funct_1(X59) )
    | ~ spl9_98 ),
    inference(duplicate_literal_removal,[],[f1605])).

fof(f1605,plain,
    ( ! [X61,X59,X57,X62,X60,X58] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X57,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(X58,sK1,X59,X60))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4))
        | ~ m1_subset_1(k2_tmap_1(X58,sK1,X59,X60),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),X61)))
        | ~ l1_struct_0(X58)
        | ~ l1_struct_0(X62)
        | v1_funct_1(k2_tmap_1(X58,sK2,k5_relat_1(k2_tmap_1(X58,sK1,X59,X60),sK4),X62))
        | ~ v1_funct_2(k2_tmap_1(X58,sK1,X59,X60),u1_struct_0(X58),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X58,sK1,X59,X60))
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(sK1))))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X60,X58)
        | ~ v1_funct_2(X59,u1_struct_0(X58),u1_struct_0(sK1))
        | ~ l1_pre_topc(X58)
        | ~ v2_pre_topc(X58)
        | ~ v1_funct_1(X59) )
    | ~ spl9_98 ),
    inference(resolution,[],[f705,f844])).

fof(f1663,plain,
    ( ~ spl9_35
    | spl9_166
    | spl9_165
    | ~ spl9_14
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f1631,f484,f178,f1657,f1661,f311])).

fof(f1661,plain,
    ( spl9_166
  <=> ! [X53,X55,X56,X52,X54] :
        ( ~ v1_funct_1(k2_tmap_1(X52,sK1,X53,X54))
        | ~ v1_funct_2(k2_tmap_1(X52,sK1,X53,X54),u1_struct_0(X54),u1_struct_0(sK1))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(sK1))
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(sK1))))
        | ~ l1_struct_0(X52)
        | v1_funct_1(k2_tmap_1(X54,sK2,k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4),X56))
        | ~ l1_struct_0(X56)
        | ~ l1_struct_0(X54)
        | ~ m1_subset_1(k2_tmap_1(X52,sK1,X53,X54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),X55)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f484,plain,
    ( spl9_57
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f1631,plain,
    ( ! [X54,X52,X56,X55,X53,X51] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X51,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(X52,sK1,X53,X54))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4))
        | ~ m1_subset_1(k2_tmap_1(X52,sK1,X53,X54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),X55)))
        | ~ l1_struct_0(X54)
        | ~ l1_struct_0(X56)
        | v1_funct_1(k2_tmap_1(X54,sK2,k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4),X56))
        | ~ l1_struct_0(X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(sK1))))
        | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(sK1))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(k2_tmap_1(X52,sK1,X53,X54),u1_struct_0(X54),u1_struct_0(sK1)) )
    | ~ spl9_57 ),
    inference(duplicate_literal_removal,[],[f1604])).

fof(f1604,plain,
    ( ! [X54,X52,X56,X55,X53,X51] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X51,u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(X52,sK1,X53,X54))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4))
        | ~ m1_subset_1(k2_tmap_1(X52,sK1,X53,X54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X54),X55)))
        | ~ l1_struct_0(X54)
        | ~ l1_struct_0(X56)
        | v1_funct_1(k2_tmap_1(X54,sK2,k5_relat_1(k2_tmap_1(X52,sK1,X53,X54),sK4),X56))
        | ~ l1_struct_0(X52)
        | ~ l1_struct_0(X54)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(sK1))))
        | ~ v1_funct_2(X53,u1_struct_0(X52),u1_struct_0(sK1))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(k2_tmap_1(X52,sK1,X53,X54),u1_struct_0(X54),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X52,sK1,X53,X54)) )
    | ~ spl9_57 ),
    inference(resolution,[],[f705,f485])).

fof(f485,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2)) )
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1659,plain,
    ( spl9_163
    | ~ spl9_37
    | spl9_164
    | ~ spl9_53
    | ~ spl9_35
    | ~ spl9_20
    | spl9_165
    | ~ spl9_14
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f1603,f479,f178,f1657,f208,f311,f457,f1654,f319,f1651])).

fof(f1603,plain,
    ( ! [X50,X48,X49] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X48,u1_struct_0(sK2))))
        | ~ v1_funct_1(sK5)
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(k5_relat_1(sK5,sK4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X49)))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X50)
        | v1_funct_1(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),X50)) )
    | ~ spl9_56 ),
    inference(resolution,[],[f705,f481])).

fof(f481,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f479])).

fof(f1649,plain,
    ( ~ spl9_34
    | spl9_162
    | spl9_161
    | ~ spl9_20
    | ~ spl9_100 ),
    inference(avatar_split_clause,[],[f1632,f851,f208,f1643,f1647,f307])).

fof(f1632,plain,
    ( ! [X47,X45,X43,X46,X44,X42] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X43,sK0,X44,X45))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5))
        | ~ m1_subset_1(k2_tmap_1(X43,sK0,X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),X46)))
        | ~ l1_struct_0(X43)
        | ~ l1_struct_0(X47)
        | v1_funct_1(k2_tmap_1(X43,sK1,k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5),X47))
        | ~ v1_funct_2(k2_tmap_1(X43,sK0,X44,X45),u1_struct_0(X43),u1_struct_0(sK0))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(sK0))))
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X45,X43)
        | ~ v1_funct_2(X44,u1_struct_0(X43),u1_struct_0(sK0))
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X43)
        | ~ v1_funct_1(X44) )
    | ~ spl9_100 ),
    inference(duplicate_literal_removal,[],[f1602])).

fof(f1602,plain,
    ( ! [X47,X45,X43,X46,X44,X42] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X42,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X43,sK0,X44,X45))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5))
        | ~ m1_subset_1(k2_tmap_1(X43,sK0,X44,X45),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),X46)))
        | ~ l1_struct_0(X43)
        | ~ l1_struct_0(X47)
        | v1_funct_1(k2_tmap_1(X43,sK1,k5_relat_1(k2_tmap_1(X43,sK0,X44,X45),sK5),X47))
        | ~ v1_funct_2(k2_tmap_1(X43,sK0,X44,X45),u1_struct_0(X43),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X43,sK0,X44,X45))
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X43),u1_struct_0(sK0))))
        | v2_struct_0(X43)
        | ~ m1_pre_topc(X45,X43)
        | ~ v1_funct_2(X44,u1_struct_0(X43),u1_struct_0(sK0))
        | ~ l1_pre_topc(X43)
        | ~ v2_pre_topc(X43)
        | ~ v1_funct_1(X44) )
    | ~ spl9_100 ),
    inference(resolution,[],[f705,f852])).

fof(f1645,plain,
    ( ~ spl9_34
    | spl9_160
    | spl9_161
    | ~ spl9_20
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f1633,f492,f208,f1643,f1640,f307])).

fof(f1640,plain,
    ( spl9_160
  <=> ! [X40,X38,X41,X37,X39] :
        ( ~ v1_funct_1(k2_tmap_1(X37,sK0,X38,X39))
        | ~ v1_funct_2(k2_tmap_1(X37,sK0,X38,X39),u1_struct_0(X39),u1_struct_0(sK0))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,u1_struct_0(X37),u1_struct_0(sK0))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(sK0))))
        | ~ l1_struct_0(X37)
        | v1_funct_1(k2_tmap_1(X39,sK1,k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5),X41))
        | ~ l1_struct_0(X41)
        | ~ l1_struct_0(X39)
        | ~ m1_subset_1(k2_tmap_1(X37,sK0,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),X40)))
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f492,plain,
    ( spl9_58
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK0,X1,X2),sK5),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,X2),u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f1633,plain,
    ( ! [X39,X37,X41,X38,X36,X40] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X36,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X37,sK0,X38,X39))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5))
        | ~ m1_subset_1(k2_tmap_1(X37,sK0,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),X40)))
        | ~ l1_struct_0(X39)
        | ~ l1_struct_0(X41)
        | v1_funct_1(k2_tmap_1(X39,sK1,k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5),X41))
        | ~ l1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(sK0))))
        | ~ v1_funct_2(X38,u1_struct_0(X37),u1_struct_0(sK0))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(k2_tmap_1(X37,sK0,X38,X39),u1_struct_0(X39),u1_struct_0(sK0)) )
    | ~ spl9_58 ),
    inference(duplicate_literal_removal,[],[f1601])).

fof(f1601,plain,
    ( ! [X39,X37,X41,X38,X36,X40] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X36,u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X37,sK0,X38,X39))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5))
        | ~ m1_subset_1(k2_tmap_1(X37,sK0,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),X40)))
        | ~ l1_struct_0(X39)
        | ~ l1_struct_0(X41)
        | v1_funct_1(k2_tmap_1(X39,sK1,k5_relat_1(k2_tmap_1(X37,sK0,X38,X39),sK5),X41))
        | ~ l1_struct_0(X37)
        | ~ l1_struct_0(X39)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(sK0))))
        | ~ v1_funct_2(X38,u1_struct_0(X37),u1_struct_0(sK0))
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(k2_tmap_1(X37,sK0,X38,X39),u1_struct_0(X39),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X37,sK0,X38,X39)) )
    | ~ spl9_58 ),
    inference(resolution,[],[f705,f493])).

fof(f493,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK0,X1,X2),sK5),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,X2),u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,X2)) )
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1595,plain,
    ( ~ spl9_37
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | spl9_159
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1578,f198,f1593,f307,f208,f203,f319])).

fof(f1578,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X4))
        | v1_funct_1(k5_relat_1(X5,k2_tmap_1(sK0,sK1,sK5,X4)))
        | ~ v1_funct_1(X5)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ l1_struct_0(X4)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f661,f200])).

fof(f1591,plain,
    ( ~ spl9_34
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_35
    | spl9_158
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1577,f168,f1589,f311,f178,f173,f307])).

fof(f1589,plain,
    ( spl9_158
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | v1_funct_1(k5_relat_1(X1,k2_tmap_1(sK1,sK2,sK4,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f1577,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | v1_funct_1(k5_relat_1(X1,k2_tmap_1(sK1,sK2,sK4,X0)))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK1) )
    | ~ spl9_12 ),
    inference(resolution,[],[f661,f170])).

fof(f1565,plain,
    ( ~ spl9_87
    | ~ spl9_20
    | spl9_157
    | ~ spl9_18
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f1547,f1538,f198,f1562,f208,f722])).

fof(f722,plain,
    ( spl9_87
  <=> v1_funct_1(k5_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f1562,plain,
    ( spl9_157
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_157])])).

fof(f1547,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl9_18
    | ~ spl9_154 ),
    inference(resolution,[],[f1539,f200])).

fof(f1560,plain,
    ( ~ spl9_86
    | ~ spl9_14
    | spl9_156
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(avatar_split_clause,[],[f1546,f1538,f168,f1557,f178,f682])).

fof(f682,plain,
    ( spl9_86
  <=> v1_funct_1(k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f1557,plain,
    ( spl9_156
  <=> v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f1546,plain,
    ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ spl9_12
    | ~ spl9_154 ),
    inference(resolution,[],[f1539,f170])).

fof(f1544,plain,
    ( ~ spl9_20
    | spl9_155
    | ~ spl9_18
    | ~ spl9_147 ),
    inference(avatar_split_clause,[],[f1528,f1443,f198,f1542,f208])).

fof(f1528,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK5,X3)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_1(k5_relat_1(sK5,X3))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl9_18
    | ~ spl9_147 ),
    inference(resolution,[],[f1444,f200])).

fof(f1540,plain,
    ( ~ spl9_14
    | spl9_154
    | ~ spl9_12
    | ~ spl9_147 ),
    inference(avatar_split_clause,[],[f1527,f1443,f168,f1538,f178])).

fof(f1527,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k5_relat_1(sK5,k5_relat_1(sK4,X0)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(sK4,X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl9_12
    | ~ spl9_147 ),
    inference(resolution,[],[f1444,f170])).

fof(f1513,plain,
    ( ~ spl9_88
    | ~ spl9_20
    | spl9_153
    | ~ spl9_18
    | ~ spl9_149 ),
    inference(avatar_split_clause,[],[f1495,f1461,f198,f1510,f208,f727])).

fof(f1510,plain,
    ( spl9_153
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f1495,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK5,sK5))
    | ~ spl9_18
    | ~ spl9_149 ),
    inference(resolution,[],[f1462,f200])).

fof(f1508,plain,
    ( ~ spl9_53
    | ~ spl9_14
    | spl9_152
    | ~ spl9_12
    | ~ spl9_149 ),
    inference(avatar_split_clause,[],[f1494,f1461,f168,f1505,f178,f457])).

fof(f1494,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ spl9_12
    | ~ spl9_149 ),
    inference(resolution,[],[f1462,f170])).

fof(f1483,plain,
    ( ~ spl9_87
    | ~ spl9_20
    | spl9_151
    | ~ spl9_18
    | ~ spl9_148 ),
    inference(avatar_split_clause,[],[f1465,f1457,f198,f1480,f208,f722])).

fof(f1480,plain,
    ( spl9_151
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_151])])).

fof(f1465,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK5)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl9_18
    | ~ spl9_148 ),
    inference(resolution,[],[f1458,f200])).

fof(f1478,plain,
    ( ~ spl9_86
    | ~ spl9_14
    | spl9_150
    | ~ spl9_12
    | ~ spl9_148 ),
    inference(avatar_split_clause,[],[f1464,f1457,f168,f1475,f178,f682])).

fof(f1475,plain,
    ( spl9_150
  <=> v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_150])])).

fof(f1464,plain,
    ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ spl9_12
    | ~ spl9_148 ),
    inference(resolution,[],[f1458,f170])).

fof(f1463,plain,
    ( ~ spl9_20
    | spl9_149
    | ~ spl9_18
    | ~ spl9_146 ),
    inference(avatar_split_clause,[],[f1447,f1439,f198,f1461,f208])).

fof(f1447,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK5,X3)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_1(k5_relat_1(sK5,X3))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl9_18
    | ~ spl9_146 ),
    inference(resolution,[],[f1440,f200])).

fof(f1459,plain,
    ( ~ spl9_14
    | spl9_148
    | ~ spl9_12
    | ~ spl9_146 ),
    inference(avatar_split_clause,[],[f1446,f1439,f168,f1457,f178])).

fof(f1446,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k5_relat_1(sK4,k5_relat_1(sK4,X0)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(sK4,X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl9_12
    | ~ spl9_146 ),
    inference(resolution,[],[f1440,f170])).

fof(f1445,plain,
    ( ~ spl9_20
    | spl9_147
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1429,f198,f1443,f208])).

fof(f1429,plain,
    ( ! [X6,X10,X8,X7,X11,X9] :
        ( ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(k5_relat_1(X9,X6))
        | v1_funct_1(k5_relat_1(sK5,k5_relat_1(X9,X6)))
        | ~ v1_funct_1(sK5) )
    | ~ spl9_18 ),
    inference(resolution,[],[f696,f200])).

fof(f1441,plain,
    ( ~ spl9_14
    | spl9_146
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1428,f168,f1439,f178])).

fof(f1428,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(k5_relat_1(X3,X0))
        | v1_funct_1(k5_relat_1(sK4,k5_relat_1(X3,X0)))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_12 ),
    inference(resolution,[],[f696,f170])).

fof(f1373,plain,
    ( ~ spl9_37
    | ~ spl9_34
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_144
    | spl9_145
    | ~ spl9_97 ),
    inference(avatar_split_clause,[],[f1365,f839,f1371,f1367,f198,f208,f203,f307,f319])).

fof(f1367,plain,
    ( spl9_144
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f1371,plain,
    ( spl9_145
  <=> ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X0,sK0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | sK5 = k2_tmap_1(sK0,sK1,X0,sK0)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f1365,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK0))
        | sK5 = k2_tmap_1(sK0,sK1,X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X0,sK0))
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_97 ),
    inference(duplicate_literal_removal,[],[f1364])).

fof(f1364,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK0))
        | sK5 = k2_tmap_1(sK0,sK1,X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK0,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X0,sK0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X0,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK5)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X0,sK0))
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_97 ),
    inference(resolution,[],[f840,f379])).

fof(f379,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k2_tmap_1(X5,X4,X6,X3),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_1(k2_tmap_1(X5,X4,X6,X3))
      | ~ v1_funct_2(k2_tmap_1(X5,X4,X6,X3),u1_struct_0(X3),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),X2,k2_tmap_1(X5,X4,X6,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X4))
      | ~ l1_struct_0(X4)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X5) ) ),
    inference(resolution,[],[f103,f87])).

fof(f1363,plain,
    ( ~ spl9_34
    | ~ spl9_35
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_142
    | spl9_143
    | ~ spl9_95 ),
    inference(avatar_split_clause,[],[f1355,f831,f1361,f1357,f168,f178,f173,f311,f307])).

fof(f1357,plain,
    ( spl9_142
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f1361,plain,
    ( spl9_143
  <=> ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK1,sK2,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | sK4 = k2_tmap_1(sK1,sK2,X0,sK1)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f1355,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK1,sK2,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X0,sK1))
        | sK4 = k2_tmap_1(sK1,sK2,X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(sK1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(sK4)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X0,sK1))
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(sK1) )
    | ~ spl9_95 ),
    inference(duplicate_literal_removal,[],[f1354])).

fof(f1354,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_tmap_1(sK1,sK2,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X0,sK1))
        | sK4 = k2_tmap_1(sK1,sK2,X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(sK1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X0,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(sK4)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X0,sK1))
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(sK1) )
    | ~ spl9_95 ),
    inference(resolution,[],[f832,f379])).

fof(f1353,plain,
    ( spl9_141
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1337,f198,f208,f1351])).

fof(f1351,plain,
    ( spl9_141
  <=> ! [X5,X7,X4,X6] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | m1_subset_1(X7,k2_zfmisc_1(X5,u1_struct_0(sK1)))
        | ~ r2_hidden(X7,k5_relat_1(X4,sK5))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).

fof(f1337,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | ~ r2_hidden(X7,k5_relat_1(X4,sK5))
        | m1_subset_1(X7,k2_zfmisc_1(X5,u1_struct_0(sK1))) )
    | ~ spl9_18 ),
    inference(resolution,[],[f711,f200])).

fof(f1349,plain,
    ( spl9_140
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1336,f168,f178,f1347])).

fof(f1347,plain,
    ( spl9_140
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(X3,k2_zfmisc_1(X1,u1_struct_0(sK2)))
        | ~ r2_hidden(X3,k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f1336,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k5_relat_1(X0,sK4))
        | m1_subset_1(X3,k2_zfmisc_1(X1,u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f711,f170])).

fof(f1310,plain,
    ( ~ spl9_14
    | spl9_138
    | ~ spl9_139
    | ~ spl9_12
    | ~ spl9_135 ),
    inference(avatar_split_clause,[],[f1293,f1268,f168,f1307,f1304,f178])).

fof(f1304,plain,
    ( spl9_138
  <=> ! [X0] : ~ r2_hidden(X0,k5_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f1307,plain,
    ( spl9_139
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f1293,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
        | ~ r2_hidden(X0,k5_relat_1(sK4,sK5))
        | ~ v1_funct_1(sK4) )
    | ~ spl9_12
    | ~ spl9_135 ),
    inference(resolution,[],[f1269,f170])).

fof(f1288,plain,
    ( ~ spl9_20
    | spl9_136
    | ~ spl9_137
    | ~ spl9_18
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f1272,f1264,f198,f1285,f1282,f208])).

fof(f1282,plain,
    ( spl9_136
  <=> ! [X1] : ~ r2_hidden(X1,k5_relat_1(sK5,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1285,plain,
    ( spl9_137
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f1272,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK2)))
        | ~ r2_hidden(X1,k5_relat_1(sK5,sK4))
        | ~ v1_funct_1(sK5) )
    | ~ spl9_18
    | ~ spl9_134 ),
    inference(resolution,[],[f1265,f200])).

fof(f1270,plain,
    ( spl9_135
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1254,f198,f208,f1268])).

fof(f1254,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | ~ r2_hidden(X7,k5_relat_1(X4,sK5))
        | ~ v1_xboole_0(k2_zfmisc_1(X5,u1_struct_0(sK1))) )
    | ~ spl9_18 ),
    inference(resolution,[],[f712,f200])).

fof(f1266,plain,
    ( spl9_134
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f1253,f168,f178,f1264])).

fof(f1253,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X3,k5_relat_1(X0,sK4))
        | ~ v1_xboole_0(k2_zfmisc_1(X1,u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f712,f170])).

fof(f1245,plain,
    ( ~ spl9_37
    | spl9_133
    | ~ spl9_101 ),
    inference(avatar_split_clause,[],[f1241,f855,f1243,f319])).

fof(f855,plain,
    ( spl9_101
  <=> ! [X55,X56,X57] :
        ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(sK0))))
        | ~ v1_funct_2(k2_tmap_1(X56,sK0,X55,X57),u1_struct_0(X56),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X56,sK0,X55,X57))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X56,sK0,X55,X57),sK5))
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X57,X56)
        | ~ v1_funct_2(X55,u1_struct_0(X56),u1_struct_0(sK0))
        | ~ l1_pre_topc(X56)
        | ~ v2_pre_topc(X56)
        | ~ v1_funct_1(X55) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f1241,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK0,X0,X1),sK5))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X1) )
    | ~ spl9_101 ),
    inference(duplicate_literal_removal,[],[f1240])).

fof(f1240,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X1,sK0,X0,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK0,X0,X1),sK5))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X1) )
    | ~ spl9_101 ),
    inference(resolution,[],[f856,f86])).

fof(f856,plain,
    ( ! [X57,X56,X55] :
        ( ~ v1_funct_2(k2_tmap_1(X56,sK0,X55,X57),u1_struct_0(X56),u1_struct_0(sK0))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(sK0))))
        | ~ v1_funct_1(k2_tmap_1(X56,sK0,X55,X57))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X56,sK0,X55,X57),sK5))
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X57,X56)
        | ~ v1_funct_2(X55,u1_struct_0(X56),u1_struct_0(sK0))
        | ~ l1_pre_topc(X56)
        | ~ v2_pre_topc(X56)
        | ~ v1_funct_1(X55) )
    | ~ spl9_101 ),
    inference(avatar_component_clause,[],[f855])).

fof(f1239,plain,
    ( ~ spl9_34
    | spl9_132
    | ~ spl9_99 ),
    inference(avatar_split_clause,[],[f1235,f847,f1237,f307])).

fof(f847,plain,
    ( spl9_99
  <=> ! [X49,X51,X50] :
        ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_tmap_1(X50,sK1,X49,X51),u1_struct_0(X50),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X50,sK1,X49,X51))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X50,sK1,X49,X51),sK4))
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X51,X50)
        | ~ v1_funct_2(X49,u1_struct_0(X50),u1_struct_0(sK1))
        | ~ l1_pre_topc(X50)
        | ~ v2_pre_topc(X50)
        | ~ v1_funct_1(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f1235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X0,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK1,X0,X1),sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X1) )
    | ~ spl9_99 ),
    inference(duplicate_literal_removal,[],[f1234])).

fof(f1234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X1,sK1,X0,X1))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X1,sK1,X0,X1),sK4))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X1) )
    | ~ spl9_99 ),
    inference(resolution,[],[f848,f86])).

fof(f848,plain,
    ( ! [X50,X51,X49] :
        ( ~ v1_funct_2(k2_tmap_1(X50,sK1,X49,X51),u1_struct_0(X50),u1_struct_0(sK1))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(sK1))))
        | ~ v1_funct_1(k2_tmap_1(X50,sK1,X49,X51))
        | v1_funct_1(k5_relat_1(k2_tmap_1(X50,sK1,X49,X51),sK4))
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X51,X50)
        | ~ v1_funct_2(X49,u1_struct_0(X50),u1_struct_0(sK1))
        | ~ l1_pre_topc(X50)
        | ~ v2_pre_topc(X50)
        | ~ v1_funct_1(X49) )
    | ~ spl9_99 ),
    inference(avatar_component_clause,[],[f847])).

fof(f1231,plain,
    ( ~ spl9_126
    | ~ spl9_127
    | spl9_131
    | ~ spl9_128
    | spl9_130
    | spl9_82
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f1175,f363,f644,f1223,f1215,f1228,f1211,f1207])).

fof(f1207,plain,
    ( spl9_126
  <=> v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f1211,plain,
    ( spl9_127
  <=> v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f1228,plain,
    ( spl9_131
  <=> sK5 = sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f1215,plain,
    ( spl9_128
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f1223,plain,
    ( spl9_130
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f644,plain,
    ( spl9_82
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f363,plain,
    ( spl9_43
  <=> ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5)
        | sK5 = X1
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f1175,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),sK5)
    | sK5 = sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))))
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_43 ),
    inference(resolution,[],[f599,f364])).

fof(f364,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5)
        | sK5 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f363])).

fof(f599,plain,(
    ! [X43] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X43))))),X43)
      | v1_xboole_0(sK6(k1_zfmisc_1(X43)))
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X43))))) ) ),
    inference(resolution,[],[f575,f450])).

fof(f450,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK6(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK6(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f255,f94])).

fof(f255,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK6(k1_zfmisc_1(X3)))
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f93,f96])).

fof(f575,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f450,f96])).

fof(f1226,plain,
    ( ~ spl9_126
    | ~ spl9_127
    | ~ spl9_128
    | spl9_129
    | spl9_130
    | spl9_82
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f1174,f388,f644,f1223,f1219,f1215,f1211,f1207])).

fof(f1219,plain,
    ( spl9_129
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f388,plain,
    ( spl9_45
  <=> ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f1174,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),sK5)
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_45 ),
    inference(resolution,[],[f599,f389])).

fof(f389,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f388])).

fof(f1205,plain,
    ( ~ spl9_120
    | ~ spl9_121
    | spl9_125
    | ~ spl9_122
    | spl9_124
    | spl9_76
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f1173,f359,f618,f1197,f1189,f1202,f1185,f1181])).

fof(f1181,plain,
    ( spl9_120
  <=> v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f1185,plain,
    ( spl9_121
  <=> v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f1202,plain,
    ( spl9_125
  <=> sK4 = sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f1189,plain,
    ( spl9_122
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f1197,plain,
    ( spl9_124
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f618,plain,
    ( spl9_76
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f359,plain,
    ( spl9_42
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4)
        | sK4 = X0
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f1173,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),sK4)
    | sK4 = sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))))
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_42 ),
    inference(resolution,[],[f599,f360])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4)
        | sK4 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f359])).

fof(f1200,plain,
    ( ~ spl9_120
    | ~ spl9_121
    | ~ spl9_122
    | spl9_123
    | spl9_124
    | spl9_76
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f1172,f384,f618,f1197,f1193,f1189,f1185,f1181])).

fof(f1193,plain,
    ( spl9_123
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f384,plain,
    ( spl9_44
  <=> ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f1172,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),sK4)
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_44 ),
    inference(resolution,[],[f599,f385])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) )
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1138,plain,
    ( ~ spl9_37
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | spl9_119
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f1122,f671,f198,f1136,f307,f208,f203,f319])).

fof(f1136,plain,
    ( spl9_119
  <=> ! [X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK5))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f1122,plain,
    ( ! [X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK5))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(resolution,[],[f715,f200])).

fof(f1134,plain,
    ( ~ spl9_34
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_35
    | spl9_118
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f1121,f671,f168,f1132,f311,f178,f173,f307])).

fof(f1132,plain,
    ( spl9_118
  <=> ! [X0] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK5))
        | ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f1121,plain,
    ( ! [X0] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK5))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK1) )
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(resolution,[],[f715,f170])).

fof(f1120,plain,
    ( ~ spl9_37
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | spl9_117
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f1104,f667,f198,f1118,f307,f208,f203,f319])).

fof(f1118,plain,
    ( spl9_117
  <=> ! [X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK4))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f1104,plain,
    ( ! [X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK0,sK1,sK5,X1),sK4))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK0) )
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(resolution,[],[f676,f200])).

fof(f1116,plain,
    ( ~ spl9_34
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_35
    | spl9_116
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f1103,f667,f168,f1114,f311,f178,f173,f307])).

fof(f1114,plain,
    ( spl9_116
  <=> ! [X0] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK4))
        | ~ l1_struct_0(X0)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f1103,plain,
    ( ! [X0] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(sK1,sK2,sK4,X0),sK4))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK1) )
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(resolution,[],[f676,f170])).

fof(f1055,plain,
    ( spl9_115
    | ~ spl9_88
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_111 ),
    inference(avatar_split_clause,[],[f1038,f1009,f198,f208,f727,f1052])).

fof(f1052,plain,
    ( spl9_115
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f1038,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK5,sK5))
    | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK5),sK5))
    | ~ spl9_18
    | ~ spl9_111 ),
    inference(resolution,[],[f1010,f200])).

fof(f1050,plain,
    ( spl9_114
    | ~ spl9_87
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_111 ),
    inference(avatar_split_clause,[],[f1037,f1009,f168,f178,f722,f1047])).

fof(f1047,plain,
    ( spl9_114
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK5),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f1037,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK5),sK5))
    | ~ spl9_12
    | ~ spl9_111 ),
    inference(resolution,[],[f1010,f170])).

fof(f1030,plain,
    ( spl9_113
    | ~ spl9_53
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f1013,f1005,f198,f208,f457,f1027])).

fof(f1013,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK5))
    | ~ spl9_18
    | ~ spl9_110 ),
    inference(resolution,[],[f1006,f200])).

fof(f1025,plain,
    ( spl9_112
    | ~ spl9_86
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f1012,f1005,f168,f178,f682,f1022])).

fof(f1022,plain,
    ( spl9_112
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f1012,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK5))
    | ~ spl9_12
    | ~ spl9_110 ),
    inference(resolution,[],[f1006,f170])).

fof(f1011,plain,
    ( ~ spl9_20
    | spl9_111
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f996,f671,f198,f1009,f208])).

fof(f996,plain,
    ( ! [X4,X5,X3] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK5))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | ~ v1_funct_1(X3) )
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(resolution,[],[f718,f200])).

fof(f1007,plain,
    ( ~ spl9_14
    | spl9_110
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f995,f671,f168,f1005,f178])).

fof(f995,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK5))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) )
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(resolution,[],[f718,f170])).

fof(f970,plain,
    ( ~ spl9_20
    | ~ spl9_88
    | spl9_109
    | ~ spl9_18
    | ~ spl9_105 ),
    inference(avatar_split_clause,[],[f953,f914,f198,f967,f727,f208])).

fof(f967,plain,
    ( spl9_109
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK5),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f953,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK5),sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,sK5))
    | ~ v1_funct_1(sK5)
    | ~ spl9_18
    | ~ spl9_105 ),
    inference(resolution,[],[f915,f200])).

fof(f965,plain,
    ( ~ spl9_14
    | ~ spl9_87
    | spl9_108
    | ~ spl9_12
    | ~ spl9_105 ),
    inference(avatar_split_clause,[],[f952,f914,f168,f962,f722,f178])).

fof(f962,plain,
    ( spl9_108
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK5),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f952,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK5),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ v1_funct_1(sK4)
    | ~ spl9_12
    | ~ spl9_105 ),
    inference(resolution,[],[f915,f170])).

fof(f937,plain,
    ( ~ spl9_20
    | ~ spl9_53
    | spl9_107
    | ~ spl9_18
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f920,f910,f198,f934,f457,f208])).

fof(f920,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK5,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(sK5)
    | ~ spl9_18
    | ~ spl9_104 ),
    inference(resolution,[],[f911,f200])).

fof(f932,plain,
    ( ~ spl9_14
    | ~ spl9_86
    | spl9_106
    | ~ spl9_12
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f919,f910,f168,f929,f682,f178])).

fof(f929,plain,
    ( spl9_106
  <=> v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f919,plain,
    ( v1_funct_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4))
    | ~ v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ v1_funct_1(sK4)
    | ~ spl9_12
    | ~ spl9_104 ),
    inference(resolution,[],[f911,f170])).

fof(f916,plain,
    ( spl9_105
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f901,f667,f198,f208,f914])).

fof(f901,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(sK5)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_1(k5_relat_1(X3,sK5))
        | v1_funct_1(k5_relat_1(k5_relat_1(X3,sK5),sK4)) )
    | ~ spl9_18
    | ~ spl9_84 ),
    inference(resolution,[],[f697,f200])).

fof(f912,plain,
    ( spl9_104
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f900,f667,f168,f178,f910])).

fof(f900,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k5_relat_1(X0,sK4))
        | v1_funct_1(k5_relat_1(k5_relat_1(X0,sK4),sK4)) )
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(resolution,[],[f697,f170])).

fof(f877,plain,
    ( ~ spl9_19
    | ~ spl9_103
    | ~ spl9_20
    | ~ spl9_65
    | ~ spl9_66
    | ~ spl9_18
    | spl9_68 ),
    inference(avatar_split_clause,[],[f865,f543,f198,f535,f531,f208,f874,f203])).

fof(f874,plain,
    ( spl9_103
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f531,plain,
    ( spl9_65
  <=> v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f535,plain,
    ( spl9_66
  <=> v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f543,plain,
    ( spl9_68
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f865,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl9_68 ),
    inference(resolution,[],[f382,f545])).

fof(f545,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),sK5)
    | spl9_68 ),
    inference(avatar_component_clause,[],[f543])).

fof(f382,plain,(
    ! [X21,X19,X20] :
      ( r2_funct_2(X20,X21,sK6(k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
      | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(X20,X21))),X20,X21)
      | ~ v1_funct_1(X19)
      | ~ r2_funct_2(X20,X21,X19,sK6(k1_zfmisc_1(k2_zfmisc_1(X20,X21))))
      | ~ v1_funct_2(X19,X20,X21) ) ),
    inference(resolution,[],[f103,f96])).

fof(f872,plain,
    ( ~ spl9_13
    | ~ spl9_102
    | ~ spl9_14
    | ~ spl9_60
    | ~ spl9_61
    | ~ spl9_12
    | spl9_63 ),
    inference(avatar_split_clause,[],[f864,f517,f168,f509,f505,f178,f869,f173])).

fof(f869,plain,
    ( spl9_102
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f505,plain,
    ( spl9_60
  <=> v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f509,plain,
    ( spl9_61
  <=> v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f517,plain,
    ( spl9_63
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f864,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))
    | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | spl9_63 ),
    inference(resolution,[],[f382,f519])).

fof(f519,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),sK4)
    | spl9_63 ),
    inference(avatar_component_clause,[],[f517])).

fof(f857,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_101
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f806,f343,f855,f123,f118,f113])).

fof(f343,plain,
    ( spl9_41
  <=> ! [X3,X2] :
        ( ~ v1_funct_1(X2)
        | v1_funct_1(k5_relat_1(X2,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f806,plain,
    ( ! [X57,X56,X55] :
        ( ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(sK0))))
        | ~ v1_funct_1(X55)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_2(X55,u1_struct_0(X56),u1_struct_0(sK0))
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X56,sK0,X55,X57),sK5))
        | ~ v1_funct_1(k2_tmap_1(X56,sK0,X55,X57))
        | ~ v1_funct_2(k2_tmap_1(X56,sK0,X55,X57),u1_struct_0(X56),u1_struct_0(sK0)) )
    | ~ spl9_41 ),
    inference(resolution,[],[f400,f344])).

fof(f344,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | v1_funct_1(k5_relat_1(X2,sK5))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0)) )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f343])).

fof(f853,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_100
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f805,f426,f851,f123,f118,f113])).

fof(f805,plain,
    ( ! [X54,X52,X53] :
        ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(sK0))))
        | ~ v1_funct_1(X52)
        | ~ v2_pre_topc(X53)
        | ~ l1_pre_topc(X53)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_funct_2(X52,u1_struct_0(X53),u1_struct_0(sK0))
        | ~ m1_pre_topc(X54,X53)
        | v2_struct_0(X53)
        | v1_funct_2(k5_relat_1(k2_tmap_1(X53,sK0,X52,X54),sK5),u1_struct_0(X53),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X53,sK0,X52,X54))
        | ~ v1_funct_2(k2_tmap_1(X53,sK0,X52,X54),u1_struct_0(X53),u1_struct_0(sK0)) )
    | ~ spl9_51 ),
    inference(resolution,[],[f400,f427])).

fof(f849,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_99
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f804,f335,f847,f138,f133,f128])).

fof(f804,plain,
    ( ! [X50,X51,X49] :
        ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(sK1))))
        | ~ v1_funct_1(X49)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X49,u1_struct_0(X50),u1_struct_0(sK1))
        | ~ m1_pre_topc(X51,X50)
        | v2_struct_0(X50)
        | v1_funct_1(k5_relat_1(k2_tmap_1(X50,sK1,X49,X51),sK4))
        | ~ v1_funct_1(k2_tmap_1(X50,sK1,X49,X51))
        | ~ v1_funct_2(k2_tmap_1(X50,sK1,X49,X51),u1_struct_0(X50),u1_struct_0(sK1)) )
    | ~ spl9_39 ),
    inference(resolution,[],[f400,f336])).

fof(f845,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_98
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f803,f394,f843,f138,f133,f128])).

fof(f803,plain,
    ( ! [X47,X48,X46] :
        ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(sK1))))
        | ~ v1_funct_1(X46)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X46,u1_struct_0(X47),u1_struct_0(sK1))
        | ~ m1_pre_topc(X48,X47)
        | v2_struct_0(X47)
        | v1_funct_2(k5_relat_1(k2_tmap_1(X47,sK1,X46,X48),sK4),u1_struct_0(X47),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(X47,sK1,X46,X48))
        | ~ v1_funct_2(k2_tmap_1(X47,sK1,X46,X48),u1_struct_0(X47),u1_struct_0(sK1)) )
    | ~ spl9_46 ),
    inference(resolution,[],[f400,f395])).

fof(f841,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_97
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f802,f363,f839,f118,f113,f138,f133,f128,f123])).

fof(f802,plain,
    ( ! [X45,X44] :
        ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(X44)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X44,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X45,sK0)
        | v2_struct_0(sK0)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X44,X45),sK5)
        | sK5 = k2_tmap_1(sK0,sK1,X44,X45)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X44,X45))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X44,X45),u1_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl9_43 ),
    inference(resolution,[],[f400,f364])).

fof(f837,plain,
    ( spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_96
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f801,f388,f835,f118,f113,f138,f133,f128,f123])).

fof(f801,plain,
    ( ! [X43,X42] :
        ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(X42)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X42,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X43,sK0)
        | v2_struct_0(sK0)
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(sK0,sK1,X42,X43))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X42,X43),sK5)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X42,X43))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X42,X43),u1_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl9_45 ),
    inference(resolution,[],[f400,f389])).

fof(f833,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_95
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f800,f359,f831,f133,f128,f153,f148,f143,f138])).

fof(f800,plain,
    ( ! [X41,X40] :
        ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(X40)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(X40,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X41,sK1)
        | v2_struct_0(sK1)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X40,X41),sK4)
        | sK4 = k2_tmap_1(sK1,sK2,X40,X41)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X40,X41))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X40,X41),u1_struct_0(sK1),u1_struct_0(sK2)) )
    | ~ spl9_42 ),
    inference(resolution,[],[f400,f360])).

fof(f829,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_94
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f799,f384,f827,f133,f128,f153,f148,f143,f138])).

fof(f799,plain,
    ( ! [X39,X38] :
        ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(X38)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_2(X38,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_pre_topc(X39,sK1)
        | v2_struct_0(sK1)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(sK1,sK2,X38,X39))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,X38,X39),sK4)
        | ~ v1_funct_1(k2_tmap_1(sK1,sK2,X38,X39))
        | ~ v1_funct_2(k2_tmap_1(sK1,sK2,X38,X39),u1_struct_0(sK1),u1_struct_0(sK2)) )
    | ~ spl9_44 ),
    inference(resolution,[],[f400,f385])).

fof(f825,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_93
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f818,f436,f823,f138,f133,f128])).

fof(f818,plain,
    ( ! [X37,X35,X36] :
        ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(sK1))))
        | ~ v1_funct_1(X35)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X35,u1_struct_0(X36),u1_struct_0(sK1))
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | v5_pre_topc(k5_relat_1(k2_tmap_1(X36,sK1,X35,X37),sK4),X36,sK2)
        | ~ v5_pre_topc(k2_tmap_1(X36,sK1,X35,X37),X36,sK1)
        | ~ v1_funct_1(k2_tmap_1(X36,sK1,X35,X37))
        | ~ v1_funct_2(k2_tmap_1(X36,sK1,X35,X37),u1_struct_0(X36),u1_struct_0(sK1)) )
    | ~ spl9_52 ),
    inference(duplicate_literal_removal,[],[f798])).

fof(f798,plain,
    ( ! [X37,X35,X36] :
        ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(sK1))))
        | ~ v1_funct_1(X35)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(X35,u1_struct_0(X36),u1_struct_0(sK1))
        | ~ m1_pre_topc(X37,X36)
        | v2_struct_0(X36)
        | v5_pre_topc(k5_relat_1(k2_tmap_1(X36,sK1,X35,X37),sK4),X36,sK2)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ v5_pre_topc(k2_tmap_1(X36,sK1,X35,X37),X36,sK1)
        | ~ v1_funct_1(k2_tmap_1(X36,sK1,X35,X37))
        | ~ v1_funct_2(k2_tmap_1(X36,sK1,X35,X37),u1_struct_0(X36),u1_struct_0(sK1))
        | ~ l1_pre_topc(X36) )
    | ~ spl9_52 ),
    inference(resolution,[],[f400,f437])).

fof(f781,plain,
    ( ~ spl9_37
    | spl9_92
    | ~ spl9_34
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f766,f198,f208,f203,f307,f779,f319])).

fof(f779,plain,
    ( spl9_92
  <=> ! [X3,X2] :
        ( ~ l1_struct_0(X2)
        | m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))
        | ~ r2_hidden(X3,k2_tmap_1(sK0,sK1,sK5,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f766,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(X3,k2_tmap_1(sK0,sK1,sK5,X2))
        | m1_subset_1(X3,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))) )
    | ~ spl9_18 ),
    inference(resolution,[],[f374,f200])).

fof(f777,plain,
    ( ~ spl9_34
    | spl9_91
    | ~ spl9_35
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f765,f168,f178,f173,f311,f775,f307])).

fof(f775,plain,
    ( spl9_91
  <=> ! [X1,X0] :
        ( ~ l1_struct_0(X0)
        | m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))
        | ~ r2_hidden(X1,k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f765,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK1)
        | ~ r2_hidden(X1,k2_tmap_1(sK1,sK2,sK4,X0))
        | m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f374,f170])).

fof(f755,plain,
    ( ~ spl9_37
    | spl9_90
    | ~ spl9_34
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f740,f198,f208,f203,f307,f753,f319])).

fof(f753,plain,
    ( spl9_90
  <=> ! [X3,X2] :
        ( ~ l1_struct_0(X2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))
        | ~ r2_hidden(X3,k2_tmap_1(sK0,sK1,sK5,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f740,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(sK0)
        | ~ r2_hidden(X3,k2_tmap_1(sK0,sK1,sK5,X2))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))) )
    | ~ spl9_18 ),
    inference(resolution,[],[f375,f200])).

fof(f751,plain,
    ( ~ spl9_34
    | spl9_89
    | ~ spl9_35
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f739,f168,f178,f173,f311,f749,f307])).

fof(f749,plain,
    ( spl9_89
  <=> ! [X1,X0] :
        ( ~ l1_struct_0(X0)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))
        | ~ r2_hidden(X1,k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f739,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(sK1)
        | ~ r2_hidden(X1,k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f375,f170])).

fof(f730,plain,
    ( spl9_88
    | ~ spl9_20
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f714,f671,f198,f208,f727])).

fof(f714,plain,
    ( ~ v1_funct_1(sK5)
    | v1_funct_1(k5_relat_1(sK5,sK5))
    | ~ spl9_18
    | ~ spl9_85 ),
    inference(resolution,[],[f672,f200])).

fof(f725,plain,
    ( spl9_87
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f713,f671,f168,f178,f722])).

fof(f713,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k5_relat_1(sK4,sK5))
    | ~ spl9_12
    | ~ spl9_85 ),
    inference(resolution,[],[f672,f170])).

fof(f685,plain,
    ( spl9_86
    | ~ spl9_14
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f674,f667,f168,f178,f682])).

fof(f674,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k5_relat_1(sK4,sK4))
    | ~ spl9_12
    | ~ spl9_84 ),
    inference(resolution,[],[f668,f170])).

fof(f673,plain,
    ( ~ spl9_20
    | spl9_85
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f660,f198,f671,f208])).

fof(f660,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(sK5)
        | v1_funct_1(k5_relat_1(X3,sK5))
        | ~ v1_funct_1(X3) )
    | ~ spl9_18 ),
    inference(resolution,[],[f286,f200])).

fof(f669,plain,
    ( ~ spl9_14
    | spl9_84
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f659,f168,f667,f178])).

fof(f659,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(sK4)
        | v1_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_funct_1(X0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f286,f170])).

fof(f652,plain,
    ( ~ spl9_78
    | ~ spl9_79
    | spl9_83
    | ~ spl9_80
    | spl9_82
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f598,f363,f644,f636,f649,f632,f628])).

fof(f628,plain,
    ( spl9_78
  <=> v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f632,plain,
    ( spl9_79
  <=> v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f649,plain,
    ( spl9_83
  <=> sK5 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f636,plain,
    ( spl9_80
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f598,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),sK5)
    | sK5 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_43 ),
    inference(resolution,[],[f575,f364])).

fof(f647,plain,
    ( ~ spl9_78
    | ~ spl9_79
    | ~ spl9_80
    | spl9_81
    | spl9_82
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f597,f388,f644,f640,f636,f632,f628])).

fof(f640,plain,
    ( spl9_81
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f597,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))))
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))
    | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),sK5)
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_45 ),
    inference(resolution,[],[f575,f389])).

fof(f626,plain,
    ( ~ spl9_72
    | ~ spl9_73
    | spl9_77
    | ~ spl9_74
    | spl9_76
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f596,f359,f618,f610,f623,f606,f602])).

fof(f602,plain,
    ( spl9_72
  <=> v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f606,plain,
    ( spl9_73
  <=> v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f623,plain,
    ( spl9_77
  <=> sK4 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f610,plain,
    ( spl9_74
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f596,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),sK4)
    | sK4 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_42 ),
    inference(resolution,[],[f575,f360])).

fof(f621,plain,
    ( ~ spl9_72
    | ~ spl9_73
    | ~ spl9_74
    | spl9_75
    | spl9_76
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f595,f384,f618,f614,f610,f606,f602])).

fof(f614,plain,
    ( spl9_75
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f595,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))))
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))
    | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),sK4)
    | ~ v1_funct_1(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))))
    | ~ v1_funct_2(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_44 ),
    inference(resolution,[],[f575,f385])).

fof(f574,plain,
    ( ~ spl9_34
    | spl9_71
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f567,f436,f572,f307])).

fof(f572,plain,
    ( spl9_71
  <=> ! [X1,X0,X2] :
        ( v5_pre_topc(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4),X2,sK2)
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2))
        | ~ v5_pre_topc(k2_tmap_1(X0,sK1,X1,X2),X2,sK1)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f567,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4),X2,sK2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(k2_tmap_1(X0,sK1,X1,X2),X2,sK1)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_pre_topc(X2)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_52 ),
    inference(resolution,[],[f437,f87])).

fof(f565,plain,
    ( ~ spl9_37
    | ~ spl9_34
    | spl9_70
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f558,f388,f563,f307,f319])).

fof(f563,plain,
    ( spl9_70
  <=> ! [X1,X0] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(X0,sK1,X1,sK0))
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK0))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK0),sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f558,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,k2_tmap_1(X0,sK1,X1,sK0))
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK0),sK5)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK0))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X0) )
    | ~ spl9_45 ),
    inference(resolution,[],[f389,f87])).

fof(f555,plain,
    ( ~ spl9_34
    | ~ spl9_35
    | spl9_69
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f548,f384,f553,f311,f307])).

fof(f553,plain,
    ( spl9_69
  <=> ! [X1,X0] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(X0,sK2,X1,sK1))
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK2,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(X0,sK2,X1,sK1))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X1,sK1),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,k2_tmap_1(X0,sK2,X1,sK1))
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X1,sK1),sK4)
        | ~ v1_funct_1(k2_tmap_1(X0,sK2,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK2,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X0) )
    | ~ spl9_44 ),
    inference(resolution,[],[f385,f87])).

fof(f546,plain,
    ( ~ spl9_65
    | ~ spl9_66
    | spl9_67
    | ~ spl9_68
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f525,f363,f543,f539,f535,f531])).

fof(f539,plain,
    ( spl9_67
  <=> sK5 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f525,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),sK5)
    | sK5 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))))
    | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_43 ),
    inference(resolution,[],[f364,f96])).

fof(f529,plain,
    ( ~ spl9_37
    | ~ spl9_34
    | spl9_64
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f522,f363,f527,f307,f319])).

fof(f527,plain,
    ( spl9_64
  <=> ! [X1,X0] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK0),sK5)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK0))
        | sK5 = k2_tmap_1(X0,sK1,X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f522,plain,
    ( ! [X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X1,sK0),sK5)
        | sK5 = k2_tmap_1(X0,sK1,X1,sK0)
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,sK0))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,sK0),u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X0) )
    | ~ spl9_43 ),
    inference(resolution,[],[f364,f87])).

fof(f520,plain,
    ( ~ spl9_60
    | ~ spl9_61
    | spl9_62
    | ~ spl9_63
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f499,f359,f517,f513,f509,f505])).

fof(f513,plain,
    ( spl9_62
  <=> sK4 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f499,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),sK4)
    | sK4 = sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))))
    | ~ v1_funct_2(sK6(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_42 ),
    inference(resolution,[],[f360,f96])).

fof(f503,plain,
    ( ~ spl9_34
    | ~ spl9_35
    | spl9_59
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f496,f359,f501,f311,f307])).

fof(f501,plain,
    ( spl9_59
  <=> ! [X1,X0] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X1,sK1),sK4)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK2,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(X0,sK2,X1,sK1))
        | sK4 = k2_tmap_1(X0,sK2,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f496,plain,
    ( ! [X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X1,sK1),sK4)
        | sK4 = k2_tmap_1(X0,sK2,X1,sK1)
        | ~ v1_funct_1(k2_tmap_1(X0,sK2,X1,sK1))
        | ~ v1_funct_2(k2_tmap_1(X0,sK2,X1,sK1),u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X0) )
    | ~ spl9_42 ),
    inference(resolution,[],[f360,f87])).

fof(f494,plain,
    ( ~ spl9_37
    | spl9_58
    | ~ spl9_51 ),
    inference(avatar_split_clause,[],[f487,f426,f492,f319])).

fof(f487,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK0,X1,X2),sK5),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,X2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,X2),u1_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_51 ),
    inference(resolution,[],[f427,f87])).

fof(f486,plain,
    ( ~ spl9_34
    | spl9_57
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f474,f394,f484,f307])).

fof(f474,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4),u1_struct_0(X2),u1_struct_0(sK2))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_46 ),
    inference(resolution,[],[f395,f87])).

fof(f482,plain,
    ( ~ spl9_19
    | ~ spl9_20
    | spl9_56
    | ~ spl9_18
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f473,f394,f198,f479,f208,f203])).

fof(f473,plain,
    ( v1_funct_2(k5_relat_1(sK5,sK4),u1_struct_0(sK0),u1_struct_0(sK2))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_18
    | ~ spl9_46 ),
    inference(resolution,[],[f395,f200])).

fof(f472,plain,
    ( ~ spl9_37
    | spl9_55
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f465,f343,f470,f319])).

fof(f470,plain,
    ( spl9_55
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK0,X1,X2),sK5))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,X2),u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f465,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK0,X1,X2),sK5))
        | ~ v1_funct_1(k2_tmap_1(X0,sK0,X1,X2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK0,X1,X2),u1_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_41 ),
    inference(resolution,[],[f344,f87])).

fof(f464,plain,
    ( ~ spl9_34
    | spl9_54
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f452,f335,f462,f307])).

fof(f462,plain,
    ( spl9_54
  <=> ! [X1,X0,X2] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f452,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_1(k5_relat_1(k2_tmap_1(X0,sK1,X1,X2),sK4))
        | ~ v1_funct_1(k2_tmap_1(X0,sK1,X1,X2))
        | ~ v1_funct_2(k2_tmap_1(X0,sK1,X1,X2),u1_struct_0(X2),u1_struct_0(sK1))
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ l1_struct_0(X2)
        | ~ l1_struct_0(X0) )
    | ~ spl9_39 ),
    inference(resolution,[],[f336,f87])).

fof(f460,plain,
    ( ~ spl9_19
    | ~ spl9_20
    | spl9_53
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f451,f335,f198,f457,f208,f203])).

fof(f451,plain,
    ( v1_funct_1(k5_relat_1(sK5,sK4))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_18
    | ~ spl9_39 ),
    inference(resolution,[],[f336,f200])).

fof(f438,plain,
    ( ~ spl9_17
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | spl9_52
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f429,f168,f436,f138,f133,f128,f153,f148,f143,f178,f173,f193])).

fof(f193,plain,
    ( spl9_17
  <=> v5_pre_topc(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f429,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v5_pre_topc(sK4,sK1,sK2)
        | v2_struct_0(X0)
        | v5_pre_topc(k5_relat_1(X1,sK4),X0,sK2) )
    | ~ spl9_12 ),
    inference(resolution,[],[f91,f170])).

fof(f428,plain,
    ( spl9_40
    | ~ spl9_19
    | ~ spl9_20
    | spl9_51
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f349,f198,f426,f208,f203,f339])).

fof(f349,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_2(k5_relat_1(X2,sK5),X3,u1_struct_0(sK1)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f98,f200])).

fof(f424,plain,
    ( spl9_3
    | ~ spl9_37
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f423,f339,f319,f123])).

fof(f423,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_40 ),
    inference(resolution,[],[f341,f104])).

fof(f341,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f339])).

fof(f422,plain,
    ( ~ spl9_49
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_50
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f410,f198,f420,f123,f118,f113,f138,f133,f128,f208,f203,f416])).

fof(f416,plain,
    ( spl9_49
  <=> v5_pre_topc(sK5,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f420,plain,
    ( spl9_50
  <=> ! [X3,X2] :
        ( ~ v2_pre_topc(X2)
        | v1_funct_1(k5_relat_1(X3,sK5))
        | v2_struct_0(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v5_pre_topc(X3,X2,sK0)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f410,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK0))
        | ~ v5_pre_topc(X3,X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK5,sK0,sK1)
        | v2_struct_0(X2)
        | v1_funct_1(k5_relat_1(X3,sK5)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f89,f200])).

fof(f408,plain,
    ( spl9_3
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6
    | ~ spl9_1
    | ~ spl9_2
    | spl9_48
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f398,f264,f406,f118,f113,f138,f133,f128,f208,f203,f198,f123])).

fof(f264,plain,
    ( spl9_29
  <=> ! [X1] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f398,plain,
    ( ! [X1] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_29 ),
    inference(superposition,[],[f265,f88])).

fof(f265,plain,
    ( ! [X1] : v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f264])).

fof(f404,plain,
    ( spl9_6
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_4
    | ~ spl9_5
    | spl9_47
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f397,f260,f402,f133,f128,f153,f148,f143,f178,f173,f168,f138])).

fof(f402,plain,
    ( spl9_47
  <=> ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f260,plain,
    ( spl9_28
  <=> ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f397,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK2)
        | ~ v2_pre_topc(sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(sK1) )
    | ~ spl9_28 ),
    inference(superposition,[],[f261,f88])).

fof(f261,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f260])).

fof(f396,plain,
    ( spl9_38
    | ~ spl9_13
    | ~ spl9_14
    | spl9_46
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f348,f168,f394,f178,f173,f331])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_funct_2(k5_relat_1(X0,sK4),X1,u1_struct_0(sK2)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f98,f170])).

fof(f392,plain,
    ( spl9_6
    | ~ spl9_34
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f391,f331,f307,f138])).

fof(f391,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_38 ),
    inference(resolution,[],[f333,f104])).

fof(f333,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f331])).

fof(f390,plain,
    ( ~ spl9_19
    | ~ spl9_20
    | spl9_45
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f378,f198,f388,f208,f203])).

fof(f378,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5)
        | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1) )
    | ~ spl9_18 ),
    inference(resolution,[],[f103,f200])).

fof(f386,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | spl9_44
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f377,f168,f384,f178,f173])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4)
        | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f103,f170])).

fof(f367,plain,
    ( ~ spl9_1
    | spl9_37 ),
    inference(avatar_split_clause,[],[f366,f319,f113])).

fof(f366,plain,
    ( ~ l1_pre_topc(sK0)
    | spl9_37 ),
    inference(resolution,[],[f321,f109])).

fof(f321,plain,
    ( ~ l1_struct_0(sK0)
    | spl9_37 ),
    inference(avatar_component_clause,[],[f319])).

fof(f365,plain,
    ( ~ spl9_19
    | ~ spl9_20
    | spl9_43
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f354,f198,f363,f208,f203])).

fof(f354,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | sK5 = X1
        | ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X1,sK5) )
    | ~ spl9_18 ),
    inference(resolution,[],[f102,f200])).

fof(f361,plain,
    ( ~ spl9_13
    | ~ spl9_14
    | spl9_42
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f353,f168,f359,f178,f173])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | sK4 = X0
        | ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),X0,sK4) )
    | ~ spl9_12 ),
    inference(resolution,[],[f102,f170])).

fof(f347,plain,
    ( ~ spl9_7
    | spl9_35 ),
    inference(avatar_split_clause,[],[f346,f311,f143])).

fof(f346,plain,
    ( ~ l1_pre_topc(sK2)
    | spl9_35 ),
    inference(resolution,[],[f313,f109])).

fof(f313,plain,
    ( ~ l1_struct_0(sK2)
    | spl9_35 ),
    inference(avatar_component_clause,[],[f311])).

fof(f345,plain,
    ( spl9_40
    | ~ spl9_19
    | ~ spl9_20
    | spl9_41
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f326,f198,f343,f208,f203,f339])).

fof(f326,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,u1_struct_0(sK0))))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_funct_1(k5_relat_1(X2,sK5)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f97,f200])).

fof(f337,plain,
    ( spl9_38
    | ~ spl9_13
    | ~ spl9_14
    | spl9_39
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f325,f168,f335,f178,f173,f331])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_funct_1(k5_relat_1(X0,sK4)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f97,f170])).

fof(f324,plain,
    ( ~ spl9_4
    | spl9_34 ),
    inference(avatar_split_clause,[],[f323,f307,f128])).

fof(f323,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_34 ),
    inference(resolution,[],[f309,f109])).

fof(f309,plain,
    ( ~ l1_struct_0(sK1)
    | spl9_34 ),
    inference(avatar_component_clause,[],[f307])).

fof(f322,plain,
    ( spl9_36
    | ~ spl9_37
    | ~ spl9_19
    | ~ spl9_20
    | ~ spl9_34
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f299,f198,f307,f208,f203,f319,f316])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_struct_0(sK0)
        | ~ l1_struct_0(X1)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK5,X1)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f85,f200])).

fof(f314,plain,
    ( spl9_33
    | ~ spl9_34
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_35
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f298,f168,f311,f178,f173,f307,f304])).

fof(f304,plain,
    ( spl9_33
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK2)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ l1_struct_0(sK1)
        | ~ l1_struct_0(X0)
        | v1_funct_1(k2_tmap_1(sK1,sK2,sK4,X0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f85,f170])).

fof(f291,plain,
    ( ~ spl9_20
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_32
    | spl9_15 ),
    inference(avatar_split_clause,[],[f284,f183,f288,f198,f178,f168,f208])).

fof(f284,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k5_relat_1(sK5,sK4),sK3),sK3,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | spl9_15 ),
    inference(superposition,[],[f185,f83])).

fof(f279,plain,
    ( spl9_31
    | ~ spl9_20
    | ~ spl9_19
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f268,f198,f203,f208,f276])).

fof(f276,plain,
    ( spl9_31
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f268,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK5,sK5)
    | ~ spl9_18 ),
    inference(resolution,[],[f111,f200])).

fof(f274,plain,
    ( spl9_30
    | ~ spl9_14
    | ~ spl9_13
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f267,f168,f173,f178,f271])).

fof(f271,plain,
    ( spl9_30
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f267,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK4,sK4)
    | ~ spl9_12 ),
    inference(resolution,[],[f111,f170])).

fof(f266,plain,
    ( spl9_29
    | ~ spl9_20
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f257,f198,f208,f264])).

fof(f257,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK5)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK5,X1)) )
    | ~ spl9_18 ),
    inference(resolution,[],[f99,f200])).

fof(f262,plain,
    ( spl9_28
    | ~ spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f256,f168,f178,f260])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK4,X0)) )
    | ~ spl9_12 ),
    inference(resolution,[],[f99,f170])).

fof(f252,plain,
    ( spl9_27
    | ~ spl9_2
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f245,f158,f113,f118,f249])).

fof(f245,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ spl9_10 ),
    inference(resolution,[],[f105,f160])).

fof(f160,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f244,plain,
    ( ~ spl9_25
    | spl9_26
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f227,f198,f242,f238])).

fof(f238,plain,
    ( spl9_25
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f242,plain,
    ( spl9_26
  <=> ! [X1] : ~ r2_hidden(X1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f227,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK5)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) )
    | ~ spl9_18 ),
    inference(resolution,[],[f92,f200])).

fof(f236,plain,
    ( ~ spl9_23
    | spl9_24
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f226,f168,f234,f230])).

fof(f230,plain,
    ( spl9_23
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f234,plain,
    ( spl9_24
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f92,f170])).

fof(f224,plain,
    ( spl9_22
    | ~ spl9_1
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f217,f158,f113,f221])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3)
    | ~ spl9_10 ),
    inference(resolution,[],[f107,f160])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f216,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f108,f213])).

fof(f213,plain,
    ( spl9_21
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f108,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_l1_pre_topc)).

fof(f211,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f61,f208])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v5_pre_topc(X4,X1,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2)
                          & v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                          & v5_pre_topc(X4,X1,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                                & v5_pre_topc(X4,X1,X2) )
                             => v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( v5_pre_topc(k2_tmap_1(X0,X1,X5,X3),X3,X1)
                              & v5_pre_topc(X4,X1,X2) )
                           => v5_pre_topc(k2_tmap_1(X0,X2,k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X5,X4),X3),X3,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tmap_1)).

fof(f206,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f62,f203])).

fof(f62,plain,(
    v1_funct_2(sK5,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f201,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f63,f198])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f196,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f64,f193])).

fof(f64,plain,(
    v5_pre_topc(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f191,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f65,f188])).

fof(f65,plain,(
    v5_pre_topc(k2_tmap_1(sK0,sK1,sK5,sK3),sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f186,plain,(
    ~ spl9_15 ),
    inference(avatar_split_clause,[],[f66,f183])).

fof(f66,plain,(
    ~ v5_pre_topc(k2_tmap_1(sK0,sK2,k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK4),sK3),sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f181,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f67,f178])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f176,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f68,f173])).

fof(f68,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f171,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f69,f168])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f166,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f70,f163])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f161,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f71,f158])).

fof(f71,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f156,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f72,f153])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f73,f148])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f74,f143])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f75,f138])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f76,f133])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f77,f128])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f126,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f78,f123])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f79,f118])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f116,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f80,f113])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------

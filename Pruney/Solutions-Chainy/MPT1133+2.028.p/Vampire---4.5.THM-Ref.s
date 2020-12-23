%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:33 EST 2020

% Result     : Theorem 8.67s
% Output     : Refutation 9.30s
% Verified   : 
% Statistics : Number of formulae       : 1668 (8961 expanded)
%              Number of leaves         :  251 (3435 expanded)
%              Depth                    :   21
%              Number of atoms          : 6835 (32087 expanded)
%              Number of equality atoms :  258 (5180 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f200,f208,f224,f225,f246,f251,f260,f265,f266,f267,f286,f295,f307,f312,f314,f316,f324,f329,f341,f376,f388,f395,f401,f403,f408,f440,f475,f496,f501,f511,f514,f521,f523,f528,f532,f534,f539,f590,f591,f592,f608,f613,f614,f623,f624,f625,f638,f643,f644,f684,f716,f725,f734,f749,f750,f758,f763,f764,f779,f784,f791,f794,f796,f797,f803,f804,f805,f827,f828,f847,f854,f857,f859,f860,f866,f867,f868,f882,f894,f899,f904,f910,f915,f920,f937,f941,f948,f956,f962,f969,f975,f984,f985,f987,f988,f992,f1009,f1041,f1051,f1056,f1073,f1074,f1082,f1087,f1088,f1102,f1109,f1112,f1114,f1115,f1121,f1122,f1123,f1137,f1139,f1145,f1147,f1149,f1155,f1157,f1159,f1160,f1161,f1195,f1196,f1217,f1224,f1227,f1229,f1230,f1236,f1237,f1238,f1258,f1270,f1295,f1296,f1297,f1299,f1316,f1319,f1320,f1409,f1418,f1419,f1436,f1441,f1442,f1447,f1455,f1459,f1467,f1471,f1488,f1493,f1498,f1522,f1526,f1530,f1537,f1542,f1547,f1549,f1551,f1556,f1557,f1566,f1572,f1594,f1596,f1603,f1606,f1608,f1610,f1612,f1621,f1625,f1639,f1662,f1669,f1671,f1689,f1694,f1699,f1704,f1705,f1710,f1715,f1721,f1726,f1753,f1760,f1764,f1769,f1770,f1771,f1772,f1778,f1782,f1785,f1788,f1792,f1794,f1800,f1804,f1823,f1907,f1913,f1918,f1931,f1936,f1939,f1963,f1981,f1994,f1997,f1999,f2000,f2002,f2003,f2005,f2007,f2014,f2020,f2024,f2030,f2034,f2036,f2043,f2052,f2054,f2057,f2061,f2063,f2066,f2069,f2073,f2078,f2084,f2103,f2107,f2110,f2114,f2163,f2168,f2169,f2174,f2205,f2223,f2228,f2233,f2234,f2239,f2244,f2249,f2297,f2304,f2332,f2350,f2413,f2416,f2419,f2421,f2425,f2429,f2431,f2434,f2440,f2444,f2448,f2451,f2454,f2457,f2465,f2468,f2470,f2515,f2521,f2526,f2539,f2545,f2548,f2551,f2575,f2593,f2607,f2618,f2648,f2652,f2656,f2660,f2664,f2668,f2672,f2676,f2680,f2684,f2686,f2695,f2697,f2702,f2709,f2711,f2726,f2733,f2735,f2740,f2752,f2755,f2761,f2763,f2764,f2766,f2788,f2794,f2800,f2802,f2852,f2854,f2873,f2880,f2882,f2884,f2891,f2894,f2896,f2898,f2900,f2903,f2919,f2926,f2931,f2933,f2934,f2951,f2957,f2958,f2959,f2965,f2967,f2968,f2969,f2970,f2971,f2992,f2997,f3002,f3007,f3012,f3013,f3018,f3023,f3028,f3033,f3047,f3051,f3055,f3058,f3076,f3083,f3088,f3090,f3091,f3114,f3119,f3124,f3129,f3134,f3139,f3144,f3149,f3154,f3155,f3160,f3165,f3174,f3178,f3182,f3186,f3189,f3210,f3215,f3217,f3265,f3302])).

fof(f3302,plain,
    ( ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_71
    | ~ spl7_81
    | spl7_83
    | ~ spl7_102 ),
    inference(avatar_contradiction_clause,[],[f3301])).

fof(f3301,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_71
    | ~ spl7_81
    | spl7_83
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f3300,f486])).

fof(f486,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
    | ~ spl7_14 ),
    inference(superposition,[],[f110,f348])).

fof(f348,plain,
    ( ! [X0] : k1_xboole_0 = sK6(X0,k1_xboole_0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f332,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f332,plain,
    ( ! [X0] : v1_xboole_0(sK6(X0,k1_xboole_0))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f199,f105,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f105,plain,(
    ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK6(X0,X1),X0,X1)
      & v1_funct_1(sK6(X0,X1))
      & v5_relat_1(sK6(X0,X1),X1)
      & v4_relat_1(sK6(X0,X1),X0)
      & v1_relat_1(sK6(X0,X1))
      & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK6(X0,X1),X0,X1)
        & v1_funct_1(sK6(X0,X1))
        & v5_relat_1(sK6(X0,X1),X1)
        & v4_relat_1(sK6(X0,X1),X0)
        & v1_relat_1(sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f199,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl7_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f110,plain,(
    ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f65])).

fof(f3300,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_71
    | ~ spl7_81
    | spl7_83
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f3296,f889])).

fof(f889,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f887])).

fof(f887,plain,
    ( spl7_71
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f3296,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_81
    | spl7_83
    | ~ spl7_102 ),
    inference(unit_resulting_resolution,[],[f194,f189,f184,f179,f495,f960,f230,f974,f230,f1294,f129])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f1294,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1292,plain,
    ( spl7_102
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f974,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_83 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl7_83
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f230,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f228,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f228,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f212,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f212,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f199,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f960,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl7_81
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f495,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl7_41
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f179,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl7_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f184,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl7_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f189,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f194,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl7_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f3265,plain,
    ( spl7_222
    | spl7_223
    | ~ spl7_185 ),
    inference(avatar_split_clause,[],[f3255,f2749,f3262,f3258])).

fof(f3258,plain,
    ( spl7_222
  <=> v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).

fof(f3262,plain,
    ( spl7_223
  <=> r2_hidden(sK4(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_223])])).

fof(f2749,plain,
    ( spl7_185
  <=> r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).

fof(f3255,plain,
    ( r2_hidden(sK4(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_185 ),
    inference(resolution,[],[f2751,f277])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f97,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2751,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_185 ),
    inference(avatar_component_clause,[],[f2749])).

fof(f3217,plain,
    ( spl7_220
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3216,f2329,f2301,f3207])).

fof(f3207,plain,
    ( spl7_220
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f2301,plain,
    ( spl7_166
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f2329,plain,
    ( spl7_168
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f3216,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))))
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(subsumption_resolution,[],[f3204,f2303])).

fof(f2303,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f3204,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))))
    | ~ spl7_168 ),
    inference(resolution,[],[f2330,f1357])).

fof(f1357,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ),
    inference(subsumption_resolution,[],[f1356,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1356,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f319,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f319,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) ),
    inference(resolution,[],[f85,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f85,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2330,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_168 ),
    inference(avatar_component_clause,[],[f2329])).

fof(f3215,plain,
    ( spl7_221
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3202,f2329,f2301,f3212])).

fof(f3212,plain,
    ( spl7_221
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_221])])).

fof(f3202,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2303,f2330,f85])).

fof(f3210,plain,
    ( spl7_220
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3203,f2329,f2301,f3207])).

fof(f3203,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))))
    | ~ spl7_166
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2303,f2330,f1357])).

fof(f3189,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(avatar_contradiction_clause,[],[f3188])).

fof(f3188,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(subsumption_resolution,[],[f3187,f230])).

fof(f3187,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3170,f123])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3170,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_114
    | spl7_126 ),
    inference(superposition,[],[f1602,f1466])).

fof(f1466,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_114 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f1464,plain,
    ( spl7_114
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f1602,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | spl7_126 ),
    inference(avatar_component_clause,[],[f1600])).

fof(f1600,plain,
    ( spl7_126
  <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f3186,plain,
    ( ~ spl7_14
    | ~ spl7_43
    | ~ spl7_58
    | spl7_126 ),
    inference(avatar_contradiction_clause,[],[f3185])).

fof(f3185,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_43
    | ~ spl7_58
    | spl7_126 ),
    inference(subsumption_resolution,[],[f3184,f230])).

fof(f3184,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_43
    | ~ spl7_58
    | spl7_126 ),
    inference(forward_demodulation,[],[f3183,f123])).

fof(f3183,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_43
    | ~ spl7_58
    | spl7_126 ),
    inference(forward_demodulation,[],[f3169,f510])).

fof(f510,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl7_43
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f3169,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_58
    | spl7_126 ),
    inference(superposition,[],[f1602,f748])).

fof(f748,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl7_58
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f3182,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(avatar_contradiction_clause,[],[f3181])).

fof(f3181,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(subsumption_resolution,[],[f3180,f212])).

fof(f3180,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3179,f123])).

fof(f3179,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3168,f1466])).

fof(f3168,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl7_126 ),
    inference(resolution,[],[f1602,f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(resolution,[],[f98,f101])).

fof(f3178,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(avatar_contradiction_clause,[],[f3177])).

fof(f3177,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(subsumption_resolution,[],[f3176,f212])).

fof(f3176,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3175,f123])).

fof(f3175,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3166,f1466])).

fof(f3166,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl7_126 ),
    inference(unit_resulting_resolution,[],[f1602,f229])).

fof(f3174,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(avatar_contradiction_clause,[],[f3173])).

fof(f3173,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_126 ),
    inference(subsumption_resolution,[],[f3172,f228])).

fof(f3172,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3171,f123])).

fof(f3171,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_114
    | spl7_126 ),
    inference(forward_demodulation,[],[f3167,f1466])).

fof(f3167,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0)
    | spl7_126 ),
    inference(unit_resulting_resolution,[],[f1602,f101])).

fof(f3165,plain,
    ( ~ spl7_219
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3092,f2017,f3162])).

fof(f3162,plain,
    ( spl7_219
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_219])])).

fof(f2017,plain,
    ( spl7_151
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

fof(f3092,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f2019,f82])).

fof(f2019,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | spl7_151 ),
    inference(avatar_component_clause,[],[f2017])).

fof(f3160,plain,
    ( ~ spl7_218
    | spl7_69
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3093,f2017,f875,f3157])).

fof(f3157,plain,
    ( spl7_218
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f875,plain,
    ( spl7_69
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f3093,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_69
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f876,f2019,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f876,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl7_69 ),
    inference(avatar_component_clause,[],[f875])).

fof(f3155,plain,
    ( ~ spl7_213
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3094,f2017,f3131])).

fof(f3131,plain,
    ( spl7_213
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).

fof(f3094,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f2019,f2019,f102])).

fof(f3154,plain,
    ( ~ spl7_217
    | spl7_65
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3095,f2017,f824,f3151])).

fof(f3151,plain,
    ( spl7_217
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_217])])).

fof(f824,plain,
    ( spl7_65
  <=> k1_xboole_0 = u1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f3095,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | spl7_65
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f825,f2019,f102])).

fof(f825,plain,
    ( k1_xboole_0 != u1_pre_topc(sK0)
    | spl7_65 ),
    inference(avatar_component_clause,[],[f824])).

fof(f3149,plain,
    ( ~ spl7_216
    | spl7_86
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3096,f2017,f1070,f3146])).

fof(f3146,plain,
    ( spl7_216
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f1070,plain,
    ( spl7_86
  <=> k1_xboole_0 = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f3096,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1))
    | spl7_86
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f1071,f2019,f102])).

fof(f1071,plain,
    ( k1_xboole_0 != u1_pre_topc(sK1)
    | spl7_86 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f3144,plain,
    ( ~ spl7_215
    | spl7_110
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3097,f2017,f1433,f3141])).

fof(f3141,plain,
    ( spl7_215
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).

fof(f1433,plain,
    ( spl7_110
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f3097,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_110
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f1435,f2019,f102])).

fof(f1435,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | spl7_110 ),
    inference(avatar_component_clause,[],[f1433])).

fof(f3139,plain,
    ( ~ spl7_214
    | spl7_69
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3099,f2017,f875,f3136])).

fof(f3136,plain,
    ( spl7_214
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f3099,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_69
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f876,f2019,f102])).

fof(f3134,plain,
    ( ~ spl7_213
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3100,f2017,f3131])).

fof(f3100,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f2019,f2019,f102])).

fof(f3129,plain,
    ( ~ spl7_212
    | spl7_65
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3101,f2017,f824,f3126])).

fof(f3126,plain,
    ( spl7_212
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f3101,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_65
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f825,f2019,f102])).

fof(f3124,plain,
    ( ~ spl7_211
    | spl7_86
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3102,f2017,f1070,f3121])).

fof(f3121,plain,
    ( spl7_211
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_211])])).

fof(f3102,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_86
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f1071,f2019,f102])).

fof(f3119,plain,
    ( ~ spl7_210
    | spl7_110
    | spl7_151 ),
    inference(avatar_split_clause,[],[f3103,f2017,f1433,f3116])).

fof(f3116,plain,
    ( spl7_210
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).

fof(f3103,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_110
    | spl7_151 ),
    inference(unit_resulting_resolution,[],[f1435,f2019,f102])).

fof(f3114,plain,
    ( ~ spl7_209
    | ~ spl7_14
    | ~ spl7_41
    | spl7_151
    | spl7_153 ),
    inference(avatar_split_clause,[],[f3105,f2040,f2017,f493,f197,f3111])).

fof(f3111,plain,
    ( spl7_209
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).

fof(f2040,plain,
    ( spl7_153
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f3105,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_151
    | spl7_153 ),
    inference(unit_resulting_resolution,[],[f2042,f495,f230,f2019,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f2042,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_153 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f3091,plain,
    ( spl7_208
    | ~ spl7_14
    | spl7_195 ),
    inference(avatar_split_clause,[],[f3061,f2948,f197,f3085])).

fof(f3085,plain,
    ( spl7_208
  <=> r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f2948,plain,
    ( spl7_195
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_195])])).

fof(f3061,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_14
    | spl7_195 ),
    inference(unit_resulting_resolution,[],[f212,f2950,f701])).

fof(f701,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK5(X1,X2),X1)
      | v1_xboole_0(X1)
      | r2_hidden(sK4(X1),X2) ) ),
    inference(resolution,[],[f277,f98])).

fof(f2950,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | spl7_195 ),
    inference(avatar_component_clause,[],[f2948])).

fof(f3090,plain,
    ( spl7_208
    | ~ spl7_14
    | spl7_195 ),
    inference(avatar_split_clause,[],[f3089,f2948,f197,f3085])).

fof(f3089,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_14
    | spl7_195 ),
    inference(forward_demodulation,[],[f3062,f571])).

fof(f571,plain,
    ( ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f558,f82])).

fof(f558,plain,
    ( ! [X0] : v1_xboole_0(sK6(k1_xboole_0,X0))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f235,f335])).

fof(f335,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f333,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl7_14 ),
    inference(resolution,[],[f92,f199])).

fof(f235,plain,(
    ! [X1] : m1_subset_1(sK6(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f105,f123])).

fof(f3062,plain,
    ( ! [X0] : r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),sK6(k1_xboole_0,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_14
    | spl7_195 ),
    inference(unit_resulting_resolution,[],[f551,f2950,f701])).

fof(f551,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,sK6(k1_xboole_0,X1))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f199,f235,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f3088,plain,
    ( spl7_208
    | ~ spl7_14
    | spl7_195 ),
    inference(avatar_split_clause,[],[f3063,f2948,f197,f3085])).

fof(f3063,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_14
    | spl7_195 ),
    inference(unit_resulting_resolution,[],[f2950,f690])).

fof(f690,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(X2,k1_xboole_0),X2)
        | v1_xboole_0(X2) )
    | ~ spl7_14 ),
    inference(resolution,[],[f229,f335])).

fof(f3083,plain,
    ( spl7_207
    | spl7_195 ),
    inference(avatar_split_clause,[],[f3064,f2948,f3073])).

fof(f3073,plain,
    ( spl7_207
  <=> r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).

fof(f3064,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl7_195 ),
    inference(unit_resulting_resolution,[],[f216,f2950,f277])).

fof(f216,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f201,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f201,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f3076,plain,
    ( spl7_207
    | spl7_195 ),
    inference(avatar_split_clause,[],[f3071,f2948,f3073])).

fof(f3071,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl7_195 ),
    inference(unit_resulting_resolution,[],[f2950,f91])).

fof(f3058,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(avatar_contradiction_clause,[],[f3057])).

fof(f3057,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(subsumption_resolution,[],[f3056,f228])).

fof(f3056,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_114
    | spl7_125 ),
    inference(forward_demodulation,[],[f3043,f123])).

fof(f3043,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_114
    | spl7_125 ),
    inference(superposition,[],[f1593,f1466])).

fof(f1593,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0)
    | spl7_125 ),
    inference(avatar_component_clause,[],[f1591])).

fof(f1591,plain,
    ( spl7_125
  <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f3055,plain,
    ( ~ spl7_14
    | ~ spl7_43
    | ~ spl7_58
    | spl7_125 ),
    inference(avatar_contradiction_clause,[],[f3054])).

fof(f3054,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_43
    | ~ spl7_58
    | spl7_125 ),
    inference(subsumption_resolution,[],[f3053,f228])).

fof(f3053,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_43
    | ~ spl7_58
    | spl7_125 ),
    inference(forward_demodulation,[],[f3052,f123])).

fof(f3052,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_43
    | ~ spl7_58
    | spl7_125 ),
    inference(forward_demodulation,[],[f3042,f510])).

fof(f3042,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_58
    | spl7_125 ),
    inference(superposition,[],[f1593,f748])).

fof(f3051,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(avatar_contradiction_clause,[],[f3050])).

fof(f3050,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(subsumption_resolution,[],[f3049,f212])).

fof(f3049,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_114
    | spl7_125 ),
    inference(forward_demodulation,[],[f3048,f123])).

fof(f3048,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_114
    | spl7_125 ),
    inference(forward_demodulation,[],[f3041,f1466])).

fof(f3041,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl7_125 ),
    inference(resolution,[],[f1593,f98])).

fof(f3047,plain,
    ( ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(avatar_contradiction_clause,[],[f3046])).

fof(f3046,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_114
    | spl7_125 ),
    inference(subsumption_resolution,[],[f3045,f212])).

fof(f3045,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_114
    | spl7_125 ),
    inference(forward_demodulation,[],[f3044,f123])).

fof(f3044,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_114
    | spl7_125 ),
    inference(forward_demodulation,[],[f3039,f1466])).

fof(f3039,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))
    | spl7_125 ),
    inference(unit_resulting_resolution,[],[f1593,f98])).

fof(f3033,plain,
    ( ~ spl7_206
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2972,f1433,f3030])).

fof(f3030,plain,
    ( spl7_206
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f2972,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f1435,f82])).

fof(f3028,plain,
    ( ~ spl7_205
    | spl7_69
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2973,f1433,f875,f3025])).

fof(f3025,plain,
    ( spl7_205
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_205])])).

fof(f2973,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl7_69
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f876,f1435,f102])).

fof(f3023,plain,
    ( ~ spl7_204
    | spl7_65
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2974,f1433,f824,f3020])).

fof(f3020,plain,
    ( spl7_204
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).

fof(f2974,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK0))
    | spl7_65
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f825,f1435,f102])).

fof(f3018,plain,
    ( ~ spl7_203
    | spl7_86
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2975,f1433,f1070,f3015])).

fof(f3015,plain,
    ( spl7_203
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).

fof(f2975,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK1))
    | spl7_86
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f1071,f1435,f102])).

fof(f3013,plain,
    ( ~ spl7_199
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2976,f1433,f2994])).

fof(f2994,plain,
    ( spl7_199
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_199])])).

fof(f2976,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f1435,f1435,f102])).

fof(f3012,plain,
    ( ~ spl7_202
    | spl7_69
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2978,f1433,f875,f3009])).

fof(f3009,plain,
    ( spl7_202
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_202])])).

fof(f2978,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_69
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f876,f1435,f102])).

fof(f3007,plain,
    ( ~ spl7_201
    | spl7_65
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2979,f1433,f824,f3004])).

fof(f3004,plain,
    ( spl7_201
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).

fof(f2979,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_65
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f825,f1435,f102])).

fof(f3002,plain,
    ( ~ spl7_200
    | spl7_86
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2980,f1433,f1070,f2999])).

fof(f2999,plain,
    ( spl7_200
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f2980,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_86
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f1071,f1435,f102])).

fof(f2997,plain,
    ( ~ spl7_199
    | spl7_110 ),
    inference(avatar_split_clause,[],[f2981,f1433,f2994])).

fof(f2981,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | spl7_110 ),
    inference(unit_resulting_resolution,[],[f1435,f1435,f102])).

fof(f2992,plain,
    ( ~ spl7_198
    | ~ spl7_14
    | ~ spl7_41
    | spl7_110
    | spl7_153 ),
    inference(avatar_split_clause,[],[f2983,f2040,f1433,f493,f197,f2989])).

fof(f2989,plain,
    ( spl7_198
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).

fof(f2983,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_110
    | spl7_153 ),
    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1435,f125])).

fof(f2971,plain,
    ( ~ spl7_195
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2946,f722,f2948])).

fof(f722,plain,
    ( spl7_55
  <=> r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f2946,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_55 ),
    inference(resolution,[],[f724,f90])).

fof(f724,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f722])).

fof(f2970,plain,
    ( ~ spl7_197
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2944,f722,f197,f2962])).

fof(f2962,plain,
    ( spl7_197
  <=> m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_197])])).

fof(f2944,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(resolution,[],[f724,f298])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f116,f199])).

fof(f2969,plain,
    ( ~ spl7_197
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2935,f722,f197,f2962])).

fof(f2935,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f724,f298])).

fof(f2968,plain,
    ( ~ spl7_197
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2936,f722,f197,f2962])).

fof(f2936,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f199,f724,f116])).

fof(f2967,plain,
    ( ~ spl7_197
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2966,f722,f197,f2962])).

fof(f2966,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f2937,f348])).

fof(f2937,plain,
    ( ! [X0] : ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f332,f724,f116])).

fof(f2965,plain,
    ( ~ spl7_197
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2960,f722,f197,f2962])).

fof(f2960,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f2938,f571])).

fof(f2938,plain,
    ( ! [X0] : ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f558,f724,f116])).

fof(f2959,plain,
    ( ~ spl7_195
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2939,f722,f2948])).

fof(f2939,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f201,f724,f116])).

fof(f2958,plain,
    ( ~ spl7_196
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2941,f722,f197,f2954])).

fof(f2954,plain,
    ( spl7_196
  <=> r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f2941,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f212,f724,f97])).

fof(f2957,plain,
    ( ~ spl7_196
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2952,f722,f197,f2954])).

fof(f2952,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(forward_demodulation,[],[f2942,f571])).

fof(f2942,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f551,f724,f97])).

fof(f2951,plain,
    ( ~ spl7_195
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f2943,f722,f2948])).

fof(f2943,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f724,f90])).

fof(f2934,plain,
    ( spl7_194
    | ~ spl7_14
    | spl7_190 ),
    inference(avatar_split_clause,[],[f2904,f2870,f197,f2928])).

fof(f2928,plain,
    ( spl7_194
  <=> r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f2870,plain,
    ( spl7_190
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f2904,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_190 ),
    inference(unit_resulting_resolution,[],[f212,f2872,f701])).

fof(f2872,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | spl7_190 ),
    inference(avatar_component_clause,[],[f2870])).

fof(f2933,plain,
    ( spl7_194
    | ~ spl7_14
    | spl7_190 ),
    inference(avatar_split_clause,[],[f2932,f2870,f197,f2928])).

fof(f2932,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_190 ),
    inference(forward_demodulation,[],[f2905,f571])).

fof(f2905,plain,
    ( ! [X0] : r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),sK6(k1_xboole_0,X0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_190 ),
    inference(unit_resulting_resolution,[],[f551,f2872,f701])).

fof(f2931,plain,
    ( spl7_194
    | ~ spl7_14
    | spl7_190 ),
    inference(avatar_split_clause,[],[f2906,f2870,f197,f2928])).

fof(f2906,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_190 ),
    inference(unit_resulting_resolution,[],[f2872,f690])).

fof(f2926,plain,
    ( spl7_193
    | spl7_190 ),
    inference(avatar_split_clause,[],[f2907,f2870,f2916])).

fof(f2916,plain,
    ( spl7_193
  <=> r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).

fof(f2907,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | spl7_190 ),
    inference(unit_resulting_resolution,[],[f216,f2872,f277])).

fof(f2919,plain,
    ( spl7_193
    | spl7_190 ),
    inference(avatar_split_clause,[],[f2914,f2870,f2916])).

fof(f2914,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | spl7_190 ),
    inference(unit_resulting_resolution,[],[f2872,f91])).

fof(f2903,plain,
    ( ~ spl7_190
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2902,f1452,f713,f2870])).

fof(f713,plain,
    ( spl7_53
  <=> r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1452,plain,
    ( spl7_113
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f2902,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2866,f1454])).

fof(f1454,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f1452])).

fof(f2866,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_53 ),
    inference(resolution,[],[f715,f90])).

fof(f715,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f713])).

fof(f2900,plain,
    ( ~ spl7_192
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2899,f1452,f713,f197,f2888])).

fof(f2888,plain,
    ( spl7_192
  <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f2899,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2864,f1454])).

fof(f2864,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(resolution,[],[f715,f298])).

fof(f2898,plain,
    ( ~ spl7_192
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2897,f1452,f713,f197,f2888])).

fof(f2897,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2855,f1454])).

fof(f2855,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f715,f298])).

fof(f2896,plain,
    ( ~ spl7_192
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2895,f1452,f713,f197,f2888])).

fof(f2895,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2856,f1454])).

fof(f2856,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f199,f715,f116])).

fof(f2894,plain,
    ( ~ spl7_192
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2893,f1452,f713,f197,f2888])).

fof(f2893,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2892,f1454])).

fof(f2892,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f2857,f348])).

fof(f2857,plain,
    ( ! [X0] : ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f332,f715,f116])).

fof(f2891,plain,
    ( ~ spl7_192
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2886,f1452,f713,f197,f2888])).

fof(f2886,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2885,f1454])).

fof(f2885,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f2858,f571])).

fof(f2858,plain,
    ( ! [X0] : ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f558,f715,f116])).

fof(f2884,plain,
    ( ~ spl7_190
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2883,f1452,f713,f2870])).

fof(f2883,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2859,f1454])).

fof(f2859,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f201,f715,f116])).

fof(f2882,plain,
    ( ~ spl7_191
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2881,f1452,f713,f197,f2877])).

fof(f2877,plain,
    ( spl7_191
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).

fof(f2881,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2861,f1454])).

fof(f2861,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f212,f715,f97])).

% (28109)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
fof(f2880,plain,
    ( ~ spl7_191
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2875,f1452,f713,f197,f2877])).

fof(f2875,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2874,f1454])).

fof(f2874,plain,
    ( ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f2862,f571])).

fof(f2862,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f551,f715,f97])).

fof(f2873,plain,
    ( ~ spl7_190
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2868,f1452,f713,f2870])).

fof(f2868,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_53
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2863,f1454])).

fof(f2863,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_53 ),
    inference(unit_resulting_resolution,[],[f715,f90])).

fof(f2854,plain,
    ( spl7_189
    | spl7_52
    | ~ spl7_175 ),
    inference(avatar_split_clause,[],[f2853,f2542,f709,f2849])).

fof(f2849,plain,
    ( spl7_189
  <=> r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f709,plain,
    ( spl7_52
  <=> v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f2542,plain,
    ( spl7_175
  <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_175])])).

fof(f2853,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0))
    | spl7_52
    | ~ spl7_175 ),
    inference(subsumption_resolution,[],[f2846,f710])).

fof(f710,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | spl7_52 ),
    inference(avatar_component_clause,[],[f709])).

fof(f2846,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl7_175 ),
    inference(resolution,[],[f2544,f277])).

fof(f2544,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_175 ),
    inference(avatar_component_clause,[],[f2542])).

fof(f2852,plain,
    ( spl7_189
    | spl7_52
    | ~ spl7_175 ),
    inference(avatar_split_clause,[],[f2844,f2542,f709,f2849])).

fof(f2844,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0))
    | spl7_52
    | ~ spl7_175 ),
    inference(unit_resulting_resolution,[],[f710,f2544,f277])).

fof(f2802,plain,
    ( spl7_187
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2801,f887,f640,f2785])).

fof(f2785,plain,
    ( spl7_187
  <=> r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).

fof(f640,plain,
    ( spl7_51
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f2801,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2782,f889])).

fof(f2782,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_51 ),
    inference(resolution,[],[f1204,f642])).

fof(f642,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f640])).

fof(f1204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | r1_tarski(u1_pre_topc(g1_pre_topc(X1,X0)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X0)))) ) ),
    inference(resolution,[],[f272,f100])).

fof(f272,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_pre_topc(g1_pre_topc(X1,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X0)))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f94,f83])).

fof(f2800,plain,
    ( spl7_188
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2799,f1452,f610,f2791])).

fof(f2791,plain,
    ( spl7_188
  <=> r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).

fof(f610,plain,
    ( spl7_48
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f2799,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2781,f1454])).

fof(f2781,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl7_48 ),
    inference(resolution,[],[f1204,f612])).

fof(f612,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f610])).

fof(f2794,plain,
    ( spl7_188
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2789,f1452,f610,f2791])).

fof(f2789,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2772,f1454])).

fof(f2772,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f612,f1204])).

fof(f2788,plain,
    ( spl7_187
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2783,f887,f640,f2785])).

fof(f2783,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2773,f889])).

fof(f2773,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f642,f1204])).

fof(f2766,plain,
    ( ~ spl7_168
    | spl7_167
    | ~ spl7_50
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2765,f887,f635,f2325,f2329])).

fof(f2325,plain,
    ( spl7_167
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f635,plain,
    ( spl7_50
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f2765,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_50
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2690,f889])).

fof(f2690,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_50
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2688,f889])).

fof(f2688,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_50 ),
    inference(resolution,[],[f637,f84])).

fof(f637,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f635])).

fof(f2764,plain,
    ( spl7_168
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2753,f887,f640,f2329])).

fof(f2753,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2742,f889])).

fof(f2742,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f642,f94])).

fof(f2763,plain,
    ( spl7_185
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2762,f887,f640,f2749])).

fof(f2762,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2745,f889])).

fof(f2745,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_51 ),
    inference(resolution,[],[f642,f100])).

fof(f2761,plain,
    ( spl7_186
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2756,f887,f640,f2758])).

fof(f2758,plain,
    ( spl7_186
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f2756,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2741,f889])).

fof(f2741,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f642,f272])).

fof(f2755,plain,
    ( ~ spl7_51
    | ~ spl7_71
    | spl7_168 ),
    inference(avatar_contradiction_clause,[],[f2754])).

fof(f2754,plain,
    ( $false
    | ~ spl7_51
    | ~ spl7_71
    | spl7_168 ),
    inference(subsumption_resolution,[],[f2753,f2331])).

fof(f2331,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl7_168 ),
    inference(avatar_component_clause,[],[f2329])).

fof(f2752,plain,
    ( spl7_185
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2747,f887,f640,f2749])).

fof(f2747,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_51
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2744,f889])).

fof(f2744,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f642,f100])).

fof(f2740,plain,
    ( spl7_184
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2720,f1452,f610,f2737])).

fof(f2737,plain,
    ( spl7_184
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f2720,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(superposition,[],[f612,f1454])).

fof(f2735,plain,
    ( spl7_182
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2734,f1452,f610,f2723])).

fof(f2723,plain,
    ( spl7_182
  <=> r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f2734,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2719,f1454])).

fof(f2719,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_48 ),
    inference(resolution,[],[f612,f100])).

fof(f2733,plain,
    ( spl7_183
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2728,f1452,f610,f2730])).

fof(f2730,plain,
    ( spl7_183
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f2728,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2715,f1454])).

fof(f2715,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f612,f272])).

fof(f2726,plain,
    ( spl7_182
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2721,f1452,f610,f2723])).

fof(f2721,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_48
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2718,f1454])).

fof(f2718,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f612,f100])).

fof(f2711,plain,
    ( spl7_180
    | ~ spl7_104
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2710,f1452,f1390,f2699])).

fof(f2699,plain,
    ( spl7_180
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f1390,plain,
    ( spl7_104
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f2710,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_104
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1391,f1454])).

fof(f1391,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f2709,plain,
    ( ~ spl7_180
    | spl7_181
    | ~ spl7_47
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2704,f1452,f605,f2706,f2699])).

fof(f2706,plain,
    ( spl7_181
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_181])])).

fof(f605,plain,
    ( spl7_47
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f2704,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_47
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2703,f1454])).

fof(f2703,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl7_47
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2612,f1454])).

fof(f2612,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl7_47 ),
    inference(resolution,[],[f607,f84])).

fof(f607,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f605])).

fof(f2702,plain,
    ( ~ spl7_180
    | spl7_104
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2693,f1452,f1390,f2699])).

fof(f2693,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | spl7_104
    | ~ spl7_113 ),
    inference(superposition,[],[f1392,f1454])).

fof(f1392,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl7_104 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f2697,plain,
    ( ~ spl7_48
    | spl7_104 ),
    inference(avatar_contradiction_clause,[],[f2696])).

fof(f2696,plain,
    ( $false
    | ~ spl7_48
    | spl7_104 ),
    inference(subsumption_resolution,[],[f2692,f612])).

fof(f2692,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | spl7_104 ),
    inference(resolution,[],[f1392,f94])).

fof(f2695,plain,
    ( ~ spl7_48
    | spl7_104 ),
    inference(avatar_contradiction_clause,[],[f2694])).

fof(f2694,plain,
    ( $false
    | ~ spl7_48
    | spl7_104 ),
    inference(subsumption_resolution,[],[f2691,f612])).

fof(f2691,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | spl7_104 ),
    inference(unit_resulting_resolution,[],[f1392,f94])).

fof(f2686,plain,
    ( ~ spl7_58
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2685])).

fof(f2685,plain,
    ( $false
    | ~ spl7_58
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2635,f123])).

fof(f2635,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_58
    | spl7_95 ),
    inference(superposition,[],[f1194,f748])).

fof(f1194,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK2)
    | spl7_95 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f1192,plain,
    ( spl7_95
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f2684,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2683])).

fof(f2683,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2682,f199])).

fof(f2682,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2681,f122])).

fof(f2681,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2619,f748])).

fof(f2619,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK2))
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f1194,f82])).

fof(f2680,plain,
    ( ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2679])).

fof(f2679,plain,
    ( $false
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2678,f123])).

fof(f2678,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(forward_demodulation,[],[f2677,f122])).

fof(f2677,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_struct_0(sK1))
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(forward_demodulation,[],[f2620,f748])).

fof(f2620,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_struct_0(sK1))
    | spl7_69
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f876,f1194,f102])).

fof(f2676,plain,
    ( ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2675])).

fof(f2675,plain,
    ( $false
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2674,f123])).

fof(f2674,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_pre_topc(sK0))
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(forward_demodulation,[],[f2673,f122])).

fof(f2673,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_pre_topc(sK0))
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(forward_demodulation,[],[f2621,f748])).

fof(f2621,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_pre_topc(sK0))
    | spl7_65
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f825,f1194,f102])).

fof(f2672,plain,
    ( ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2671])).

fof(f2671,plain,
    ( $false
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2670,f123])).

fof(f2670,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_pre_topc(sK1))
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(forward_demodulation,[],[f2669,f122])).

fof(f2669,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_pre_topc(sK1))
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(forward_demodulation,[],[f2622,f748])).

fof(f2622,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_pre_topc(sK1))
    | spl7_86
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f1071,f1194,f102])).

fof(f2668,plain,
    ( ~ spl7_58
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2667])).

fof(f2667,plain,
    ( $false
    | ~ spl7_58
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2666,f123])).

fof(f2666,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2665,f122])).

fof(f2665,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2623,f748])).

fof(f2623,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(sK2,sK2))
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f1194,f1194,f102])).

fof(f2664,plain,
    ( ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2663])).

fof(f2663,plain,
    ( $false
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2662,f122])).

fof(f2662,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(forward_demodulation,[],[f2661,f122])).

fof(f2661,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_69
    | spl7_95 ),
    inference(forward_demodulation,[],[f2625,f748])).

fof(f2625,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(sK2,sK2))
    | spl7_69
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f876,f1194,f102])).

fof(f2660,plain,
    ( ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2659])).

fof(f2659,plain,
    ( $false
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2658,f122])).

fof(f2658,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k1_xboole_0)
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(forward_demodulation,[],[f2657,f122])).

fof(f2657,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_65
    | spl7_95 ),
    inference(forward_demodulation,[],[f2626,f748])).

fof(f2626,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(sK2,sK2))
    | spl7_65
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f825,f1194,f102])).

fof(f2656,plain,
    ( ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2655])).

fof(f2655,plain,
    ( $false
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2654,f122])).

fof(f2654,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k1_xboole_0)
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(forward_demodulation,[],[f2653,f122])).

fof(f2653,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_86
    | spl7_95 ),
    inference(forward_demodulation,[],[f2627,f748])).

fof(f2627,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(sK2,sK2))
    | spl7_86
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f1071,f1194,f102])).

fof(f2652,plain,
    ( ~ spl7_58
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f2651])).

fof(f2651,plain,
    ( $false
    | ~ spl7_58
    | spl7_95 ),
    inference(subsumption_resolution,[],[f2650,f123])).

fof(f2650,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2649,f122])).

fof(f2649,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_58
    | spl7_95 ),
    inference(forward_demodulation,[],[f2628,f748])).

fof(f2628,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(sK2,sK2))
    | spl7_95 ),
    inference(unit_resulting_resolution,[],[f1194,f1194,f102])).

fof(f2648,plain,
    ( ~ spl7_14
    | ~ spl7_41
    | ~ spl7_58
    | spl7_95
    | spl7_153 ),
    inference(avatar_contradiction_clause,[],[f2647])).

fof(f2647,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_58
    | spl7_95
    | spl7_153 ),
    inference(subsumption_resolution,[],[f2646,f486])).

fof(f2646,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_58
    | spl7_95
    | spl7_153 ),
    inference(forward_demodulation,[],[f2645,f122])).

fof(f2645,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_58
    | spl7_95
    | spl7_153 ),
    inference(forward_demodulation,[],[f2630,f748])).

fof(f2630,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(sK2,sK2))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_95
    | spl7_153 ),
    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1194,f125])).

fof(f2618,plain,
    ( spl7_179
    | ~ spl7_47
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2613,f1452,f605,f2615])).

fof(f2615,plain,
    ( spl7_179
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_179])])).

fof(f2613,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_47
    | ~ spl7_113 ),
    inference(superposition,[],[f607,f1454])).

fof(f2607,plain,
    ( spl7_178
    | ~ spl7_44
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2602,f887,f525,f2604])).

fof(f2604,plain,
    ( spl7_178
  <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f525,plain,
    ( spl7_44
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f2602,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_44
    | ~ spl7_71 ),
    inference(superposition,[],[f527,f889])).

fof(f527,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f525])).

fof(f2593,plain,
    ( ~ spl7_174
    | spl7_177
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2589,f1452,f192,f187,f2591,f2536])).

fof(f2536,plain,
    ( spl7_174
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f2591,plain,
    ( spl7_177
  <=> ! [X13,X12] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).

fof(f2589,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2588,f122])).

fof(f2588,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2587,f194])).

fof(f2587,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_12
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2499,f189])).

fof(f2499,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_113 ),
    inference(superposition,[],[f481,f1454])).

fof(f481,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f480,f85])).

fof(f480,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f479,f85])).

fof(f479,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f478])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f130,f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2575,plain,
    ( spl7_176
    | ~ spl7_174
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2570,f1452,f192,f187,f2536,f2572])).

fof(f2572,plain,
    ( spl7_176
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f2570,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2569,f189])).

fof(f2569,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2496,f194])).

fof(f2496,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))
    | ~ spl7_113 ),
    inference(superposition,[],[f319,f1454])).

fof(f2551,plain,
    ( spl7_173
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2550,f1452,f192,f187,f2523])).

fof(f2523,plain,
    ( spl7_173
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f2550,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2549,f194])).

fof(f2549,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_12
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2490,f189])).

fof(f2490,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_113 ),
    inference(superposition,[],[f85,f1454])).

fof(f2548,plain,
    ( ~ spl7_14
    | ~ spl7_113
    | spl7_142 ),
    inference(avatar_contradiction_clause,[],[f2547])).

fof(f2547,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_113
    | spl7_142 ),
    inference(subsumption_resolution,[],[f2489,f651])).

fof(f651,plain,
    ( ! [X7] : v1_funct_2(k1_xboole_0,k1_xboole_0,X7)
    | ~ spl7_14 ),
    inference(superposition,[],[f110,f571])).

fof(f2489,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl7_113
    | spl7_142 ),
    inference(superposition,[],[f1822,f1454])).

fof(f1822,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl7_142 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f1820,plain,
    ( spl7_142
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f2545,plain,
    ( spl7_175
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2487,f1452,f587,f2542])).

fof(f587,plain,
    ( spl7_46
  <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f2487,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_46
    | ~ spl7_113 ),
    inference(superposition,[],[f589,f1454])).

fof(f589,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f587])).

fof(f2539,plain,
    ( spl7_174
    | ~ spl7_37
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2485,f1452,f460,f2536])).

fof(f460,plain,
    ( spl7_37
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f2485,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_37
    | ~ spl7_113 ),
    inference(superposition,[],[f461,f1454])).

fof(f461,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f460])).

fof(f2526,plain,
    ( spl7_173
    | ~ spl7_25
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2480,f1452,f321,f2523])).

fof(f321,plain,
    ( spl7_25
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f2480,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_25
    | ~ spl7_113 ),
    inference(superposition,[],[f323,f1454])).

fof(f323,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f321])).

fof(f2521,plain,
    ( spl7_172
    | ~ spl7_23
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2479,f1452,f304,f2518])).

fof(f2518,plain,
    ( spl7_172
  <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f304,plain,
    ( spl7_23
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f2479,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_23
    | ~ spl7_113 ),
    inference(superposition,[],[f306,f1454])).

fof(f306,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f304])).

fof(f2515,plain,
    ( spl7_171
    | ~ spl7_19
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2477,f1452,f257,f2512])).

fof(f2512,plain,
    ( spl7_171
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f257,plain,
    ( spl7_19
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f2477,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_19
    | ~ spl7_113 ),
    inference(superposition,[],[f259,f1454])).

fof(f259,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f257])).

fof(f2470,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2469])).

fof(f2469,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2412,f212])).

fof(f2412,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(superposition,[],[f1086,f748])).

fof(f1086,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2)
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1084,plain,
    ( spl7_88
  <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f2468,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2467])).

fof(f2467,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2466,f212])).

fof(f2466,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2411,f748])).

fof(f2411,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),sK2)
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(superposition,[],[f1086,f889])).

fof(f2465,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2464])).

fof(f2464,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2463,f199])).

fof(f2463,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2410,f748])).

fof(f2410,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_88 ),
    inference(resolution,[],[f1086,f90])).

fof(f2457,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2456])).

fof(f2456,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2455,f230])).

fof(f2455,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2408,f748])).

fof(f2408,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(resolution,[],[f1086,f298])).

fof(f2454,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2453])).

fof(f2453,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2452,f230])).

fof(f2452,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2392,f748])).

fof(f2392,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f1086,f298])).

fof(f2451,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2450])).

fof(f2450,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2449,f230])).

fof(f2449,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2393,f748])).

fof(f2393,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f199,f1086,f116])).

fof(f2448,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2447])).

fof(f2447,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2446,f230])).

fof(f2446,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2445,f748])).

fof(f2445,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2394,f348])).

fof(f2394,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(sK6(X0,k1_xboole_0)))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f332,f1086,f116])).

fof(f2444,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2443])).

fof(f2443,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2442,f230])).

fof(f2442,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2441,f748])).

fof(f2441,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2395,f571])).

fof(f2395,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(sK6(k1_xboole_0,X0)))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f558,f1086,f116])).

fof(f2440,plain,
    ( ~ spl7_170
    | ~ spl7_39
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2435,f1452,f1084,f468,f2437])).

fof(f2437,plain,
    ( spl7_170
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f468,plain,
    ( spl7_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f2435,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | ~ spl7_39
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2398,f1454])).

fof(f2398,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | ~ spl7_39
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f469,f1086,f116])).

fof(f469,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f468])).

fof(f2434,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2433])).

fof(f2433,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2432,f199])).

fof(f2432,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2399,f748])).

fof(f2399,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f201,f1086,f116])).

fof(f2431,plain,
    ( ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2430])).

fof(f2430,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2401,f212])).

fof(f2401,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0)
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f801,f1086,f97])).

fof(f801,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f800])).

fof(f800,plain,
    ( spl7_64
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f2429,plain,
    ( ~ spl7_14
    | ~ spl7_16
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f2428])).

fof(f2428,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2427,f212])).

fof(f2427,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0)
    | ~ spl7_16
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2426,f123])).

fof(f2426,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_16
    | ~ spl7_88
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2402,f1454])).

fof(f2402,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_16
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f223,f1086,f97])).

fof(f223,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl7_16
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f2425,plain,
    ( ~ spl7_14
    | ~ spl7_29
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2424])).

fof(f2424,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_29
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2423,f212])).

fof(f2423,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k1_xboole_0)
    | ~ spl7_29
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2422,f122])).

fof(f2422,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))
    | ~ spl7_29
    | ~ spl7_71
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2403,f889])).

fof(f2403,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_29
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f387,f1086,f97])).

fof(f387,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl7_29
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f2421,plain,
    ( ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2420])).

fof(f2420,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2404,f801])).

fof(f2404,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f212,f1086,f97])).

fof(f2419,plain,
    ( ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2418])).

fof(f2418,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2417,f801])).

fof(f2417,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2406,f571])).

fof(f2406,plain,
    ( ! [X0] : ~ r1_tarski(sK2,sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f551,f1086,f97])).

fof(f2416,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2415])).

fof(f2415,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f2414,f199])).

fof(f2414,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f2407,f748])).

fof(f2407,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f1086,f90])).

fof(f2413,plain,
    ( ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f2405])).

fof(f2405,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_64
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f801,f212,f1086,f97])).

fof(f2350,plain,
    ( ~ spl7_168
    | spl7_169
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2346,f887,f425,f326,f2348,f2329])).

fof(f2348,plain,
    ( spl7_169
  <=> ! [X16,X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f326,plain,
    ( spl7_26
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f425,plain,
    ( spl7_33
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f2346,plain,
    ( ! [X15,X16] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16) )
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2345,f122])).

fof(f2345,plain,
    ( ! [X15,X16] :
        ( ~ v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16) )
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2344,f328])).

fof(f328,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f326])).

fof(f2344,plain,
    ( ! [X15,X16] :
        ( ~ v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16) )
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2269,f426])).

fof(f426,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f425])).

fof(f2269,plain,
    ( ! [X15,X16] :
        ( ~ v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ v1_funct_1(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)))
        | ~ v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))
        | ~ v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ l1_pre_topc(X16)
        | ~ v2_pre_topc(X16) )
    | ~ spl7_71 ),
    inference(superposition,[],[f481,f889])).

fof(f2332,plain,
    ( spl7_167
    | ~ spl7_168
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2323,f887,f425,f326,f2329,f2325])).

fof(f2323,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2322,f426])).

fof(f2322,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_26
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2266,f328])).

fof(f2266,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))
    | ~ spl7_71 ),
    inference(superposition,[],[f319,f889])).

fof(f2304,plain,
    ( spl7_166
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2299,f887,f425,f326,f2301])).

fof(f2299,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2298,f328])).

fof(f2298,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_33
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2260,f426])).

fof(f2260,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_71 ),
    inference(superposition,[],[f85,f889])).

fof(f2297,plain,
    ( spl7_165
    | ~ spl7_20
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2292,f887,f262,f2294])).

fof(f2294,plain,
    ( spl7_165
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).

fof(f262,plain,
    ( spl7_20
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f2292,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_20
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2259,f264])).

fof(f264,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f2259,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_71 ),
    inference(superposition,[],[f272,f889])).

fof(f2249,plain,
    ( ~ spl7_164
    | ~ spl7_14
    | ~ spl7_41
    | spl7_86
    | spl7_153 ),
    inference(avatar_split_clause,[],[f2207,f2040,f1070,f493,f197,f2246])).

fof(f2246,plain,
    ( spl7_164
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f2207,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_86
    | spl7_153 ),
    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1071,f125])).

fof(f2244,plain,
    ( ~ spl7_163
    | spl7_69
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2210,f1070,f875,f2241])).

fof(f2241,plain,
    ( spl7_163
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).

fof(f2210,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK1))
    | spl7_69
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f876,f1071,f102])).

fof(f2239,plain,
    ( ~ spl7_162
    | spl7_65
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2211,f1070,f824,f2236])).

fof(f2236,plain,
    ( spl7_162
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f2211,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | spl7_65
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f825,f1071,f102])).

fof(f2234,plain,
    ( ~ spl7_159
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2212,f1070,f2220])).

fof(f2220,plain,
    ( spl7_159
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).

fof(f2212,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f1071,f1071,f102])).

fof(f2233,plain,
    ( ~ spl7_161
    | spl7_69
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2214,f1070,f875,f2230])).

fof(f2230,plain,
    ( spl7_161
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).

fof(f2214,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(sK1))
    | spl7_69
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f876,f1071,f102])).

fof(f2228,plain,
    ( ~ spl7_160
    | spl7_65
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2215,f1070,f824,f2225])).

fof(f2225,plain,
    ( spl7_160
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f2215,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | spl7_65
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f825,f1071,f102])).

fof(f2223,plain,
    ( ~ spl7_159
    | spl7_86 ),
    inference(avatar_split_clause,[],[f2216,f1070,f2220])).

fof(f2216,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1))
    | spl7_86 ),
    inference(unit_resulting_resolution,[],[f1071,f1071,f102])).

fof(f2205,plain,
    ( ~ spl7_158
    | ~ spl7_14
    | ~ spl7_41
    | spl7_65
    | spl7_153 ),
    inference(avatar_split_clause,[],[f2199,f2040,f824,f493,f197,f2202])).

fof(f2202,plain,
    ( spl7_158
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f2199,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_65
    | spl7_153 ),
    inference(unit_resulting_resolution,[],[f495,f825,f230,f2042,f125])).

fof(f2174,plain,
    ( ~ spl7_157
    | spl7_65
    | spl7_69 ),
    inference(avatar_split_clause,[],[f2152,f875,f824,f2171])).

fof(f2171,plain,
    ( spl7_157
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).

fof(f2152,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl7_65
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f876,f825,f102])).

fof(f2169,plain,
    ( ~ spl7_155
    | spl7_65 ),
    inference(avatar_split_clause,[],[f2153,f824,f2160])).

fof(f2160,plain,
    ( spl7_155
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_155])])).

fof(f2153,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | spl7_65 ),
    inference(unit_resulting_resolution,[],[f825,f825,f102])).

fof(f2168,plain,
    ( ~ spl7_156
    | spl7_65
    | spl7_69 ),
    inference(avatar_split_clause,[],[f2155,f875,f824,f2165])).

fof(f2165,plain,
    ( spl7_156
  <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f2155,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(sK1))
    | spl7_65
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f876,f825,f102])).

fof(f2163,plain,
    ( ~ spl7_155
    | spl7_65 ),
    inference(avatar_split_clause,[],[f2156,f824,f2160])).

fof(f2156,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0))
    | spl7_65 ),
    inference(unit_resulting_resolution,[],[f825,f825,f102])).

fof(f2114,plain,
    ( ~ spl7_154
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2113,f1452,f746,f142,f136,f2100])).

fof(f2100,plain,
    ( spl7_154
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f136,plain,
    ( spl7_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f142,plain,
    ( spl7_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f2113,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2112,f748])).

fof(f2112,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2111,f144])).

fof(f144,plain,
    ( sK2 = sK3
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f2111,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f138,f1454])).

fof(f138,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f2110,plain,
    ( ~ spl7_154
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2109,f1452,f746,f142,f136,f2100])).

fof(f2109,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2108,f748])).

fof(f2108,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f203,f1454])).

fof(f203,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f138,f144])).

fof(f2107,plain,
    ( ~ spl7_154
    | spl7_15
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2106,f1452,f746,f205,f2100])).

fof(f205,plain,
    ( spl7_15
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f2106,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_15
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2105,f748])).

fof(f2105,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_15
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f207,f1454])).

fof(f207,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f2103,plain,
    ( ~ spl7_154
    | spl7_82
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2098,f1452,f966,f2100])).

fof(f966,plain,
    ( spl7_82
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f2098,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_82
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f967,f1454])).

fof(f967,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_82 ),
    inference(avatar_component_clause,[],[f966])).

fof(f2084,plain,
    ( ~ spl7_14
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_114
    | spl7_128 ),
    inference(avatar_contradiction_clause,[],[f2083])).

fof(f2083,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_114
    | spl7_128 ),
    inference(subsumption_resolution,[],[f2082,f651])).

fof(f2082,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_58
    | ~ spl7_71
    | ~ spl7_114
    | spl7_128 ),
    inference(forward_demodulation,[],[f2081,f748])).

fof(f2081,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_71
    | ~ spl7_114
    | spl7_128 ),
    inference(forward_demodulation,[],[f2080,f1466])).

fof(f2080,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl7_71
    | spl7_128 ),
    inference(forward_demodulation,[],[f1638,f889])).

fof(f1638,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_128 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f1636,plain,
    ( spl7_128
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f2078,plain,
    ( ~ spl7_14
    | spl7_35
    | ~ spl7_58
    | ~ spl7_71 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | ~ spl7_14
    | spl7_35
    | ~ spl7_58
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2076,f230])).

fof(f2076,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl7_35
    | ~ spl7_58
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2075,f748])).

fof(f2075,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl7_35
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2074,f122])).

fof(f2074,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl7_35
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f435,f889])).

fof(f435,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl7_35 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl7_35
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f2073,plain,
    ( spl7_35
    | ~ spl7_64
    | ~ spl7_71 ),
    inference(avatar_contradiction_clause,[],[f2072])).

fof(f2072,plain,
    ( $false
    | spl7_35
    | ~ spl7_64
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f2071,f801])).

fof(f2071,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl7_35
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f2070,f122])).

fof(f2070,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
    | spl7_35
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f1076,f889])).

fof(f1076,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl7_35 ),
    inference(unit_resulting_resolution,[],[f435,f101])).

fof(f2069,plain,
    ( ~ spl7_152
    | spl7_38
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2068,f1452,f746,f464,f2027])).

fof(f2027,plain,
    ( spl7_152
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f464,plain,
    ( spl7_38
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f2068,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | spl7_38
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2067,f748])).

fof(f2067,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | spl7_38
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f466,f1454])).

fof(f466,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl7_38 ),
    inference(avatar_component_clause,[],[f464])).

fof(f2066,plain,
    ( ~ spl7_150
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2065,f1452,f746,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f2011])).

fof(f2011,plain,
    ( spl7_150
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f172,plain,
    ( spl7_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f373,plain,
    ( spl7_28
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f405,plain,
    ( spl7_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f2065,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2064,f748])).

fof(f2064,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1050,f1454])).

fof(f1050,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1049,f323])).

fof(f1049,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1048,f461])).

fof(f1048,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1047,f184])).

fof(f1047,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1046,f179])).

fof(f1046,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1045,f469])).

fof(f1045,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1044,f174])).

fof(f174,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1044,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1043,f375])).

fof(f375,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f373])).

fof(f1043,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15
    | ~ spl7_32
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1042,f407])).

fof(f407,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f405])).

fof(f1042,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1032,f466])).

fof(f1032,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15 ),
    inference(resolution,[],[f206,f130])).

fof(f206,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f2063,plain,
    ( ~ spl7_152
    | spl7_38
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2062,f1452,f746,f464,f2027])).

fof(f2062,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | spl7_38
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1289,f1454])).

fof(f1289,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl7_38
    | ~ spl7_58 ),
    inference(superposition,[],[f466,f748])).

fof(f2061,plain,
    ( ~ spl7_150
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2060,f1452,f746,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f2011])).

fof(f2060,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2059,f748])).

fof(f2059,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2058,f1454])).

fof(f2058,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1049,f323])).

fof(f2057,plain,
    ( ~ spl7_150
    | spl7_40
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2056,f1452,f746,f472,f2011])).

fof(f472,plain,
    ( spl7_40
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f2056,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_40
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2055,f748])).

fof(f2055,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_40
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f474,f1454])).

fof(f474,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_40 ),
    inference(avatar_component_clause,[],[f472])).

fof(f2054,plain,
    ( ~ spl7_150
    | spl7_40
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2053,f1452,f746,f472,f2011])).

fof(f2053,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_40
    | ~ spl7_58
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1300,f1454])).

fof(f1300,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_40
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f474,f748])).

fof(f2052,plain,
    ( ~ spl7_62
    | spl7_69 ),
    inference(avatar_split_clause,[],[f1431,f875,f781])).

fof(f781,plain,
    ( spl7_62
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1431,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f876,f82])).

fof(f2043,plain,
    ( ~ spl7_153
    | ~ spl7_58
    | spl7_77
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2038,f1452,f917,f746,f2040])).

fof(f917,plain,
    ( spl7_77
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f2038,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | ~ spl7_58
    | spl7_77
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2037,f748])).

fof(f2037,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))
    | spl7_77
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f918,f1454])).

fof(f918,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl7_77 ),
    inference(avatar_component_clause,[],[f917])).

fof(f2036,plain,
    ( ~ spl7_150
    | spl7_84
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2035,f1452,f981,f2011])).

fof(f981,plain,
    ( spl7_84
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f2035,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_84
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f983,f1454])).

fof(f983,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_84 ),
    inference(avatar_component_clause,[],[f981])).

fof(f2034,plain,
    ( ~ spl7_64
    | spl7_87
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f2033])).

fof(f2033,plain,
    ( $false
    | ~ spl7_64
    | spl7_87
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f2032,f801])).

fof(f2032,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl7_87
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f2031,f123])).

fof(f2031,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl7_87
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1081,f1454])).

fof(f1081,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl7_87 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f1079,plain,
    ( spl7_87
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f2030,plain,
    ( ~ spl7_152
    | spl7_101
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f2025,f1452,f1267,f2027])).

fof(f1267,plain,
    ( spl7_101
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f2025,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | spl7_101
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1268,f1454])).

fof(f1268,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl7_101 ),
    inference(avatar_component_clause,[],[f1267])).

fof(f2024,plain,
    ( spl7_113
    | ~ spl7_114
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f2023,f1553,f1464,f1452])).

fof(f1553,plain,
    ( spl7_122
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f2023,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_114
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1555,f1466])).

fof(f1555,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f1553])).

fof(f2020,plain,
    ( ~ spl7_151
    | ~ spl7_114
    | spl7_127 ),
    inference(avatar_split_clause,[],[f2015,f1618,f1464,f2017])).

fof(f1618,plain,
    ( spl7_127
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f2015,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl7_114
    | spl7_127 ),
    inference(forward_demodulation,[],[f1619,f1466])).

fof(f1619,plain,
    ( k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl7_127 ),
    inference(avatar_component_clause,[],[f1618])).

fof(f2014,plain,
    ( ~ spl7_150
    | ~ spl7_58
    | ~ spl7_114
    | spl7_131 ),
    inference(avatar_split_clause,[],[f2009,f1659,f1464,f746,f2011])).

fof(f1659,plain,
    ( spl7_131
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_131])])).

fof(f2009,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_58
    | ~ spl7_114
    | spl7_131 ),
    inference(forward_demodulation,[],[f2008,f748])).

fof(f2008,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_114
    | spl7_131 ),
    inference(forward_demodulation,[],[f1661,f1466])).

fof(f1661,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl7_131 ),
    inference(avatar_component_clause,[],[f1659])).

fof(f2007,plain,
    ( ~ spl7_141
    | ~ spl7_114
    | spl7_140 ),
    inference(avatar_split_clause,[],[f2006,f1766,f1464,f1797])).

fof(f1797,plain,
    ( spl7_141
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f1766,plain,
    ( spl7_140
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f2006,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_114
    | spl7_140 ),
    inference(forward_demodulation,[],[f1767,f1466])).

fof(f1767,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2)
    | spl7_140 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f2005,plain,
    ( spl7_69
    | spl7_70
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).

fof(f879,plain,
    ( spl7_70
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f157,plain,
    ( spl7_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f162,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f167,plain,
    ( spl7_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f873,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f872,f748])).

fof(f872,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f870,f164])).

fof(f164,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f870,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(resolution,[],[f414,f169])).

fof(f169,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X1,X0)
        | v1_partfun1(sK2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f413,f144])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | v1_partfun1(sK3,X1) )
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f412,f144])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_partfun1(sK3,X1) )
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f409,f144])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_partfun1(sK3,X1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f125,f159])).

fof(f159,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f2003,plain,
    ( spl7_82
    | ~ spl7_15
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1275,f746,f205,f966])).

fof(f1275,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_15
    | ~ spl7_58 ),
    inference(superposition,[],[f206,f748])).

fof(f2002,plain,
    ( spl7_82
    | ~ spl7_15
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f2001,f746,f205,f966])).

fof(f2001,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_15
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f206,f748])).

fof(f2000,plain,
    ( spl7_82
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f964,f746,f142,f136,f966])).

fof(f964,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f963,f748])).

fof(f963,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f137,f144])).

fof(f137,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1999,plain,
    ( spl7_82
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1998,f746,f142,f136,f966])).

fof(f1998,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f963,f748])).

fof(f1997,plain,
    ( spl7_82
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1996,f746,f142,f136,f966])).

fof(f1996,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f1995,f748])).

fof(f1995,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f137,f144])).

fof(f1994,plain,
    ( ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_69
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(avatar_contradiction_clause,[],[f1993])).

fof(f1993,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_69
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1992,f486])).

fof(f1992,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_69
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(forward_demodulation,[],[f1991,f877])).

fof(f877,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f875])).

fof(f1991,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1990,f194])).

fof(f1990,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1989,f189])).

fof(f1989,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1988,f184])).

fof(f1988,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1987,f179])).

fof(f1987,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1986,f1294])).

fof(f1986,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1985,f230])).

fof(f1985,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_41
    | spl7_81
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1984,f495])).

fof(f1984,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | spl7_81
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1983,f230])).

fof(f1983,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_81
    | ~ spl7_101 ),
    inference(subsumption_resolution,[],[f1982,f961])).

fof(f961,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl7_81 ),
    inference(avatar_component_clause,[],[f959])).

fof(f1982,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_101 ),
    inference(resolution,[],[f1269,f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1269,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_101 ),
    inference(avatar_component_clause,[],[f1267])).

fof(f1981,plain,
    ( ~ spl7_146
    | spl7_149
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1977,f875,f182,f177,f1979,f1928])).

fof(f1928,plain,
    ( spl7_146
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f1979,plain,
    ( spl7_149
  <=> ! [X13,X12] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13)
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f1977,plain,
    ( ! [X12,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1976,f122])).

fof(f1976,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1975,f184])).

fof(f1975,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_10
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1891,f179])).

fof(f1891,plain,
    ( ! [X12,X13] :
        ( ~ v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)))
        | ~ v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
        | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X13)
        | ~ v2_pre_topc(X13) )
    | ~ spl7_69 ),
    inference(superposition,[],[f481,f877])).

fof(f1963,plain,
    ( spl7_148
    | ~ spl7_146
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1958,f875,f182,f177,f1928,f1960])).

fof(f1960,plain,
    ( spl7_148
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f1958,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1957,f179])).

fof(f1957,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1888,f184])).

fof(f1888,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | ~ spl7_69 ),
    inference(superposition,[],[f319,f877])).

fof(f1939,plain,
    ( spl7_145
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1938,f875,f182,f177,f1915])).

fof(f1915,plain,
    ( spl7_145
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f1938,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1937,f184])).

fof(f1937,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl7_10
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1882,f179])).

fof(f1882,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl7_69 ),
    inference(superposition,[],[f85,f877])).

fof(f1936,plain,
    ( spl7_147
    | ~ spl7_49
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1879,f875,f620,f1933])).

fof(f1933,plain,
    ( spl7_147
  <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).

fof(f620,plain,
    ( spl7_49
  <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f1879,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_49
    | ~ spl7_69 ),
    inference(superposition,[],[f622,f877])).

fof(f622,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f620])).

fof(f1931,plain,
    ( spl7_146
    | ~ spl7_33
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1878,f875,f425,f1928])).

fof(f1878,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_33
    | ~ spl7_69 ),
    inference(superposition,[],[f426,f877])).

fof(f1918,plain,
    ( spl7_145
    | ~ spl7_26
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1873,f875,f326,f1915])).

fof(f1873,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_26
    | ~ spl7_69 ),
    inference(superposition,[],[f328,f877])).

fof(f1913,plain,
    ( spl7_144
    | ~ spl7_24
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1872,f875,f309,f1910])).

fof(f1910,plain,
    ( spl7_144
  <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f309,plain,
    ( spl7_24
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1872,plain,
    ( v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_24
    | ~ spl7_69 ),
    inference(superposition,[],[f311,f877])).

fof(f311,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1907,plain,
    ( spl7_143
    | ~ spl7_20
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1870,f875,f262,f1904])).

fof(f1904,plain,
    ( spl7_143
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f1870,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_20
    | ~ spl7_69 ),
    inference(superposition,[],[f264,f877])).

fof(f1823,plain,
    ( ~ spl7_142
    | spl7_34
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1818,f875,f746,f429,f1820])).

fof(f429,plain,
    ( spl7_34
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1818,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl7_34
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1817,f748])).

fof(f1817,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl7_34
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f431,f877])).

fof(f431,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f429])).

fof(f1804,plain,
    ( spl7_80
    | ~ spl7_69
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f1803,f966,f875,f953])).

fof(f953,plain,
    ( spl7_80
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f1803,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_69
    | ~ spl7_82 ),
    inference(forward_demodulation,[],[f968,f877])).

fof(f968,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f966])).

fof(f1800,plain,
    ( spl7_141
    | ~ spl7_114
    | ~ spl7_140 ),
    inference(avatar_split_clause,[],[f1795,f1766,f1464,f1797])).

fof(f1795,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_114
    | ~ spl7_140 ),
    inference(forward_demodulation,[],[f1768,f1466])).

fof(f1768,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl7_140 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f1794,plain,
    ( spl7_81
    | ~ spl7_1
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1793,f746,f132,f959])).

fof(f132,plain,
    ( spl7_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1793,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_1
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f133,f748])).

fof(f133,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1792,plain,
    ( ~ spl7_80
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1791,f875,f746,f142,f136,f953])).

fof(f1791,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1790,f748])).

fof(f1790,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1789,f144])).

fof(f1789,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f138,f877])).

fof(f1788,plain,
    ( ~ spl7_80
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1787,f875,f746,f142,f136,f953])).

fof(f1787,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1786,f748])).

fof(f1786,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f203,f877])).

fof(f1785,plain,
    ( ~ spl7_80
    | spl7_15
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f1784,f875,f746,f205,f953])).

fof(f1784,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_15
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1783,f748])).

fof(f1783,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_15
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f207,f877])).

fof(f1782,plain,
    ( ~ spl7_14
    | spl7_35
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_contradiction_clause,[],[f1781])).

fof(f1781,plain,
    ( $false
    | ~ spl7_14
    | spl7_35
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1780,f230])).

fof(f1780,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl7_35
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1779,f748])).

fof(f1779,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl7_35
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f435,f877])).

fof(f1778,plain,
    ( ~ spl7_14
    | spl7_40
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_contradiction_clause,[],[f1777])).

fof(f1777,plain,
    ( $false
    | ~ spl7_14
    | spl7_40
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f1776,f486])).

fof(f1776,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl7_40
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f1775,f748])).

fof(f1775,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl7_40
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f474,f877])).

fof(f1772,plain,
    ( spl7_56
    | ~ spl7_7
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f1306,f781,f162,f727])).

fof(f727,plain,
    ( spl7_56
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f1306,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_7
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f164,f782,f92])).

fof(f782,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f781])).

fof(f1771,plain,
    ( spl7_63
    | ~ spl7_39
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f939,f875,f468,f788])).

fof(f788,plain,
    ( spl7_63
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f939,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_39
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f938,f122])).

fof(f938,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl7_39
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f469,f877])).

fof(f1770,plain,
    ( spl7_140
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1614,f917,f392,f243,f1766])).

fof(f243,plain,
    ( spl7_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f392,plain,
    ( spl7_30
  <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f1614,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77 ),
    inference(unit_resulting_resolution,[],[f245,f394,f919,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f919,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f917])).

fof(f394,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f392])).

fof(f245,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1769,plain,
    ( spl7_140
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77 ),
    inference(avatar_split_clause,[],[f1623,f917,f392,f243,f1766])).

fof(f1623,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f1622,f245])).

fof(f1622,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_30
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f1615,f394])).

fof(f1615,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_relat_1(sK2)
    | ~ spl7_77 ),
    inference(resolution,[],[f919,f95])).

fof(f1764,plain,
    ( ~ spl7_38
    | spl7_15
    | ~ spl7_39
    | ~ spl7_40
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1763,f460,f321,f182,f177,f157,f152,f147,f142,f472,f468,f205,f464])).

fof(f147,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f152,plain,
    ( spl7_5
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1763,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f1762,f144])).

fof(f1762,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f1761,f144])).

fof(f1761,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f455,f461])).

fof(f455,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f454,f144])).

fof(f454,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f453,f144])).

fof(f453,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f452,f323])).

fof(f452,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f451,f184])).

fof(f451,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f450,f179])).

fof(f450,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f449,f159])).

fof(f449,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f446,f149])).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f446,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f129,f154])).

fof(f154,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f1760,plain,
    ( ~ spl7_40
    | ~ spl7_39
    | spl7_15
    | ~ spl7_38
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1759,f460,f405,f373,f321,f182,f177,f172,f464,f205,f468,f472])).

fof(f1759,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1758,f323])).

fof(f1758,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1757,f461])).

fof(f1757,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1756,f184])).

fof(f1756,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1755,f179])).

fof(f1755,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1754,f174])).

fof(f1754,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f807,f407])).

fof(f807,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_28 ),
    inference(resolution,[],[f375,f129])).

fof(f1753,plain,
    ( ~ spl7_128
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1752,f1553,f437,f433,f192,f187,f182,f177,f172,f167,f162,f132,f1636])).

fof(f437,plain,
    ( spl7_36
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1752,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1751,f1555])).

fof(f1751,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1750,f194])).

fof(f1750,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1749,f189])).

fof(f1749,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1748,f184])).

fof(f1748,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1747,f179])).

fof(f1747,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1746,f169])).

fof(f1746,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1745,f164])).

fof(f1745,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_9
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1744,f174])).

fof(f1744,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1743,f434])).

fof(f434,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f433])).

fof(f1743,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_1
    | ~ spl7_36 ),
    inference(subsumption_resolution,[],[f1724,f134])).

fof(f134,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1724,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_36 ),
    inference(resolution,[],[f438,f130])).

fof(f438,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f437])).

fof(f1726,plain,
    ( ~ spl7_128
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1725,f1553,f437,f433,f192,f187,f182,f177,f172,f167,f162,f132,f1636])).

fof(f1725,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1722,f1555])).

fof(f1722,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f194,f189,f184,f179,f174,f134,f169,f164,f434,f438,f130])).

fof(f1721,plain,
    ( ~ spl7_139
    | ~ spl7_14
    | ~ spl7_41
    | spl7_70
    | spl7_114
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1716,f1553,f1464,f879,f493,f197,f1718])).

fof(f1718,plain,
    ( spl7_139
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).

fof(f1716,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_70
    | spl7_114
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1673,f1555])).

fof(f1673,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_relat_1(sK2))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_70
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f880,f495,f230,f1465,f125])).

fof(f1465,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl7_114 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f880,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | spl7_70 ),
    inference(avatar_component_clause,[],[f879])).

fof(f1715,plain,
    ( ~ spl7_138
    | spl7_58
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1676,f1464,f746,f1712])).

fof(f1712,plain,
    ( spl7_138
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f1676,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_relat_1(sK2))
    | spl7_58
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f747,f1465,f102])).

fof(f747,plain,
    ( k1_xboole_0 != sK2
    | spl7_58 ),
    inference(avatar_component_clause,[],[f746])).

fof(f1710,plain,
    ( ~ spl7_137
    | spl7_69
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1677,f1464,f875,f1707])).

fof(f1707,plain,
    ( spl7_137
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f1677,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))
    | spl7_69
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f876,f1465,f102])).

fof(f1705,plain,
    ( ~ spl7_134
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1678,f1464,f1691])).

fof(f1691,plain,
    ( spl7_134
  <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f1678,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f1465,f1465,f102])).

fof(f1704,plain,
    ( ~ spl7_136
    | spl7_58
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1680,f1464,f746,f1701])).

fof(f1701,plain,
    ( spl7_136
  <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f1680,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),sK2)
    | spl7_58
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f747,f1465,f102])).

fof(f1699,plain,
    ( ~ spl7_135
    | spl7_69
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1681,f1464,f875,f1696])).

fof(f1696,plain,
    ( spl7_135
  <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1681,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))
    | spl7_69
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f876,f1465,f102])).

fof(f1694,plain,
    ( ~ spl7_134
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1682,f1464,f1691])).

fof(f1682,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f1465,f1465,f102])).

fof(f1689,plain,
    ( ~ spl7_133
    | spl7_114 ),
    inference(avatar_split_clause,[],[f1684,f1464,f1686])).

fof(f1686,plain,
    ( spl7_133
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f1684,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | spl7_114 ),
    inference(unit_resulting_resolution,[],[f1465,f82])).

fof(f1671,plain,
    ( spl7_129
    | ~ spl7_38
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1670,f1553,f464,f1651])).

fof(f1651,plain,
    ( spl7_129
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1670,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_38
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f465,f1555])).

fof(f465,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f464])).

fof(f1669,plain,
    ( spl7_132
    | ~ spl7_39
    | ~ spl7_122
    | ~ spl7_127 ),
    inference(avatar_split_clause,[],[f1664,f1618,f1553,f468,f1666])).

fof(f1666,plain,
    ( spl7_132
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f1664,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl7_39
    | ~ spl7_122
    | ~ spl7_127 ),
    inference(forward_demodulation,[],[f1663,f1620])).

fof(f1620,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_127 ),
    inference(avatar_component_clause,[],[f1618])).

fof(f1663,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl7_39
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f469,f1555])).

fof(f1662,plain,
    ( spl7_129
    | ~ spl7_130
    | ~ spl7_131
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1649,f1553,f460,f405,f373,f321,f205,f182,f177,f172,f1659,f1655,f1651])).

fof(f1655,plain,
    ( spl7_130
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f1649,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1648,f1555])).

fof(f1648,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1647,f1555])).

fof(f1647,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1646,f1555])).

fof(f1646,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1645,f323])).

fof(f1645,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1644,f461])).

fof(f1644,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1643,f184])).

fof(f1643,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1642,f179])).

fof(f1642,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1641,f174])).

fof(f1641,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1640,f375])).

fof(f1640,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1032,f407])).

fof(f1639,plain,
    ( spl7_36
    | ~ spl7_128
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1634,f1553,f433,f425,f405,f373,f326,f205,f192,f187,f172,f1636,f437])).

fof(f1634,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1633,f1555])).

fof(f1633,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1632,f194])).

fof(f1632,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1631,f189])).

fof(f1631,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1630,f328])).

fof(f1630,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1629,f426])).

fof(f1629,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1628,f434])).

fof(f1628,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1627,f174])).

fof(f1627,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1626,f375])).

fof(f1626,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1031,f407])).

fof(f1031,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15 ),
    inference(resolution,[],[f206,f128])).

fof(f1625,plain,
    ( spl7_127
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1624,f1553,f917,f392,f243,f1618])).

fof(f1624,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1623,f1555])).

fof(f1621,plain,
    ( spl7_127
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1616,f1553,f917,f392,f243,f1618])).

fof(f1616,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl7_17
    | ~ spl7_30
    | ~ spl7_77
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1614,f1555])).

fof(f1612,plain,
    ( ~ spl7_126
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1611,f1553,f731,f197,f1600])).

fof(f731,plain,
    ( spl7_57
  <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f1611,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1585,f1555])).

fof(f1585,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(resolution,[],[f733,f298])).

fof(f733,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f731])).

fof(f1610,plain,
    ( ~ spl7_126
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1609,f1553,f731,f197,f1600])).

fof(f1609,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1576,f1555])).

fof(f1576,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f733,f298])).

fof(f1608,plain,
    ( ~ spl7_126
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1607,f1553,f731,f197,f1600])).

fof(f1607,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1577,f1555])).

fof(f1577,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f199,f733,f116])).

fof(f1606,plain,
    ( ~ spl7_126
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1605,f1553,f731,f197,f1600])).

fof(f1605,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1604,f1555])).

fof(f1604,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(forward_demodulation,[],[f1578,f348])).

fof(f1578,plain,
    ( ! [X0] : ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f332,f733,f116])).

fof(f1603,plain,
    ( ~ spl7_126
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1598,f1553,f731,f197,f1600])).

fof(f1598,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1597,f1555])).

fof(f1597,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(forward_demodulation,[],[f1579,f571])).

fof(f1579,plain,
    ( ! [X0] : ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f558,f733,f116])).

fof(f1596,plain,
    ( ~ spl7_125
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1595,f1553,f731,f197,f1591])).

fof(f1595,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1581,f1555])).

fof(f1581,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f212,f733,f97])).

fof(f1594,plain,
    ( ~ spl7_125
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1589,f1553,f731,f197,f1591])).

fof(f1589,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_57
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1588,f1555])).

fof(f1588,plain,
    ( ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(forward_demodulation,[],[f1582,f571])).

fof(f1582,plain,
    ( ! [X0] : ~ r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f551,f733,f97])).

fof(f1572,plain,
    ( ~ spl7_124
    | ~ spl7_14
    | ~ spl7_41
    | spl7_58
    | spl7_70
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1567,f1553,f879,f746,f493,f197,f1569])).

fof(f1569,plain,
    ( spl7_124
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f1567,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),sK2)
    | ~ spl7_14
    | ~ spl7_41
    | spl7_58
    | spl7_70
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1558,f1555])).

fof(f1558,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),sK2)
    | ~ spl7_14
    | ~ spl7_41
    | spl7_58
    | spl7_70 ),
    inference(unit_resulting_resolution,[],[f495,f747,f230,f880,f125])).

fof(f1566,plain,
    ( ~ spl7_123
    | ~ spl7_14
    | ~ spl7_41
    | spl7_69
    | spl7_70
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1561,f1553,f879,f875,f493,f197,f1563])).

fof(f1563,plain,
    ( spl7_123
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f1561,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_69
    | spl7_70
    | ~ spl7_122 ),
    inference(forward_demodulation,[],[f1559,f1555])).

fof(f1559,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_14
    | ~ spl7_41
    | spl7_69
    | spl7_70 ),
    inference(unit_resulting_resolution,[],[f495,f876,f230,f880,f125])).

fof(f1557,plain,
    ( spl7_122
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f1469,f901,f283,f243,f1553])).

fof(f283,plain,
    ( spl7_21
  <=> v4_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f901,plain,
    ( spl7_74
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f1469,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f1468,f245])).

fof(f1468,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f1461,f285])).

fof(f285,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f283])).

fof(f1461,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl7_74 ),
    inference(resolution,[],[f903,f95])).

fof(f903,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f901])).

fof(f1556,plain,
    ( spl7_122
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f1460,f901,f283,f243,f1553])).

fof(f1460,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74 ),
    inference(unit_resulting_resolution,[],[f245,f285,f903,f95])).

fof(f1551,plain,
    ( spl7_113
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_114 ),
    inference(avatar_split_clause,[],[f1550,f1464,f901,f283,f243,f1452])).

fof(f1550,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_114 ),
    inference(forward_demodulation,[],[f1460,f1466])).

fof(f1549,plain,
    ( spl7_113
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_114 ),
    inference(avatar_split_clause,[],[f1548,f1464,f901,f283,f243,f1452])).

fof(f1548,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_114 ),
    inference(forward_demodulation,[],[f1469,f1466])).

fof(f1547,plain,
    ( ~ spl7_121
    | ~ spl7_32
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f1505,f776,f405,f1544])).

fof(f1544,plain,
    ( spl7_121
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f776,plain,
    ( spl7_61
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f1505,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_32
    | ~ spl7_61 ),
    inference(unit_resulting_resolution,[],[f407,f778,f116])).

fof(f778,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f776])).

fof(f1542,plain,
    ( ~ spl7_120
    | ~ spl7_35
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f1504,f776,f433,f1539])).

fof(f1539,plain,
    ( spl7_120
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f1504,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_35
    | ~ spl7_61 ),
    inference(unit_resulting_resolution,[],[f434,f778,f116])).

fof(f1537,plain,
    ( ~ spl7_119
    | ~ spl7_7
    | ~ spl7_61 ),
    inference(avatar_split_clause,[],[f1503,f776,f162,f1534])).

fof(f1534,plain,
    ( spl7_119
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f1503,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_7
    | ~ spl7_61 ),
    inference(unit_resulting_resolution,[],[f164,f778,f116])).

fof(f1530,plain,
    ( ~ spl7_7
    | ~ spl7_14
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1529])).

fof(f1529,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_14
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1528,f199])).

fof(f1528,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1527,f123])).

fof(f1527,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | ~ spl7_7
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1503,f1454])).

fof(f1526,plain,
    ( ~ spl7_14
    | ~ spl7_35
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(avatar_contradiction_clause,[],[f1525])).

fof(f1525,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_35
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f1524,f199])).

fof(f1524,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_35
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1523,f123])).

fof(f1523,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_35
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1504,f1454])).

fof(f1522,plain,
    ( ~ spl7_118
    | ~ spl7_32
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1517,f1452,f776,f405,f1519])).

fof(f1519,plain,
    ( spl7_118
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f1517,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_32
    | ~ spl7_61
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1505,f1454])).

fof(f1498,plain,
    ( spl7_117
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f1472,f709,f197,f1495])).

fof(f1495,plain,
    ( spl7_117
  <=> r2_hidden(sK5(u1_pre_topc(sK0),k1_xboole_0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f1472,plain,
    ( r2_hidden(sK5(u1_pre_topc(sK0),k1_xboole_0),u1_pre_topc(sK0))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f710,f690])).

fof(f1493,plain,
    ( spl7_116
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1473,f718,f197,f1490])).

fof(f1490,plain,
    ( spl7_116
  <=> r2_hidden(sK5(u1_pre_topc(sK1),k1_xboole_0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f718,plain,
    ( spl7_54
  <=> v1_xboole_0(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f1473,plain,
    ( r2_hidden(sK5(u1_pre_topc(sK1),k1_xboole_0),u1_pre_topc(sK1))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f719,f690])).

fof(f719,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK1))
    | spl7_54 ),
    inference(avatar_component_clause,[],[f718])).

fof(f1488,plain,
    ( spl7_115
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1475,f781,f197,f1485])).

fof(f1485,plain,
    ( spl7_115
  <=> r2_hidden(sK5(u1_struct_0(sK1),k1_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f1475,plain,
    ( r2_hidden(sK5(u1_struct_0(sK1),k1_xboole_0),u1_struct_0(sK1))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f783,f690])).

fof(f783,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_62 ),
    inference(avatar_component_clause,[],[f781])).

fof(f1471,plain,
    ( spl7_114
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1470,f1452,f901,f283,f243,f1464])).

fof(f1470,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1469,f1454])).

fof(f1467,plain,
    ( spl7_114
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1462,f1452,f901,f283,f243,f1464])).

fof(f1462,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_74
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1460,f1454])).

fof(f1459,plain,
    ( spl7_113
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_43
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1458,f879,f508,f248,f197,f1452])).

fof(f248,plain,
    ( spl7_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1458,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_43
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1457,f510])).

fof(f1457,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f1456,f250])).

fof(f250,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f248])).

fof(f1456,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_70 ),
    inference(subsumption_resolution,[],[f1449,f279])).

fof(f279,plain,
    ( ! [X0] : v4_relat_1(k1_xboole_0,X0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f230,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1449,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_70 ),
    inference(resolution,[],[f881,f95])).

fof(f881,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f879])).

fof(f1455,plain,
    ( spl7_113
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_43
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f1450,f879,f508,f248,f197,f1452])).

fof(f1450,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_43
    | ~ spl7_70 ),
    inference(forward_demodulation,[],[f1448,f510])).

fof(f1448,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f250,f279,f881,f95])).

fof(f1447,plain,
    ( ~ spl7_112
    | spl7_58
    | spl7_69 ),
    inference(avatar_split_clause,[],[f1425,f875,f746,f1444])).

fof(f1444,plain,
    ( spl7_112
  <=> k1_xboole_0 = k2_zfmisc_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1425,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,u1_struct_0(sK1))
    | spl7_58
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f747,f876,f102])).

fof(f1442,plain,
    ( ~ spl7_110
    | spl7_69 ),
    inference(avatar_split_clause,[],[f1426,f875,f1433])).

fof(f1426,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f876,f876,f102])).

fof(f1441,plain,
    ( ~ spl7_111
    | spl7_58
    | spl7_69 ),
    inference(avatar_split_clause,[],[f1428,f875,f746,f1438])).

fof(f1438,plain,
    ( spl7_111
  <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f1428,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),sK2)
    | spl7_58
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f747,f876,f102])).

fof(f1436,plain,
    ( ~ spl7_110
    | spl7_69 ),
    inference(avatar_split_clause,[],[f1429,f875,f1433])).

fof(f1429,plain,
    ( k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | spl7_69 ),
    inference(unit_resulting_resolution,[],[f876,f876,f102])).

fof(f1419,plain,
    ( spl7_109
    | spl7_64 ),
    inference(avatar_split_clause,[],[f1413,f800,f1415])).

fof(f1415,plain,
    ( spl7_109
  <=> r2_hidden(sK5(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f1413,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),sK2)
    | spl7_64 ),
    inference(resolution,[],[f802,f98])).

fof(f802,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl7_64 ),
    inference(avatar_component_clause,[],[f800])).

fof(f1418,plain,
    ( spl7_109
    | spl7_64 ),
    inference(avatar_split_clause,[],[f1411,f800,f1415])).

fof(f1411,plain,
    ( r2_hidden(sK5(sK2,k1_xboole_0),sK2)
    | spl7_64 ),
    inference(unit_resulting_resolution,[],[f802,f98])).

fof(f1409,plain,
    ( spl7_103
    | ~ spl7_104
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_107
    | ~ spl7_108
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f1384,f460,f425,f405,f373,f321,f205,f182,f177,f172,f1406,f1402,f1398,f1394,f1390,f1386])).

fof(f1386,plain,
    ( spl7_103
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f1394,plain,
    ( spl7_105
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f1398,plain,
    ( spl7_106
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f1402,plain,
    ( spl7_107
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f1406,plain,
    ( spl7_108
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1384,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1383,f323])).

fof(f1383,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f1382,f461])).

fof(f1382,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f1381,f426])).

fof(f1381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1380,f375])).

fof(f1380,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f1379,f407])).

fof(f1379,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1378,f184])).

fof(f1378,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1377,f179])).

fof(f1377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f1373,f174])).

fof(f1373,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_15 ),
    inference(resolution,[],[f481,f206])).

fof(f1320,plain,
    ( ~ spl7_56
    | spl7_58 ),
    inference(avatar_split_clause,[],[f1190,f746,f727])).

fof(f1190,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_58 ),
    inference(unit_resulting_resolution,[],[f747,f82])).

fof(f1319,plain,
    ( ~ spl7_62
    | spl7_69 ),
    inference(avatar_contradiction_clause,[],[f1318])).

fof(f1318,plain,
    ( $false
    | ~ spl7_62
    | spl7_69 ),
    inference(subsumption_resolution,[],[f1314,f876])).

fof(f1314,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_62 ),
    inference(resolution,[],[f782,f82])).

fof(f1316,plain,
    ( ~ spl7_62
    | spl7_69 ),
    inference(avatar_contradiction_clause,[],[f1315])).

fof(f1315,plain,
    ( $false
    | ~ spl7_62
    | spl7_69 ),
    inference(subsumption_resolution,[],[f1311,f876])).

fof(f1311,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f782,f82])).

fof(f1299,plain,
    ( ~ spl7_14
    | spl7_39
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f1298])).

fof(f1298,plain,
    ( $false
    | ~ spl7_14
    | spl7_39
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f1290,f230])).

fof(f1290,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl7_39
    | ~ spl7_58 ),
    inference(superposition,[],[f470,f748])).

fof(f470,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f468])).

fof(f1297,plain,
    ( ~ spl7_101
    | spl7_38
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1289,f746,f464,f1267])).

fof(f1296,plain,
    ( spl7_100
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1280,f746,f373,f1255])).

fof(f1255,plain,
    ( spl7_100
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f1280,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_28
    | ~ spl7_58 ),
    inference(superposition,[],[f375,f748])).

fof(f1295,plain,
    ( spl7_102
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f1273,f746,f167,f1292])).

fof(f1273,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(superposition,[],[f169,f748])).

fof(f1270,plain,
    ( ~ spl7_84
    | ~ spl7_100
    | spl7_101
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_25
    | ~ spl7_37
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(avatar_split_clause,[],[f1265,f966,f493,f460,f321,f197,f182,f177,f1267,f1255,f981])).

fof(f1265,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_25
    | ~ spl7_37
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1264,f323])).

fof(f1264,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_37
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1263,f461])).

fof(f1263,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1262,f184])).

fof(f1262,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1261,f179])).

fof(f1261,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1260,f230])).

fof(f1260,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1259,f495])).

fof(f1259,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_14
    | ~ spl7_82 ),
    inference(subsumption_resolution,[],[f1241,f230])).

fof(f1241,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_82 ),
    inference(resolution,[],[f968,f130])).

fof(f1258,plain,
    ( ~ spl7_99
    | ~ spl7_100
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(avatar_split_clause,[],[f1249,f972,f966,f493,f425,f326,f197,f192,f187,f1255,f1251])).

fof(f1251,plain,
    ( spl7_99
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f1249,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1248,f194])).

fof(f1248,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1247,f189])).

fof(f1247,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_26
    | ~ spl7_33
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1246,f328])).

fof(f1246,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_33
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1245,f426])).

fof(f1245,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1244,f230])).

fof(f1244,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_41
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1243,f495])).

fof(f1243,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_14
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1242,f230])).

fof(f1242,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_82
    | spl7_83 ),
    inference(subsumption_resolution,[],[f1240,f974])).

fof(f1240,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_82 ),
    inference(resolution,[],[f968,f128])).

fof(f1238,plain,
    ( spl7_96
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1205,f781,f1214])).

fof(f1214,plain,
    ( spl7_96
  <=> r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f1205,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f216,f783,f277])).

fof(f1237,plain,
    ( ~ spl7_98
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1206,f781,f197,f1233])).

fof(f1233,plain,
    ( spl7_98
  <=> r1_tarski(u1_struct_0(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f1206,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0)
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f212,f783,f277])).

fof(f1236,plain,
    ( ~ spl7_98
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1231,f781,f197,f1233])).

fof(f1231,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0)
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1207,f571])).

fof(f1207,plain,
    ( ! [X0] : ~ r1_tarski(u1_struct_0(sK1),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f551,f783,f277])).

fof(f1230,plain,
    ( ~ spl7_97
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1208,f781,f197,f1221])).

fof(f1221,plain,
    ( spl7_97
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1208,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f783,f335])).

fof(f1229,plain,
    ( ~ spl7_97
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1228,f781,f197,f1221])).

fof(f1228,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1209,f122])).

fof(f1209,plain,
    ( ! [X0] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f199,f783,f92])).

fof(f1227,plain,
    ( ~ spl7_97
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1226,f781,f197,f1221])).

fof(f1226,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1225,f122])).

fof(f1225,plain,
    ( ! [X0] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1210,f348])).

fof(f1210,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f332,f783,f92])).

fof(f1224,plain,
    ( ~ spl7_97
    | ~ spl7_14
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1219,f781,f197,f1221])).

fof(f1219,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1218,f122])).

fof(f1218,plain,
    ( ! [X0] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_62 ),
    inference(forward_demodulation,[],[f1211,f571])).

fof(f1211,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))
    | ~ spl7_14
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f558,f783,f92])).

fof(f1217,plain,
    ( spl7_96
    | spl7_62 ),
    inference(avatar_split_clause,[],[f1212,f781,f1214])).

fof(f1212,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl7_62 ),
    inference(unit_resulting_resolution,[],[f783,f91])).

fof(f1196,plain,
    ( ~ spl7_95
    | spl7_58 ),
    inference(avatar_split_clause,[],[f1186,f746,f1192])).

fof(f1186,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK2)
    | spl7_58 ),
    inference(unit_resulting_resolution,[],[f747,f747,f102])).

fof(f1195,plain,
    ( ~ spl7_95
    | spl7_58 ),
    inference(avatar_split_clause,[],[f1188,f746,f1192])).

fof(f1188,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK2)
    | spl7_58 ),
    inference(unit_resulting_resolution,[],[f747,f747,f102])).

fof(f1161,plain,
    ( spl7_87
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f1131,f433,f1079])).

fof(f1131,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_35 ),
    inference(resolution,[],[f434,f100])).

fof(f1160,plain,
    ( spl7_87
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f1130,f433,f1079])).

fof(f1130,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f434,f100])).

fof(f1159,plain,
    ( ~ spl7_35
    | spl7_87 ),
    inference(avatar_contradiction_clause,[],[f1158])).

fof(f1158,plain,
    ( $false
    | ~ spl7_35
    | spl7_87 ),
    inference(subsumption_resolution,[],[f1130,f1081])).

fof(f1157,plain,
    ( ~ spl7_35
    | spl7_87 ),
    inference(avatar_contradiction_clause,[],[f1156])).

fof(f1156,plain,
    ( $false
    | ~ spl7_35
    | spl7_87 ),
    inference(subsumption_resolution,[],[f1131,f1081])).

fof(f1155,plain,
    ( ~ spl7_94
    | spl7_35
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1150,f1070,f433,f1152])).

fof(f1152,plain,
    ( spl7_94
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f1150,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))))
    | spl7_35
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f435,f1072])).

fof(f1072,plain,
    ( k1_xboole_0 = u1_pre_topc(sK1)
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1149,plain,
    ( ~ spl7_92
    | spl7_35
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1148,f1070,f433,f1134])).

fof(f1134,plain,
    ( spl7_92
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f1148,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))
    | spl7_35
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f1076,f1072])).

fof(f1147,plain,
    ( ~ spl7_92
    | ~ spl7_86
    | spl7_87 ),
    inference(avatar_split_clause,[],[f1146,f1079,f1070,f1134])).

fof(f1146,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))
    | ~ spl7_86
    | spl7_87 ),
    inference(forward_demodulation,[],[f1081,f1072])).

fof(f1145,plain,
    ( spl7_93
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f1140,f1084,f1070,f1142])).

fof(f1142,plain,
    ( spl7_93
  <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f1140,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))),sK2)
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(forward_demodulation,[],[f1086,f1072])).

fof(f1139,plain,
    ( spl7_92
    | ~ spl7_35
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1138,f1070,f433,f1134])).

fof(f1138,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))
    | ~ spl7_35
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f1131,f1072])).

fof(f1137,plain,
    ( spl7_92
    | ~ spl7_35
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f1132,f1070,f433,f1134])).

fof(f1132,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))
    | ~ spl7_35
    | ~ spl7_86 ),
    inference(forward_demodulation,[],[f1130,f1072])).

fof(f1123,plain,
    ( spl7_89
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1089,f718,f1099])).

fof(f1099,plain,
    ( spl7_89
  <=> r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f1089,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1))
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f216,f719,f277])).

fof(f1122,plain,
    ( ~ spl7_91
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1091,f718,f197,f1118])).

fof(f1118,plain,
    ( spl7_91
  <=> r1_tarski(u1_pre_topc(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f1091,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),k1_xboole_0)
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f212,f719,f277])).

fof(f1121,plain,
    ( ~ spl7_91
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1116,f718,f197,f1118])).

fof(f1116,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),k1_xboole_0)
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1092,f571])).

fof(f1092,plain,
    ( ! [X0] : ~ r1_tarski(u1_pre_topc(sK1),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f551,f719,f277])).

fof(f1115,plain,
    ( ~ spl7_90
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1093,f718,f197,f1106])).

fof(f1106,plain,
    ( spl7_90
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f1093,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f719,f335])).

fof(f1114,plain,
    ( ~ spl7_90
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1113,f718,f197,f1106])).

fof(f1113,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1094,f122])).

fof(f1094,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f199,f719,f92])).

fof(f1112,plain,
    ( ~ spl7_90
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1111,f718,f197,f1106])).

fof(f1111,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1110,f122])).

fof(f1110,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1095,f348])).

fof(f1095,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f332,f719,f92])).

fof(f1109,plain,
    ( ~ spl7_90
    | ~ spl7_14
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1104,f718,f197,f1106])).

fof(f1104,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1103,f122])).

fof(f1103,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_54 ),
    inference(forward_demodulation,[],[f1096,f571])).

fof(f1096,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))
    | ~ spl7_14
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f558,f719,f92])).

fof(f1102,plain,
    ( spl7_89
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1097,f718,f1099])).

fof(f1097,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1))
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f719,f91])).

fof(f1088,plain,
    ( spl7_88
    | spl7_35 ),
    inference(avatar_split_clause,[],[f1077,f433,f1084])).

fof(f1077,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2)
    | spl7_35 ),
    inference(resolution,[],[f435,f229])).

fof(f1087,plain,
    ( spl7_88
    | spl7_35 ),
    inference(avatar_split_clause,[],[f1075,f433,f1084])).

fof(f1075,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2)
    | spl7_35 ),
    inference(unit_resulting_resolution,[],[f435,f229])).

fof(f1082,plain,
    ( ~ spl7_87
    | spl7_35 ),
    inference(avatar_split_clause,[],[f1076,f433,f1079])).

fof(f1074,plain,
    ( spl7_86
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f1068,f718,f1070])).

fof(f1068,plain,
    ( k1_xboole_0 = u1_pre_topc(sK1)
    | ~ spl7_54 ),
    inference(resolution,[],[f720,f82])).

fof(f720,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f718])).

fof(f1073,plain,
    ( spl7_86
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f1065,f718,f1070])).

fof(f1065,plain,
    ( k1_xboole_0 = u1_pre_topc(sK1)
    | ~ spl7_54 ),
    inference(unit_resulting_resolution,[],[f720,f82])).

fof(f1056,plain,
    ( ~ spl7_40
    | ~ spl7_39
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38 ),
    inference(avatar_split_clause,[],[f1055,f464,f460,f405,f373,f321,f205,f182,f177,f172,f468,f472])).

fof(f1055,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1054,f323])).

fof(f1054,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1053,f461])).

fof(f1053,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1052,f184])).

fof(f1052,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_38 ),
    inference(subsumption_resolution,[],[f1045,f179])).

fof(f1051,plain,
    ( ~ spl7_40
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_15
    | ~ spl7_25
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_37
    | spl7_38
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f1050,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f472])).

fof(f1041,plain,
    ( ~ spl7_34
    | ~ spl7_35
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | spl7_36 ),
    inference(avatar_split_clause,[],[f1040,f437,f425,f405,f373,f326,f205,f192,f187,f172,f433,f429])).

fof(f1040,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1039,f194])).

fof(f1039,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1038,f189])).

fof(f1038,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1037,f328])).

fof(f1037,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_33
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1036,f426])).

fof(f1036,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1035,f174])).

fof(f1035,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15
    | ~ spl7_28
    | ~ spl7_32
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1034,f375])).

fof(f1034,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15
    | ~ spl7_32
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1033,f407])).

fof(f1033,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_15
    | spl7_36 ),
    inference(subsumption_resolution,[],[f1031,f439])).

fof(f439,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_36 ),
    inference(avatar_component_clause,[],[f437])).

fof(f1009,plain,
    ( ~ spl7_85
    | ~ spl7_32
    | spl7_56 ),
    inference(avatar_split_clause,[],[f1003,f727,f405,f1006])).

fof(f1006,plain,
    ( spl7_85
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1003,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_32
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f407,f728,f92])).

fof(f728,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_56 ),
    inference(avatar_component_clause,[],[f727])).

fof(f992,plain,
    ( ~ spl7_14
    | ~ spl7_71
    | ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f991])).

fof(f991,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_71
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f990,f212])).

fof(f990,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ spl7_71
    | ~ spl7_76 ),
    inference(forward_demodulation,[],[f989,f122])).

fof(f989,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))
    | ~ spl7_71
    | ~ spl7_76 ),
    inference(forward_demodulation,[],[f914,f889])).

fof(f914,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f912])).

fof(f912,plain,
    ( spl7_76
  <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f988,plain,
    ( spl7_15
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f963,f142,f136,f205])).

fof(f987,plain,
    ( spl7_70
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f986,f901,f746,f879])).

fof(f986,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl7_58
    | ~ spl7_74 ),
    inference(forward_demodulation,[],[f903,f748])).

fof(f985,plain,
    ( spl7_69
    | spl7_70
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).

fof(f984,plain,
    ( ~ spl7_81
    | ~ spl7_84
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_38
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f979,f746,f464,f197,f192,f187,f182,f177,f172,f167,f162,f981,f959])).

fof(f979,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_38
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f978,f748])).

fof(f978,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_38
    | ~ spl7_58 ),
    inference(subsumption_resolution,[],[f977,f230])).

fof(f977,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_38
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f929,f748])).

fof(f929,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_38
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f928,f748])).

fof(f928,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_38 ),
    inference(subsumption_resolution,[],[f927,f194])).

fof(f927,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_38 ),
    inference(subsumption_resolution,[],[f926,f189])).

fof(f926,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38 ),
    inference(subsumption_resolution,[],[f925,f184])).

fof(f925,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_38 ),
    inference(subsumption_resolution,[],[f924,f179])).

fof(f924,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f923,f169])).

fof(f923,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_7
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f922,f164])).

fof(f922,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f675,f174])).

fof(f675,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_38 ),
    inference(resolution,[],[f466,f127])).

fof(f975,plain,
    ( ~ spl7_83
    | spl7_36
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f970,f746,f437,f972])).

fof(f970,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_36
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f439,f748])).

fof(f969,plain,
    ( spl7_82
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f964,f746,f142,f136,f966])).

fof(f962,plain,
    ( ~ spl7_81
    | spl7_1
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f957,f746,f132,f959])).

fof(f957,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl7_1
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f134,f748])).

fof(f956,plain,
    ( spl7_80
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f951,f875,f746,f142,f136,f953])).

fof(f951,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f950,f748])).

fof(f950,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f949,f144])).

fof(f949,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_2
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f137,f877])).

fof(f948,plain,
    ( ~ spl7_79
    | spl7_36
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f943,f875,f746,f437,f945])).

fof(f945,plain,
    ( spl7_79
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f943,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_36
    | ~ spl7_58
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f942,f748])).

fof(f942,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl7_36
    | ~ spl7_69 ),
    inference(forward_demodulation,[],[f439,f877])).

fof(f941,plain,
    ( ~ spl7_39
    | spl7_63
    | ~ spl7_69 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | ~ spl7_39
    | spl7_63
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f939,f790])).

fof(f790,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl7_63 ),
    inference(avatar_component_clause,[],[f788])).

fof(f937,plain,
    ( spl7_78
    | ~ spl7_69
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f932,f887,f875,f934])).

fof(f934,plain,
    ( spl7_78
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f932,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl7_69
    | ~ spl7_71 ),
    inference(forward_demodulation,[],[f889,f877])).

fof(f920,plain,
    ( spl7_71
    | spl7_77
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f883,f405,f373,f157,f142,f917,f887])).

fof(f883,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f871,f407])).

fof(f871,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(resolution,[],[f414,f375])).

fof(f915,plain,
    ( spl7_56
    | spl7_76
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f809,f385,f912,f727])).

fof(f809,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_xboole_0(sK2)
    | ~ spl7_29 ),
    inference(resolution,[],[f387,f277])).

fof(f910,plain,
    ( spl7_56
    | spl7_75
    | ~ spl7_29
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f905,f824,f385,f907,f727])).

fof(f907,plain,
    ( spl7_75
  <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f905,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | v1_xboole_0(sK2)
    | ~ spl7_29
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f809,f826])).

fof(f826,plain,
    ( k1_xboole_0 = u1_pre_topc(sK0)
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f824])).

fof(f904,plain,
    ( spl7_69
    | spl7_74
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f872,f167,f162,f157,f142,f901,f875])).

fof(f899,plain,
    ( spl7_71
    | spl7_73
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f884,f824,f405,f373,f157,f142,f896,f887])).

fof(f896,plain,
    ( spl7_73
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f884,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f883,f826])).

fof(f894,plain,
    ( spl7_71
    | spl7_72
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_58
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f885,f824,f746,f405,f373,f157,f142,f891,f887])).

fof(f891,plain,
    ( spl7_72
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f885,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_32
    | ~ spl7_58
    | ~ spl7_65 ),
    inference(forward_demodulation,[],[f884,f748])).

fof(f882,plain,
    ( spl7_69
    | spl7_70
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).

fof(f868,plain,
    ( spl7_66
    | spl7_52 ),
    inference(avatar_split_clause,[],[f834,f709,f844])).

fof(f844,plain,
    ( spl7_66
  <=> r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f834,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f216,f710,f277])).

fof(f867,plain,
    ( ~ spl7_68
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f836,f709,f197,f863])).

fof(f863,plain,
    ( spl7_68
  <=> r1_tarski(u1_pre_topc(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f836,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),k1_xboole_0)
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f212,f710,f277])).

fof(f866,plain,
    ( ~ spl7_68
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f861,f709,f197,f863])).

fof(f861,plain,
    ( ~ r1_tarski(u1_pre_topc(sK0),k1_xboole_0)
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f837,f571])).

fof(f837,plain,
    ( ! [X0] : ~ r1_tarski(u1_pre_topc(sK0),sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f551,f710,f277])).

fof(f860,plain,
    ( ~ spl7_67
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f838,f709,f197,f851])).

fof(f851,plain,
    ( spl7_67
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f838,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f710,f335])).

fof(f859,plain,
    ( ~ spl7_67
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f858,f709,f197,f851])).

fof(f858,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f839,f122])).

fof(f839,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f199,f710,f92])).

fof(f857,plain,
    ( ~ spl7_67
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f856,f709,f197,f851])).

fof(f856,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f855,f122])).

fof(f855,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f840,f348])).

fof(f840,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f332,f710,f92])).

fof(f854,plain,
    ( ~ spl7_67
    | ~ spl7_14
    | spl7_52 ),
    inference(avatar_split_clause,[],[f849,f709,f197,f851])).

fof(f849,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f848,f122])).

fof(f848,plain,
    ( ! [X0] : ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_52 ),
    inference(forward_demodulation,[],[f841,f571])).

fof(f841,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))
    | ~ spl7_14
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f558,f710,f92])).

fof(f847,plain,
    ( spl7_66
    | spl7_52 ),
    inference(avatar_split_clause,[],[f842,f709,f844])).

fof(f842,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl7_52 ),
    inference(unit_resulting_resolution,[],[f710,f91])).

fof(f828,plain,
    ( spl7_65
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f822,f709,f824])).

fof(f822,plain,
    ( k1_xboole_0 = u1_pre_topc(sK0)
    | ~ spl7_52 ),
    inference(resolution,[],[f711,f82])).

fof(f711,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f709])).

fof(f827,plain,
    ( spl7_65
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f819,f709,f824])).

fof(f819,plain,
    ( k1_xboole_0 = u1_pre_topc(sK0)
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f711,f82])).

fof(f805,plain,
    ( spl7_61
    | spl7_56 ),
    inference(avatar_split_clause,[],[f765,f727,f776])).

fof(f765,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f216,f728,f277])).

fof(f804,plain,
    ( ~ spl7_64
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f767,f727,f197,f800])).

fof(f767,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f212,f728,f277])).

fof(f803,plain,
    ( ~ spl7_64
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f798,f727,f197,f800])).

fof(f798,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f768,f571])).

fof(f768,plain,
    ( ! [X0] : ~ r1_tarski(sK2,sK6(k1_xboole_0,X0))
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f551,f728,f277])).

fof(f797,plain,
    ( ~ spl7_63
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f769,f727,f197,f788])).

fof(f769,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f728,f335])).

fof(f796,plain,
    ( ~ spl7_63
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f795,f727,f197,f788])).

fof(f795,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f770,f122])).

fof(f770,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f199,f728,f92])).

fof(f794,plain,
    ( ~ spl7_63
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f793,f727,f197,f788])).

fof(f793,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f792,f122])).

fof(f792,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f771,f348])).

fof(f771,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f332,f728,f92])).

fof(f791,plain,
    ( ~ spl7_63
    | ~ spl7_14
    | spl7_56 ),
    inference(avatar_split_clause,[],[f786,f727,f197,f788])).

fof(f786,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f785,f122])).

fof(f785,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_14
    | spl7_56 ),
    inference(forward_demodulation,[],[f772,f571])).

fof(f772,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))
    | ~ spl7_14
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f558,f728,f92])).

fof(f784,plain,
    ( ~ spl7_62
    | ~ spl7_7
    | spl7_56 ),
    inference(avatar_split_clause,[],[f773,f727,f162,f781])).

fof(f773,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_7
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f164,f728,f92])).

fof(f779,plain,
    ( spl7_61
    | spl7_56 ),
    inference(avatar_split_clause,[],[f774,f727,f776])).

fof(f774,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | spl7_56 ),
    inference(unit_resulting_resolution,[],[f728,f91])).

fof(f764,plain,
    ( spl7_60
    | spl7_39 ),
    inference(avatar_split_clause,[],[f753,f468,f760])).

fof(f760,plain,
    ( spl7_60
  <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f753,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2)
    | spl7_39 ),
    inference(resolution,[],[f470,f229])).

fof(f763,plain,
    ( spl7_60
    | spl7_39 ),
    inference(avatar_split_clause,[],[f751,f468,f760])).

fof(f751,plain,
    ( r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2)
    | spl7_39 ),
    inference(unit_resulting_resolution,[],[f470,f229])).

fof(f758,plain,
    ( ~ spl7_59
    | spl7_39 ),
    inference(avatar_split_clause,[],[f752,f468,f755])).

fof(f755,plain,
    ( spl7_59
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f752,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | spl7_39 ),
    inference(unit_resulting_resolution,[],[f470,f101])).

fof(f750,plain,
    ( spl7_58
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f744,f727,f746])).

fof(f744,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_56 ),
    inference(resolution,[],[f729,f82])).

fof(f729,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f727])).

fof(f749,plain,
    ( spl7_58
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f741,f727,f746])).

fof(f741,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f729,f82])).

fof(f734,plain,
    ( spl7_56
    | spl7_57
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f705,f221,f731,f727])).

fof(f705,plain,
    ( r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_xboole_0(sK2)
    | ~ spl7_16 ),
    inference(resolution,[],[f277,f223])).

fof(f725,plain,
    ( spl7_54
    | spl7_55
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f704,f620,f722,f718])).

fof(f704,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_49 ),
    inference(resolution,[],[f277,f622])).

fof(f716,plain,
    ( spl7_52
    | spl7_53
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f703,f587,f713,f709])).

fof(f703,plain,
    ( r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl7_46 ),
    inference(resolution,[],[f277,f589])).

fof(f684,plain,
    ( ~ spl7_40
    | ~ spl7_39
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_38 ),
    inference(avatar_split_clause,[],[f683,f464,f192,f187,f182,f177,f172,f167,f162,f132,f468,f472])).

fof(f683,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | spl7_38 ),
    inference(subsumption_resolution,[],[f682,f194])).

fof(f682,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_38 ),
    inference(subsumption_resolution,[],[f681,f189])).

fof(f681,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_38 ),
    inference(subsumption_resolution,[],[f680,f184])).

fof(f680,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_38 ),
    inference(subsumption_resolution,[],[f679,f179])).

fof(f679,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f678,f169])).

fof(f678,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f677,f164])).

fof(f677,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | ~ spl7_9
    | spl7_38 ),
    inference(subsumption_resolution,[],[f676,f174])).

fof(f676,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_1
    | spl7_38 ),
    inference(subsumption_resolution,[],[f675,f133])).

fof(f644,plain,
    ( spl7_51
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f633,f425,f640])).

fof(f633,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_33 ),
    inference(resolution,[],[f426,f83])).

fof(f643,plain,
    ( spl7_51
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f630,f425,f640])).

fof(f630,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f426,f83])).

fof(f638,plain,
    ( spl7_50
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f632,f425,f326,f635])).

fof(f632,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f328,f426,f85])).

fof(f625,plain,
    ( spl7_49
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f618,f262,f620])).

fof(f618,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_20 ),
    inference(resolution,[],[f264,f100])).

fof(f624,plain,
    ( spl7_33
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f615,f262,f425])).

fof(f615,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f264,f94])).

fof(f623,plain,
    ( spl7_49
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f617,f262,f620])).

fof(f617,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f264,f100])).

fof(f614,plain,
    ( spl7_48
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f603,f460,f610])).

fof(f603,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl7_37 ),
    inference(resolution,[],[f461,f83])).

fof(f613,plain,
    ( spl7_48
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f600,f460,f610])).

fof(f600,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f461,f83])).

fof(f608,plain,
    ( spl7_47
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f602,f460,f321,f605])).

fof(f602,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_25
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f323,f461,f85])).

fof(f592,plain,
    ( spl7_46
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f585,f257,f587])).

fof(f585,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19 ),
    inference(resolution,[],[f259,f100])).

fof(f591,plain,
    ( spl7_37
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f582,f257,f460])).

fof(f582,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f259,f94])).

fof(f590,plain,
    ( spl7_46
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f584,f257,f587])).

fof(f584,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f259,f100])).

fof(f539,plain,
    ( spl7_45
    | ~ spl7_37
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f504,f321,f460,f536])).

fof(f536,plain,
    ( spl7_45
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f504,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl7_25 ),
    inference(resolution,[],[f323,f84])).

fof(f534,plain,
    ( ~ spl7_19
    | spl7_37 ),
    inference(avatar_contradiction_clause,[],[f533])).

fof(f533,plain,
    ( $false
    | ~ spl7_19
    | spl7_37 ),
    inference(subsumption_resolution,[],[f530,f259])).

fof(f530,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_37 ),
    inference(resolution,[],[f462,f94])).

fof(f462,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl7_37 ),
    inference(avatar_component_clause,[],[f460])).

fof(f532,plain,
    ( ~ spl7_19
    | spl7_37 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | ~ spl7_19
    | spl7_37 ),
    inference(subsumption_resolution,[],[f529,f259])).

fof(f529,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_37 ),
    inference(unit_resulting_resolution,[],[f462,f94])).

fof(f528,plain,
    ( spl7_44
    | ~ spl7_33
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f515,f326,f425,f525])).

fof(f515,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_26 ),
    inference(resolution,[],[f328,f84])).

fof(f523,plain,
    ( ~ spl7_20
    | spl7_33 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl7_20
    | spl7_33 ),
    inference(subsumption_resolution,[],[f519,f264])).

fof(f519,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl7_33 ),
    inference(resolution,[],[f427,f94])).

fof(f427,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl7_33 ),
    inference(avatar_component_clause,[],[f425])).

fof(f521,plain,
    ( ~ spl7_20
    | spl7_33 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | ~ spl7_20
    | spl7_33 ),
    inference(subsumption_resolution,[],[f518,f264])).

fof(f518,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl7_33 ),
    inference(unit_resulting_resolution,[],[f427,f94])).

fof(f514,plain,
    ( spl7_43
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f513,f498,f248,f197,f508])).

fof(f498,plain,
    ( spl7_42
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f513,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f512,f250])).

fof(f512,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f506,f279])).

fof(f506,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_42 ),
    inference(resolution,[],[f500,f95])).

fof(f500,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f498])).

fof(f511,plain,
    ( spl7_43
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f505,f498,f248,f197,f508])).

fof(f505,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f250,f279,f500,f95])).

fof(f501,plain,
    ( spl7_42
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f491,f197,f498])).

fof(f491,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_14 ),
    inference(superposition,[],[f368,f348])).

fof(f368,plain,(
    ! [X0] : v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f367,f109])).

fof(f109,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f367,plain,(
    ! [X0] :
      ( v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0)
      | ~ v1_funct_1(sK6(k1_xboole_0,X0)) ) ),
    inference(subsumption_resolution,[],[f366,f235])).

fof(f366,plain,(
    ! [X0] :
      ( v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0)
      | ~ m1_subset_1(sK6(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(sK6(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f202,f110])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f126,f123])).

fof(f126,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f496,plain,
    ( spl7_41
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f489,f197,f493])).

fof(f489,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_14 ),
    inference(superposition,[],[f109,f348])).

fof(f475,plain,
    ( ~ spl7_37
    | ~ spl7_38
    | ~ spl7_39
    | ~ spl7_40
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | spl7_15
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f458,f321,f205,f182,f177,f157,f152,f147,f142,f472,f468,f464,f460])).

fof(f458,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | spl7_15
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f457,f144])).

fof(f457,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | spl7_15
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f456,f144])).

fof(f456,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11
    | spl7_15
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f455,f207])).

fof(f440,plain,
    ( ~ spl7_33
    | ~ spl7_34
    | ~ spl7_35
    | ~ spl7_36
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f423,f405,f373,f326,f205,f192,f187,f172,f437,f433,f429,f425])).

fof(f423,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_13
    | spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f422,f194])).

fof(f422,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | ~ spl7_12
    | spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f421,f189])).

fof(f421,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | spl7_15
    | ~ spl7_26
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f420,f328])).

fof(f420,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_9
    | spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f419,f174])).

fof(f419,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_15
    | ~ spl7_28
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f418,f375])).

fof(f418,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_15
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f417,f407])).

fof(f417,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_15 ),
    inference(resolution,[],[f127,f207])).

fof(f408,plain,
    ( spl7_32
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f382,f147,f142,f405])).

fof(f382,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(superposition,[],[f149,f144])).

fof(f403,plain,
    ( spl7_29
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f402,f147,f142,f385])).

fof(f402,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f381,f144])).

fof(f381,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_4 ),
    inference(resolution,[],[f149,f100])).

fof(f401,plain,
    ( spl7_31
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f396,f147,f142,f398])).

fof(f398,plain,
    ( spl7_31
  <=> v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f396,plain,
    ( v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f377,f144])).

fof(f377,plain,
    ( v5_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f149,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f395,plain,
    ( spl7_30
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f390,f147,f142,f392])).

fof(f390,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f378,f144])).

fof(f378,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f149,f112])).

fof(f388,plain,
    ( spl7_29
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f383,f147,f142,f385])).

fof(f383,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f380,f144])).

fof(f380,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f149,f100])).

fof(f376,plain,
    ( spl7_28
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f371,f152,f142,f373])).

fof(f371,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(superposition,[],[f154,f144])).

fof(f341,plain,
    ( spl7_27
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f336,f248,f197,f338])).

fof(f338,plain,
    ( spl7_27
  <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f336,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f250,f279,f121])).

fof(f121,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f329,plain,
    ( spl7_26
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f317,f182,f177,f326])).

fof(f317,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f184,f179,f85])).

fof(f324,plain,
    ( spl7_25
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f318,f192,f187,f321])).

fof(f318,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f194,f189,f85])).

fof(f316,plain,
    ( spl7_23
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f315,f192,f187,f304])).

fof(f315,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f302,f189])).

fof(f302,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_13 ),
    inference(resolution,[],[f84,f194])).

fof(f314,plain,
    ( spl7_24
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f313,f182,f177,f309])).

fof(f313,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f301,f179])).

fof(f301,plain,
    ( ~ l1_pre_topc(sK1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_11 ),
    inference(resolution,[],[f84,f184])).

fof(f312,plain,
    ( spl7_24
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f299,f182,f177,f309])).

fof(f299,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f184,f179,f84])).

fof(f307,plain,
    ( spl7_23
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f300,f192,f187,f304])).

fof(f300,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f194,f189,f84])).

fof(f295,plain,
    ( spl7_22
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f289,f162,f292])).

fof(f292,plain,
    ( spl7_22
  <=> v5_relat_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f289,plain,
    ( v5_relat_1(sK2,u1_struct_0(sK1))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f164,f113])).

fof(f286,plain,
    ( spl7_21
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f280,f162,f283])).

fof(f280,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f164,f112])).

fof(f267,plain,
    ( spl7_19
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f255,f187,f257])).

fof(f255,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_12 ),
    inference(resolution,[],[f83,f189])).

fof(f266,plain,
    ( spl7_20
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f254,f177,f262])).

fof(f254,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_10 ),
    inference(resolution,[],[f83,f179])).

fof(f265,plain,
    ( spl7_20
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f252,f177,f262])).

fof(f252,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f179,f83])).

fof(f260,plain,
    ( spl7_19
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f253,f187,f257])).

fof(f253,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f189,f83])).

fof(f251,plain,
    ( spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f239,f197,f248])).

fof(f239,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f230,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f246,plain,
    ( spl7_17
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f240,f162,f243])).

fof(f240,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f164,f111])).

fof(f225,plain,
    ( spl7_16
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f219,f162,f221])).

fof(f219,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_7 ),
    inference(resolution,[],[f164,f100])).

fof(f224,plain,
    ( spl7_16
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f218,f162,f221])).

fof(f218,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f164,f100])).

fof(f208,plain,
    ( ~ spl7_15
    | spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f203,f142,f136,f205])).

fof(f200,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f79,f197])).

fof(f79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f195,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f66,f192])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f190,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f67,f187])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f185,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f68,f182])).

fof(f68,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f180,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f69,f177])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f175,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f70,f172])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f170,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f71,f167])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f165,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f72,f162])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f160,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f73,f157])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f155,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f74,f152])).

fof(f74,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f150,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f75,f147])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f49])).

fof(f145,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f76,f142])).

fof(f76,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f77,f136,f132])).

fof(f77,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f139,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f78,f136,f132])).

fof(f78,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (27800)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (27822)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (27801)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (27803)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (27821)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (27813)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (27812)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (27804)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (27810)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (27805)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (27807)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (27808)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (27809)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (27821)Refutation not found, incomplete strategy% (27821)------------------------------
% 0.22/0.54  % (27821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27821)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27821)Memory used [KB]: 11001
% 0.22/0.54  % (27821)Time elapsed: 0.079 s
% 0.22/0.54  % (27821)------------------------------
% 0.22/0.54  % (27821)------------------------------
% 0.22/0.54  % (27799)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (27819)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (27802)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (27825)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.54  % (27826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (27816)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (27828)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (27823)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.55  % (27816)Refutation not found, incomplete strategy% (27816)------------------------------
% 1.42/0.55  % (27816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (27818)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (27810)Refutation not found, incomplete strategy% (27810)------------------------------
% 1.42/0.55  % (27810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (27810)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (27810)Memory used [KB]: 10874
% 1.42/0.55  % (27810)Time elapsed: 0.146 s
% 1.42/0.55  % (27810)------------------------------
% 1.42/0.55  % (27810)------------------------------
% 1.42/0.55  % (27824)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (27808)Refutation not found, incomplete strategy% (27808)------------------------------
% 1.42/0.55  % (27808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (27820)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.55  % (27811)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (27827)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (27814)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (27815)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (27817)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.56  % (27806)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.52/0.56  % (27816)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (27816)Memory used [KB]: 10746
% 1.52/0.56  % (27816)Time elapsed: 0.128 s
% 1.52/0.56  % (27816)------------------------------
% 1.52/0.56  % (27816)------------------------------
% 1.52/0.56  % (27809)Refutation not found, incomplete strategy% (27809)------------------------------
% 1.52/0.56  % (27809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (27809)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (27809)Memory used [KB]: 10874
% 1.52/0.56  % (27809)Time elapsed: 0.156 s
% 1.52/0.56  % (27809)------------------------------
% 1.52/0.56  % (27809)------------------------------
% 1.52/0.56  % (27820)Refutation not found, incomplete strategy% (27820)------------------------------
% 1.52/0.56  % (27820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (27820)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (27820)Memory used [KB]: 1791
% 1.52/0.56  % (27820)Time elapsed: 0.160 s
% 1.52/0.56  % (27820)------------------------------
% 1.52/0.56  % (27820)------------------------------
% 1.52/0.57  % (27808)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (27808)Memory used [KB]: 10874
% 1.52/0.57  % (27808)Time elapsed: 0.142 s
% 1.52/0.57  % (27808)------------------------------
% 1.52/0.57  % (27808)------------------------------
% 1.52/0.57  % (27799)Refutation not found, incomplete strategy% (27799)------------------------------
% 1.52/0.57  % (27799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (27799)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (27799)Memory used [KB]: 2046
% 1.52/0.59  % (27799)Time elapsed: 0.159 s
% 1.52/0.59  % (27799)------------------------------
% 1.52/0.59  % (27799)------------------------------
% 2.17/0.66  % (27874)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.17/0.68  % (27875)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.17/0.70  % (27874)Refutation not found, incomplete strategy% (27874)------------------------------
% 2.17/0.70  % (27874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.70  % (27878)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.17/0.70  % (27879)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.17/0.70  % (27880)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.17/0.71  % (27877)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.71  % (27876)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.71  % (27874)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.71  
% 2.17/0.71  % (27874)Memory used [KB]: 6524
% 2.17/0.71  % (27874)Time elapsed: 0.123 s
% 2.17/0.71  % (27874)------------------------------
% 2.17/0.71  % (27874)------------------------------
% 2.17/0.73  % (27878)Refutation not found, incomplete strategy% (27878)------------------------------
% 2.17/0.73  % (27878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (27878)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (27878)Memory used [KB]: 11001
% 2.17/0.73  % (27878)Time elapsed: 0.145 s
% 2.17/0.73  % (27878)------------------------------
% 2.17/0.73  % (27878)------------------------------
% 2.69/0.74  % (27800)Refutation not found, incomplete strategy% (27800)------------------------------
% 2.69/0.74  % (27800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.69/0.74  % (27800)Termination reason: Refutation not found, incomplete strategy
% 2.69/0.74  
% 2.69/0.74  % (27800)Memory used [KB]: 6524
% 2.69/0.74  % (27800)Time elapsed: 0.339 s
% 2.69/0.74  % (27800)------------------------------
% 2.69/0.74  % (27800)------------------------------
% 3.31/0.84  % (27875)Refutation not found, incomplete strategy% (27875)------------------------------
% 3.31/0.84  % (27875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.84  % (27875)Termination reason: Refutation not found, incomplete strategy
% 3.31/0.84  
% 3.31/0.84  % (27875)Memory used [KB]: 6268
% 3.31/0.84  % (27875)Time elapsed: 0.260 s
% 3.31/0.84  % (27875)------------------------------
% 3.31/0.84  % (27875)------------------------------
% 3.31/0.84  % (27801)Refutation not found, incomplete strategy% (27801)------------------------------
% 3.31/0.84  % (27801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.84  % (27801)Termination reason: Refutation not found, incomplete strategy
% 3.31/0.84  
% 3.31/0.84  % (27801)Memory used [KB]: 13176
% 3.31/0.84  % (27801)Time elapsed: 0.428 s
% 3.31/0.84  % (27801)------------------------------
% 3.31/0.84  % (27801)------------------------------
% 3.31/0.85  % (27886)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.53/0.86  % (27804)Time limit reached!
% 3.53/0.86  % (27804)------------------------------
% 3.53/0.86  % (27804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.86  % (27804)Termination reason: Time limit
% 3.53/0.86  % (27804)Termination phase: Saturation
% 3.53/0.86  
% 3.53/0.86  % (27804)Memory used [KB]: 8315
% 3.53/0.86  % (27804)Time elapsed: 0.400 s
% 3.53/0.86  % (27804)------------------------------
% 3.53/0.86  % (27804)------------------------------
% 3.53/0.86  % (27888)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.53/0.88  % (27894)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.53/0.91  % (27811)Time limit reached!
% 3.53/0.91  % (27811)------------------------------
% 3.53/0.91  % (27811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.91  % (27811)Termination reason: Time limit
% 3.53/0.91  
% 3.53/0.91  % (27811)Memory used [KB]: 7547
% 3.53/0.91  % (27811)Time elapsed: 0.511 s
% 3.53/0.91  % (27811)------------------------------
% 3.53/0.91  % (27811)------------------------------
% 3.93/0.95  % (27899)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.12/0.97  % (27900)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.12/0.98  % (27910)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.12/1.00  % (27827)Time limit reached!
% 4.12/1.00  % (27827)------------------------------
% 4.12/1.00  % (27827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.01  % (27815)Time limit reached!
% 4.12/1.01  % (27815)------------------------------
% 4.12/1.01  % (27815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.01  % (27806)Time limit reached!
% 4.12/1.01  % (27806)------------------------------
% 4.12/1.01  % (27806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.01  % (27806)Termination reason: Time limit
% 4.12/1.01  
% 4.12/1.01  % (27806)Memory used [KB]: 8315
% 4.12/1.01  % (27806)Time elapsed: 0.610 s
% 4.12/1.01  % (27806)------------------------------
% 4.12/1.01  % (27806)------------------------------
% 4.12/1.01  % (27815)Termination reason: Time limit
% 4.12/1.01  % (27815)Termination phase: Saturation
% 4.12/1.01  
% 4.12/1.01  % (27815)Memory used [KB]: 15223
% 4.12/1.01  % (27815)Time elapsed: 0.600 s
% 4.12/1.01  % (27815)------------------------------
% 4.12/1.01  % (27815)------------------------------
% 4.12/1.02  % (27877)Time limit reached!
% 4.12/1.02  % (27877)------------------------------
% 4.12/1.02  % (27877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.02  % (27877)Termination reason: Time limit
% 4.12/1.02  
% 4.12/1.02  % (27877)Memory used [KB]: 6780
% 4.12/1.02  % (27877)Time elapsed: 0.411 s
% 4.12/1.02  % (27877)------------------------------
% 4.12/1.02  % (27877)------------------------------
% 4.12/1.02  % (27827)Termination reason: Time limit
% 4.12/1.02  % (27827)Termination phase: Saturation
% 4.12/1.02  
% 4.12/1.02  % (27827)Memory used [KB]: 7036
% 4.12/1.02  % (27827)Time elapsed: 0.600 s
% 4.12/1.02  % (27827)------------------------------
% 4.12/1.02  % (27827)------------------------------
% 4.63/1.05  % (27934)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.63/1.14  % (27985)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.15/1.14  % (27991)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.15/1.15  % (27981)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.15/1.15  % (27980)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 7.90/1.41  % (27910)Time limit reached!
% 7.90/1.41  % (27910)------------------------------
% 7.90/1.41  % (27910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.90/1.41  % (27910)Termination reason: Time limit
% 7.90/1.41  % (27910)Termination phase: Saturation
% 7.90/1.41  
% 7.90/1.41  % (27910)Memory used [KB]: 2302
% 7.90/1.41  % (27910)Time elapsed: 0.500 s
% 7.90/1.41  % (27910)------------------------------
% 7.90/1.41  % (27910)------------------------------
% 8.48/1.45  % (27985)Time limit reached!
% 8.48/1.45  % (27985)------------------------------
% 8.48/1.45  % (27985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.48/1.45  % (27985)Termination reason: Time limit
% 8.48/1.45  % (27985)Termination phase: Saturation
% 8.48/1.45  
% 8.48/1.45  % (27985)Memory used [KB]: 3454
% 8.48/1.45  % (27985)Time elapsed: 0.400 s
% 8.48/1.45  % (27985)------------------------------
% 8.48/1.45  % (27985)------------------------------
% 8.67/1.52  % (27879)Refutation found. Thanks to Tanya!
% 8.67/1.52  % SZS status Theorem for theBenchmark
% 8.67/1.52  % SZS output start Proof for theBenchmark
% 8.67/1.52  fof(f3303,plain,(
% 8.67/1.52    $false),
% 8.67/1.52    inference(avatar_sat_refutation,[],[f139,f140,f145,f150,f155,f160,f165,f170,f175,f180,f185,f190,f195,f200,f208,f224,f225,f246,f251,f260,f265,f266,f267,f286,f295,f307,f312,f314,f316,f324,f329,f341,f376,f388,f395,f401,f403,f408,f440,f475,f496,f501,f511,f514,f521,f523,f528,f532,f534,f539,f590,f591,f592,f608,f613,f614,f623,f624,f625,f638,f643,f644,f684,f716,f725,f734,f749,f750,f758,f763,f764,f779,f784,f791,f794,f796,f797,f803,f804,f805,f827,f828,f847,f854,f857,f859,f860,f866,f867,f868,f882,f894,f899,f904,f910,f915,f920,f937,f941,f948,f956,f962,f969,f975,f984,f985,f987,f988,f992,f1009,f1041,f1051,f1056,f1073,f1074,f1082,f1087,f1088,f1102,f1109,f1112,f1114,f1115,f1121,f1122,f1123,f1137,f1139,f1145,f1147,f1149,f1155,f1157,f1159,f1160,f1161,f1195,f1196,f1217,f1224,f1227,f1229,f1230,f1236,f1237,f1238,f1258,f1270,f1295,f1296,f1297,f1299,f1316,f1319,f1320,f1409,f1418,f1419,f1436,f1441,f1442,f1447,f1455,f1459,f1467,f1471,f1488,f1493,f1498,f1522,f1526,f1530,f1537,f1542,f1547,f1549,f1551,f1556,f1557,f1566,f1572,f1594,f1596,f1603,f1606,f1608,f1610,f1612,f1621,f1625,f1639,f1662,f1669,f1671,f1689,f1694,f1699,f1704,f1705,f1710,f1715,f1721,f1726,f1753,f1760,f1764,f1769,f1770,f1771,f1772,f1778,f1782,f1785,f1788,f1792,f1794,f1800,f1804,f1823,f1907,f1913,f1918,f1931,f1936,f1939,f1963,f1981,f1994,f1997,f1999,f2000,f2002,f2003,f2005,f2007,f2014,f2020,f2024,f2030,f2034,f2036,f2043,f2052,f2054,f2057,f2061,f2063,f2066,f2069,f2073,f2078,f2084,f2103,f2107,f2110,f2114,f2163,f2168,f2169,f2174,f2205,f2223,f2228,f2233,f2234,f2239,f2244,f2249,f2297,f2304,f2332,f2350,f2413,f2416,f2419,f2421,f2425,f2429,f2431,f2434,f2440,f2444,f2448,f2451,f2454,f2457,f2465,f2468,f2470,f2515,f2521,f2526,f2539,f2545,f2548,f2551,f2575,f2593,f2607,f2618,f2648,f2652,f2656,f2660,f2664,f2668,f2672,f2676,f2680,f2684,f2686,f2695,f2697,f2702,f2709,f2711,f2726,f2733,f2735,f2740,f2752,f2755,f2761,f2763,f2764,f2766,f2788,f2794,f2800,f2802,f2852,f2854,f2873,f2880,f2882,f2884,f2891,f2894,f2896,f2898,f2900,f2903,f2919,f2926,f2931,f2933,f2934,f2951,f2957,f2958,f2959,f2965,f2967,f2968,f2969,f2970,f2971,f2992,f2997,f3002,f3007,f3012,f3013,f3018,f3023,f3028,f3033,f3047,f3051,f3055,f3058,f3076,f3083,f3088,f3090,f3091,f3114,f3119,f3124,f3129,f3134,f3139,f3144,f3149,f3154,f3155,f3160,f3165,f3174,f3178,f3182,f3186,f3189,f3210,f3215,f3217,f3265,f3302])).
% 8.67/1.52  fof(f3302,plain,(
% 8.67/1.52    ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_71 | ~spl7_81 | spl7_83 | ~spl7_102),
% 8.67/1.52    inference(avatar_contradiction_clause,[],[f3301])).
% 8.67/1.52  fof(f3301,plain,(
% 8.67/1.52    $false | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_71 | ~spl7_81 | spl7_83 | ~spl7_102)),
% 8.67/1.52    inference(subsumption_resolution,[],[f3300,f486])).
% 8.67/1.52  fof(f486,plain,(
% 8.67/1.52    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0)) ) | ~spl7_14),
% 8.67/1.52    inference(superposition,[],[f110,f348])).
% 8.67/1.52  fof(f348,plain,(
% 8.67/1.52    ( ! [X0] : (k1_xboole_0 = sK6(X0,k1_xboole_0)) ) | ~spl7_14),
% 8.67/1.52    inference(unit_resulting_resolution,[],[f332,f82])).
% 8.67/1.52  fof(f82,plain,(
% 8.67/1.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 8.67/1.52    inference(cnf_transformation,[],[f25])).
% 8.67/1.52  fof(f25,plain,(
% 8.67/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 8.67/1.52    inference(ennf_transformation,[],[f4])).
% 8.67/1.52  fof(f4,axiom,(
% 8.67/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 8.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 8.67/1.52  fof(f332,plain,(
% 8.67/1.52    ( ! [X0] : (v1_xboole_0(sK6(X0,k1_xboole_0))) ) | ~spl7_14),
% 8.67/1.52    inference(unit_resulting_resolution,[],[f199,f105,f92])).
% 8.67/1.52  fof(f92,plain,(
% 8.67/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 8.67/1.52    inference(cnf_transformation,[],[f33])).
% 8.67/1.52  fof(f33,plain,(
% 8.67/1.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 8.67/1.52    inference(ennf_transformation,[],[f12])).
% 8.67/1.52  fof(f12,axiom,(
% 8.67/1.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 8.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 8.67/1.52  fof(f105,plain,(
% 8.67/1.52    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.67/1.52    inference(cnf_transformation,[],[f65])).
% 8.67/1.52  fof(f65,plain,(
% 8.67/1.52    ! [X0,X1] : (v1_funct_2(sK6(X0,X1),X0,X1) & v1_funct_1(sK6(X0,X1)) & v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.67/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f64])).
% 8.67/1.52  fof(f64,plain,(
% 8.67/1.52    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK6(X0,X1),X0,X1) & v1_funct_1(sK6(X0,X1)) & v5_relat_1(sK6(X0,X1),X1) & v4_relat_1(sK6(X0,X1),X0) & v1_relat_1(sK6(X0,X1)) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.67/1.52    introduced(choice_axiom,[])).
% 8.67/1.52  fof(f14,axiom,(
% 8.67/1.52    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.67/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 8.67/1.52  fof(f199,plain,(
% 8.67/1.52    v1_xboole_0(k1_xboole_0) | ~spl7_14),
% 8.67/1.52    inference(avatar_component_clause,[],[f197])).
% 8.67/1.52  fof(f197,plain,(
% 8.67/1.52    spl7_14 <=> v1_xboole_0(k1_xboole_0)),
% 8.67/1.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 8.67/1.52  fof(f110,plain,(
% 8.67/1.52    ( ! [X0,X1] : (v1_funct_2(sK6(X0,X1),X0,X1)) )),
% 8.67/1.52    inference(cnf_transformation,[],[f65])).
% 8.67/1.52  fof(f3300,plain,(
% 8.67/1.52    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_71 | ~spl7_81 | spl7_83 | ~spl7_102)),
% 8.67/1.52    inference(forward_demodulation,[],[f3296,f889])).
% 8.67/1.52  fof(f889,plain,(
% 8.67/1.52    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_71),
% 8.67/1.52    inference(avatar_component_clause,[],[f887])).
% 8.67/1.52  fof(f887,plain,(
% 8.67/1.52    spl7_71 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 8.67/1.52    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 8.67/1.52  fof(f3296,plain,(
% 8.67/1.52    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_81 | spl7_83 | ~spl7_102)),
% 8.67/1.52    inference(unit_resulting_resolution,[],[f194,f189,f184,f179,f495,f960,f230,f974,f230,f1294,f129])).
% 8.67/1.52  fof(f129,plain,(
% 8.67/1.52    ( ! [X0,X3,X1] : (~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.67/1.52    inference(duplicate_literal_removal,[],[f118])).
% 9.09/1.53  fof(f118,plain,(
% 9.09/1.53    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.53    inference(equality_resolution,[],[f86])).
% 9.09/1.53  fof(f86,plain,(
% 9.09/1.53    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.53    inference(cnf_transformation,[],[f50])).
% 9.09/1.53  fof(f50,plain,(
% 9.09/1.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.09/1.53    inference(nnf_transformation,[],[f30])).
% 9.09/1.54  fof(f30,plain,(
% 9.09/1.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.09/1.54    inference(flattening,[],[f29])).
% 9.09/1.54  fof(f29,plain,(
% 9.09/1.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 9.09/1.54    inference(ennf_transformation,[],[f20])).
% 9.09/1.54  fof(f20,axiom,(
% 9.09/1.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 9.09/1.54  fof(f1294,plain,(
% 9.09/1.54    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl7_102),
% 9.09/1.54    inference(avatar_component_clause,[],[f1292])).
% 9.09/1.54  fof(f1292,plain,(
% 9.09/1.54    spl7_102 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 9.09/1.54  fof(f974,plain,(
% 9.09/1.54    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_83),
% 9.09/1.54    inference(avatar_component_clause,[],[f972])).
% 9.09/1.54  fof(f972,plain,(
% 9.09/1.54    spl7_83 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 9.09/1.54  fof(f230,plain,(
% 9.09/1.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f228,f101])).
% 9.09/1.54  fof(f101,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 9.09/1.54    inference(cnf_transformation,[],[f61])).
% 9.09/1.54  fof(f61,plain,(
% 9.09/1.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 9.09/1.54    inference(nnf_transformation,[],[f8])).
% 9.09/1.54  fof(f8,axiom,(
% 9.09/1.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 9.09/1.54  fof(f228,plain,(
% 9.09/1.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f212,f98])).
% 9.09/1.54  fof(f98,plain,(
% 9.09/1.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f60])).
% 9.09/1.54  fof(f60,plain,(
% 9.09/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 9.09/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f58,f59])).
% 9.09/1.54  fof(f59,plain,(
% 9.09/1.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 9.09/1.54    introduced(choice_axiom,[])).
% 9.09/1.54  fof(f58,plain,(
% 9.09/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 9.09/1.54    inference(rectify,[],[f57])).
% 9.09/1.54  fof(f57,plain,(
% 9.09/1.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 9.09/1.54    inference(nnf_transformation,[],[f37])).
% 9.09/1.54  fof(f37,plain,(
% 9.09/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 9.09/1.54    inference(ennf_transformation,[],[f2])).
% 9.09/1.54  fof(f2,axiom,(
% 9.09/1.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 9.09/1.54  fof(f212,plain,(
% 9.09/1.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f199,f90])).
% 9.09/1.54  fof(f90,plain,(
% 9.09/1.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f55])).
% 9.09/1.54  fof(f55,plain,(
% 9.09/1.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 9.09/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).
% 9.09/1.54  fof(f54,plain,(
% 9.09/1.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 9.09/1.54    introduced(choice_axiom,[])).
% 9.09/1.54  fof(f53,plain,(
% 9.09/1.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 9.09/1.54    inference(rectify,[],[f52])).
% 9.09/1.54  fof(f52,plain,(
% 9.09/1.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 9.09/1.54    inference(nnf_transformation,[],[f1])).
% 9.09/1.54  fof(f1,axiom,(
% 9.09/1.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 9.09/1.54  fof(f960,plain,(
% 9.09/1.54    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl7_81),
% 9.09/1.54    inference(avatar_component_clause,[],[f959])).
% 9.09/1.54  fof(f959,plain,(
% 9.09/1.54    spl7_81 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).
% 9.09/1.54  fof(f495,plain,(
% 9.09/1.54    v1_funct_1(k1_xboole_0) | ~spl7_41),
% 9.09/1.54    inference(avatar_component_clause,[],[f493])).
% 9.09/1.54  fof(f493,plain,(
% 9.09/1.54    spl7_41 <=> v1_funct_1(k1_xboole_0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 9.09/1.54  fof(f179,plain,(
% 9.09/1.54    l1_pre_topc(sK1) | ~spl7_10),
% 9.09/1.54    inference(avatar_component_clause,[],[f177])).
% 9.09/1.54  fof(f177,plain,(
% 9.09/1.54    spl7_10 <=> l1_pre_topc(sK1)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 9.09/1.54  fof(f184,plain,(
% 9.09/1.54    v2_pre_topc(sK1) | ~spl7_11),
% 9.09/1.54    inference(avatar_component_clause,[],[f182])).
% 9.09/1.54  fof(f182,plain,(
% 9.09/1.54    spl7_11 <=> v2_pre_topc(sK1)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 9.09/1.54  fof(f189,plain,(
% 9.09/1.54    l1_pre_topc(sK0) | ~spl7_12),
% 9.09/1.54    inference(avatar_component_clause,[],[f187])).
% 9.09/1.54  fof(f187,plain,(
% 9.09/1.54    spl7_12 <=> l1_pre_topc(sK0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 9.09/1.54  fof(f194,plain,(
% 9.09/1.54    v2_pre_topc(sK0) | ~spl7_13),
% 9.09/1.54    inference(avatar_component_clause,[],[f192])).
% 9.09/1.54  fof(f192,plain,(
% 9.09/1.54    spl7_13 <=> v2_pre_topc(sK0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 9.09/1.54  fof(f3265,plain,(
% 9.09/1.54    spl7_222 | spl7_223 | ~spl7_185),
% 9.09/1.54    inference(avatar_split_clause,[],[f3255,f2749,f3262,f3258])).
% 9.09/1.54  fof(f3258,plain,(
% 9.09/1.54    spl7_222 <=> v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).
% 9.09/1.54  fof(f3262,plain,(
% 9.09/1.54    spl7_223 <=> r2_hidden(sK4(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_223])])).
% 9.09/1.54  fof(f2749,plain,(
% 9.09/1.54    spl7_185 <=> r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_185])])).
% 9.09/1.54  fof(f3255,plain,(
% 9.09/1.54    r2_hidden(sK4(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_185),
% 9.09/1.54    inference(resolution,[],[f2751,f277])).
% 9.09/1.54  fof(f277,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK4(X0),X1) | v1_xboole_0(X0)) )),
% 9.09/1.54    inference(resolution,[],[f97,f91])).
% 9.09/1.54  fof(f91,plain,(
% 9.09/1.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f55])).
% 9.09/1.54  fof(f97,plain,(
% 9.09/1.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f60])).
% 9.09/1.54  fof(f2751,plain,(
% 9.09/1.54    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0)) | ~spl7_185),
% 9.09/1.54    inference(avatar_component_clause,[],[f2749])).
% 9.09/1.54  fof(f3217,plain,(
% 9.09/1.54    spl7_220 | ~spl7_166 | ~spl7_168),
% 9.09/1.54    inference(avatar_split_clause,[],[f3216,f2329,f2301,f3207])).
% 9.09/1.54  fof(f3207,plain,(
% 9.09/1.54    spl7_220 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).
% 9.09/1.54  fof(f2301,plain,(
% 9.09/1.54    spl7_166 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).
% 9.09/1.54  fof(f2329,plain,(
% 9.09/1.54    spl7_168 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).
% 9.09/1.54  fof(f3216,plain,(
% 9.09/1.54    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))) | (~spl7_166 | ~spl7_168)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3204,f2303])).
% 9.09/1.54  fof(f2303,plain,(
% 9.09/1.54    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_166),
% 9.09/1.54    inference(avatar_component_clause,[],[f2301])).
% 9.09/1.54  fof(f3204,plain,(
% 9.09/1.54    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))) | ~spl7_168),
% 9.09/1.54    inference(resolution,[],[f2330,f1357])).
% 9.09/1.54  fof(f1357,plain,(
% 9.09/1.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) )),
% 9.09/1.54    inference(subsumption_resolution,[],[f1356,f83])).
% 9.09/1.54  fof(f83,plain,(
% 9.09/1.54    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 9.09/1.54    inference(cnf_transformation,[],[f26])).
% 9.09/1.54  fof(f26,plain,(
% 9.09/1.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.09/1.54    inference(ennf_transformation,[],[f17])).
% 9.09/1.54  fof(f17,axiom,(
% 9.09/1.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 9.09/1.54  fof(f1356,plain,(
% 9.09/1.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 9.09/1.54    inference(resolution,[],[f319,f94])).
% 9.09/1.54  fof(f94,plain,(
% 9.09/1.54    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 9.09/1.54    inference(cnf_transformation,[],[f34])).
% 9.09/1.54  fof(f34,plain,(
% 9.09/1.54    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 9.09/1.54    inference(ennf_transformation,[],[f16])).
% 9.09/1.54  fof(f16,axiom,(
% 9.09/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 9.09/1.54  fof(f319,plain,(
% 9.09/1.54    ( ! [X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) )),
% 9.09/1.54    inference(resolution,[],[f85,f84])).
% 9.09/1.54  fof(f84,plain,(
% 9.09/1.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 9.09/1.54    inference(cnf_transformation,[],[f28])).
% 9.09/1.54  fof(f28,plain,(
% 9.09/1.54    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.09/1.54    inference(flattening,[],[f27])).
% 9.09/1.54  fof(f27,plain,(
% 9.09/1.54    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 9.09/1.54    inference(ennf_transformation,[],[f18])).
% 9.09/1.54  fof(f18,axiom,(
% 9.09/1.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 9.09/1.54  fof(f85,plain,(
% 9.09/1.54    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f28])).
% 9.09/1.54  fof(f2330,plain,(
% 9.09/1.54    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_168),
% 9.09/1.54    inference(avatar_component_clause,[],[f2329])).
% 9.09/1.54  fof(f3215,plain,(
% 9.09/1.54    spl7_221 | ~spl7_166 | ~spl7_168),
% 9.09/1.54    inference(avatar_split_clause,[],[f3202,f2329,f2301,f3212])).
% 9.09/1.54  fof(f3212,plain,(
% 9.09/1.54    spl7_221 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_221])])).
% 9.09/1.54  fof(f3202,plain,(
% 9.09/1.54    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_166 | ~spl7_168)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2303,f2330,f85])).
% 9.09/1.54  fof(f3210,plain,(
% 9.09/1.54    spl7_220 | ~spl7_166 | ~spl7_168),
% 9.09/1.54    inference(avatar_split_clause,[],[f3203,f2329,f2301,f3207])).
% 9.09/1.54  fof(f3203,plain,(
% 9.09/1.54    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))) | (~spl7_166 | ~spl7_168)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2303,f2330,f1357])).
% 9.09/1.54  fof(f3189,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_126),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3188])).
% 9.09/1.54  fof(f3188,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_126)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3187,f230])).
% 9.09/1.54  fof(f3187,plain,(
% 9.09/1.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3170,f123])).
% 9.09/1.54  fof(f123,plain,(
% 9.09/1.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 9.09/1.54    inference(equality_resolution,[],[f103])).
% 9.09/1.54  fof(f103,plain,(
% 9.09/1.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 9.09/1.54    inference(cnf_transformation,[],[f63])).
% 9.09/1.54  fof(f63,plain,(
% 9.09/1.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 9.09/1.54    inference(flattening,[],[f62])).
% 9.09/1.54  fof(f62,plain,(
% 9.09/1.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 9.09/1.54    inference(nnf_transformation,[],[f5])).
% 9.09/1.54  fof(f5,axiom,(
% 9.09/1.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 9.09/1.54  fof(f3170,plain,(
% 9.09/1.54    ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(superposition,[],[f1602,f1466])).
% 9.09/1.54  fof(f1466,plain,(
% 9.09/1.54    k1_xboole_0 = k1_relat_1(sK2) | ~spl7_114),
% 9.09/1.54    inference(avatar_component_clause,[],[f1464])).
% 9.09/1.54  fof(f1464,plain,(
% 9.09/1.54    spl7_114 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).
% 9.09/1.54  fof(f1602,plain,(
% 9.09/1.54    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | spl7_126),
% 9.09/1.54    inference(avatar_component_clause,[],[f1600])).
% 9.09/1.54  fof(f1600,plain,(
% 9.09/1.54    spl7_126 <=> m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).
% 9.09/1.54  fof(f3186,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_43 | ~spl7_58 | spl7_126),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3185])).
% 9.09/1.54  fof(f3185,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_43 | ~spl7_58 | spl7_126)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3184,f230])).
% 9.09/1.54  fof(f3184,plain,(
% 9.09/1.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_43 | ~spl7_58 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3183,f123])).
% 9.09/1.54  fof(f3183,plain,(
% 9.09/1.54    ~m1_subset_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_43 | ~spl7_58 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3169,f510])).
% 9.09/1.54  fof(f510,plain,(
% 9.09/1.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_43),
% 9.09/1.54    inference(avatar_component_clause,[],[f508])).
% 9.09/1.54  fof(f508,plain,(
% 9.09/1.54    spl7_43 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 9.09/1.54  fof(f3169,plain,(
% 9.09/1.54    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_58 | spl7_126)),
% 9.09/1.54    inference(superposition,[],[f1602,f748])).
% 9.09/1.54  fof(f748,plain,(
% 9.09/1.54    k1_xboole_0 = sK2 | ~spl7_58),
% 9.09/1.54    inference(avatar_component_clause,[],[f746])).
% 9.09/1.54  fof(f746,plain,(
% 9.09/1.54    spl7_58 <=> k1_xboole_0 = sK2),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 9.09/1.54  fof(f3182,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_126),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3181])).
% 9.09/1.54  fof(f3181,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_126)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3180,f212])).
% 9.09/1.54  fof(f3180,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3179,f123])).
% 9.09/1.54  fof(f3179,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3168,f1466])).
% 9.09/1.54  fof(f3168,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | spl7_126),
% 9.09/1.54    inference(resolution,[],[f1602,f229])).
% 9.09/1.54  fof(f229,plain,(
% 9.09/1.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK5(X0,X1),X0)) )),
% 9.09/1.54    inference(resolution,[],[f98,f101])).
% 9.09/1.54  fof(f3178,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_126),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3177])).
% 9.09/1.54  fof(f3177,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_126)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3176,f212])).
% 9.09/1.54  fof(f3176,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3175,f123])).
% 9.09/1.54  fof(f3175,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3166,f1466])).
% 9.09/1.54  fof(f3166,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | spl7_126),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1602,f229])).
% 9.09/1.54  fof(f3174,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_126),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3173])).
% 9.09/1.54  fof(f3173,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_126)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3172,f228])).
% 9.09/1.54  fof(f3172,plain,(
% 9.09/1.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3171,f123])).
% 9.09/1.54  fof(f3171,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0) | (~spl7_114 | spl7_126)),
% 9.09/1.54    inference(forward_demodulation,[],[f3167,f1466])).
% 9.09/1.54  fof(f3167,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0) | spl7_126),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1602,f101])).
% 9.09/1.54  fof(f3165,plain,(
% 9.09/1.54    ~spl7_219 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3092,f2017,f3162])).
% 9.09/1.54  fof(f3162,plain,(
% 9.09/1.54    spl7_219 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_219])])).
% 9.09/1.54  fof(f2017,plain,(
% 9.09/1.54    spl7_151 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).
% 9.09/1.54  fof(f3092,plain,(
% 9.09/1.54    ~v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | spl7_151),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2019,f82])).
% 9.09/1.54  fof(f2019,plain,(
% 9.09/1.54    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | spl7_151),
% 9.09/1.54    inference(avatar_component_clause,[],[f2017])).
% 9.09/1.54  fof(f3160,plain,(
% 9.09/1.54    ~spl7_218 | spl7_69 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3093,f2017,f875,f3157])).
% 9.09/1.54  fof(f3157,plain,(
% 9.09/1.54    spl7_218 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).
% 9.09/1.54  fof(f875,plain,(
% 9.09/1.54    spl7_69 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 9.09/1.54  fof(f3093,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_69 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f876,f2019,f102])).
% 9.09/1.54  fof(f102,plain,(
% 9.09/1.54    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 9.09/1.54    inference(cnf_transformation,[],[f63])).
% 9.09/1.54  fof(f876,plain,(
% 9.09/1.54    k1_xboole_0 != u1_struct_0(sK1) | spl7_69),
% 9.09/1.54    inference(avatar_component_clause,[],[f875])).
% 9.09/1.54  fof(f3155,plain,(
% 9.09/1.54    ~spl7_213 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3094,f2017,f3131])).
% 9.09/1.54  fof(f3131,plain,(
% 9.09/1.54    spl7_213 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).
% 9.09/1.54  fof(f3094,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | spl7_151),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2019,f2019,f102])).
% 9.09/1.54  fof(f3154,plain,(
% 9.09/1.54    ~spl7_217 | spl7_65 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3095,f2017,f824,f3151])).
% 9.09/1.54  fof(f3151,plain,(
% 9.09/1.54    spl7_217 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_217])])).
% 9.09/1.54  fof(f824,plain,(
% 9.09/1.54    spl7_65 <=> k1_xboole_0 = u1_pre_topc(sK0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 9.09/1.54  fof(f3095,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0)) | (spl7_65 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f825,f2019,f102])).
% 9.09/1.54  fof(f825,plain,(
% 9.09/1.54    k1_xboole_0 != u1_pre_topc(sK0) | spl7_65),
% 9.09/1.54    inference(avatar_component_clause,[],[f824])).
% 9.09/1.54  fof(f3149,plain,(
% 9.09/1.54    ~spl7_216 | spl7_86 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3096,f2017,f1070,f3146])).
% 9.09/1.54  fof(f3146,plain,(
% 9.09/1.54    spl7_216 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).
% 9.09/1.54  fof(f1070,plain,(
% 9.09/1.54    spl7_86 <=> k1_xboole_0 = u1_pre_topc(sK1)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).
% 9.09/1.54  fof(f3096,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1)) | (spl7_86 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1071,f2019,f102])).
% 9.09/1.54  fof(f1071,plain,(
% 9.09/1.54    k1_xboole_0 != u1_pre_topc(sK1) | spl7_86),
% 9.09/1.54    inference(avatar_component_clause,[],[f1070])).
% 9.09/1.54  fof(f3144,plain,(
% 9.09/1.54    ~spl7_215 | spl7_110 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3097,f2017,f1433,f3141])).
% 9.09/1.54  fof(f3141,plain,(
% 9.09/1.54    spl7_215 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).
% 9.09/1.54  fof(f1433,plain,(
% 9.09/1.54    spl7_110 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).
% 9.09/1.54  fof(f3097,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | (spl7_110 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1435,f2019,f102])).
% 9.09/1.54  fof(f1435,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) | spl7_110),
% 9.09/1.54    inference(avatar_component_clause,[],[f1433])).
% 9.09/1.54  fof(f3139,plain,(
% 9.09/1.54    ~spl7_214 | spl7_69 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3099,f2017,f875,f3136])).
% 9.09/1.54  fof(f3136,plain,(
% 9.09/1.54    spl7_214 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).
% 9.09/1.54  fof(f3099,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (spl7_69 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f876,f2019,f102])).
% 9.09/1.54  fof(f3134,plain,(
% 9.09/1.54    ~spl7_213 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3100,f2017,f3131])).
% 9.09/1.54  fof(f3100,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | spl7_151),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2019,f2019,f102])).
% 9.09/1.54  fof(f3129,plain,(
% 9.09/1.54    ~spl7_212 | spl7_65 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3101,f2017,f824,f3126])).
% 9.09/1.54  fof(f3126,plain,(
% 9.09/1.54    spl7_212 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).
% 9.09/1.54  fof(f3101,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (spl7_65 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f825,f2019,f102])).
% 9.09/1.54  fof(f3124,plain,(
% 9.09/1.54    ~spl7_211 | spl7_86 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3102,f2017,f1070,f3121])).
% 9.09/1.54  fof(f3121,plain,(
% 9.09/1.54    spl7_211 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_211])])).
% 9.09/1.54  fof(f3102,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (spl7_86 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1071,f2019,f102])).
% 9.09/1.54  fof(f3119,plain,(
% 9.09/1.54    ~spl7_210 | spl7_110 | spl7_151),
% 9.09/1.54    inference(avatar_split_clause,[],[f3103,f2017,f1433,f3116])).
% 9.09/1.54  fof(f3116,plain,(
% 9.09/1.54    spl7_210 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).
% 9.09/1.54  fof(f3103,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (spl7_110 | spl7_151)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1435,f2019,f102])).
% 9.09/1.54  fof(f3114,plain,(
% 9.09/1.54    ~spl7_209 | ~spl7_14 | ~spl7_41 | spl7_151 | spl7_153),
% 9.09/1.54    inference(avatar_split_clause,[],[f3105,f2040,f2017,f493,f197,f3111])).
% 9.09/1.54  fof(f3111,plain,(
% 9.09/1.54    spl7_209 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).
% 9.09/1.54  fof(f2040,plain,(
% 9.09/1.54    spl7_153 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).
% 9.09/1.54  fof(f3105,plain,(
% 9.09/1.54    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (~spl7_14 | ~spl7_41 | spl7_151 | spl7_153)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2042,f495,f230,f2019,f125])).
% 9.09/1.54  fof(f125,plain,(
% 9.09/1.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 9.09/1.54    inference(duplicate_literal_removal,[],[f114])).
% 9.09/1.54  fof(f114,plain,(
% 9.09/1.54    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f41])).
% 9.09/1.54  fof(f41,plain,(
% 9.09/1.54    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 9.09/1.54    inference(flattening,[],[f40])).
% 9.09/1.54  fof(f40,plain,(
% 9.09/1.54    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 9.09/1.54    inference(ennf_transformation,[],[f15])).
% 9.09/1.54  fof(f15,axiom,(
% 9.09/1.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 9.09/1.54  fof(f2042,plain,(
% 9.09/1.54    ~v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | spl7_153),
% 9.09/1.54    inference(avatar_component_clause,[],[f2040])).
% 9.09/1.54  fof(f3091,plain,(
% 9.09/1.54    spl7_208 | ~spl7_14 | spl7_195),
% 9.09/1.54    inference(avatar_split_clause,[],[f3061,f2948,f197,f3085])).
% 9.09/1.54  fof(f3085,plain,(
% 9.09/1.54    spl7_208 <=> r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).
% 9.09/1.54  fof(f2948,plain,(
% 9.09/1.54    spl7_195 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_195])])).
% 9.09/1.54  fof(f3061,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_14 | spl7_195)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f212,f2950,f701])).
% 9.09/1.54  fof(f701,plain,(
% 9.09/1.54    ( ! [X2,X1] : (r2_hidden(sK5(X1,X2),X1) | v1_xboole_0(X1) | r2_hidden(sK4(X1),X2)) )),
% 9.09/1.54    inference(resolution,[],[f277,f98])).
% 9.09/1.54  fof(f2950,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | spl7_195),
% 9.09/1.54    inference(avatar_component_clause,[],[f2948])).
% 9.09/1.54  fof(f3090,plain,(
% 9.09/1.54    spl7_208 | ~spl7_14 | spl7_195),
% 9.09/1.54    inference(avatar_split_clause,[],[f3089,f2948,f197,f3085])).
% 9.09/1.54  fof(f3089,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_14 | spl7_195)),
% 9.09/1.54    inference(forward_demodulation,[],[f3062,f571])).
% 9.09/1.54  fof(f571,plain,(
% 9.09/1.54    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f558,f82])).
% 9.09/1.54  fof(f558,plain,(
% 9.09/1.54    ( ! [X0] : (v1_xboole_0(sK6(k1_xboole_0,X0))) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f235,f335])).
% 9.09/1.54  fof(f335,plain,(
% 9.09/1.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl7_14),
% 9.09/1.54    inference(forward_demodulation,[],[f333,f122])).
% 9.09/1.54  fof(f122,plain,(
% 9.09/1.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 9.09/1.54    inference(equality_resolution,[],[f104])).
% 9.09/1.54  fof(f104,plain,(
% 9.09/1.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 9.09/1.54    inference(cnf_transformation,[],[f63])).
% 9.09/1.54  fof(f333,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl7_14),
% 9.09/1.54    inference(resolution,[],[f92,f199])).
% 9.09/1.54  fof(f235,plain,(
% 9.09/1.54    ( ! [X1] : (m1_subset_1(sK6(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 9.09/1.54    inference(superposition,[],[f105,f123])).
% 9.09/1.54  fof(f3062,plain,(
% 9.09/1.54    ( ! [X0] : (r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),sK6(k1_xboole_0,X0)),k1_zfmisc_1(u1_struct_0(sK1)))) ) | (~spl7_14 | spl7_195)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f551,f2950,f701])).
% 9.09/1.54  fof(f551,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~r2_hidden(X0,sK6(k1_xboole_0,X1))) ) | ~spl7_14),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f199,f235,f116])).
% 9.09/1.54  fof(f116,plain,(
% 9.09/1.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f42])).
% 9.09/1.54  fof(f42,plain,(
% 9.09/1.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 9.09/1.54    inference(ennf_transformation,[],[f9])).
% 9.09/1.54  fof(f9,axiom,(
% 9.09/1.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 9.09/1.54  fof(f3088,plain,(
% 9.09/1.54    spl7_208 | ~spl7_14 | spl7_195),
% 9.09/1.54    inference(avatar_split_clause,[],[f3063,f2948,f197,f3085])).
% 9.09/1.54  fof(f3063,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_14 | spl7_195)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2950,f690])).
% 9.09/1.54  fof(f690,plain,(
% 9.09/1.54    ( ! [X2] : (r2_hidden(sK5(X2,k1_xboole_0),X2) | v1_xboole_0(X2)) ) | ~spl7_14),
% 9.09/1.54    inference(resolution,[],[f229,f335])).
% 9.09/1.54  fof(f3083,plain,(
% 9.09/1.54    spl7_207 | spl7_195),
% 9.09/1.54    inference(avatar_split_clause,[],[f3064,f2948,f3073])).
% 9.09/1.54  fof(f3073,plain,(
% 9.09/1.54    spl7_207 <=> r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).
% 9.09/1.54  fof(f3064,plain,(
% 9.09/1.54    r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) | spl7_195),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f216,f2950,f277])).
% 9.09/1.54  fof(f216,plain,(
% 9.09/1.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f201,f100])).
% 9.09/1.54  fof(f100,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 9.09/1.54    inference(cnf_transformation,[],[f61])).
% 9.09/1.54  fof(f201,plain,(
% 9.09/1.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 9.09/1.54    inference(forward_demodulation,[],[f81,f80])).
% 9.09/1.54  fof(f80,plain,(
% 9.09/1.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 9.09/1.54    inference(cnf_transformation,[],[f6])).
% 9.09/1.54  fof(f6,axiom,(
% 9.09/1.54    ! [X0] : k2_subset_1(X0) = X0),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 9.09/1.54  fof(f81,plain,(
% 9.09/1.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 9.09/1.54    inference(cnf_transformation,[],[f7])).
% 9.09/1.54  fof(f7,axiom,(
% 9.09/1.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 9.09/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 9.09/1.54  fof(f3076,plain,(
% 9.09/1.54    spl7_207 | spl7_195),
% 9.09/1.54    inference(avatar_split_clause,[],[f3071,f2948,f3073])).
% 9.09/1.54  fof(f3071,plain,(
% 9.09/1.54    r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK1))),k1_zfmisc_1(u1_struct_0(sK1))) | spl7_195),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2950,f91])).
% 9.09/1.54  fof(f3058,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_125),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3057])).
% 9.09/1.54  fof(f3057,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_125)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3056,f228])).
% 9.09/1.54  fof(f3056,plain,(
% 9.09/1.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3043,f123])).
% 9.09/1.54  fof(f3043,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(superposition,[],[f1593,f1466])).
% 9.09/1.54  fof(f1593,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0) | spl7_125),
% 9.09/1.54    inference(avatar_component_clause,[],[f1591])).
% 9.09/1.54  fof(f1591,plain,(
% 9.09/1.54    spl7_125 <=> r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).
% 9.09/1.54  fof(f3055,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_43 | ~spl7_58 | spl7_125),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3054])).
% 9.09/1.54  fof(f3054,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_43 | ~spl7_58 | spl7_125)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3053,f228])).
% 9.09/1.54  fof(f3053,plain,(
% 9.09/1.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_43 | ~spl7_58 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3052,f123])).
% 9.09/1.54  fof(f3052,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0) | (~spl7_43 | ~spl7_58 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3042,f510])).
% 9.09/1.54  fof(f3042,plain,(
% 9.09/1.54    ~r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)),k1_xboole_0) | (~spl7_58 | spl7_125)),
% 9.09/1.54    inference(superposition,[],[f1593,f748])).
% 9.09/1.54  fof(f3051,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_125),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3050])).
% 9.09/1.54  fof(f3050,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_125)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3049,f212])).
% 9.09/1.54  fof(f3049,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3048,f123])).
% 9.09/1.54  fof(f3048,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3041,f1466])).
% 9.09/1.54  fof(f3041,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | spl7_125),
% 9.09/1.54    inference(resolution,[],[f1593,f98])).
% 9.09/1.54  fof(f3047,plain,(
% 9.09/1.54    ~spl7_14 | ~spl7_114 | spl7_125),
% 9.09/1.54    inference(avatar_contradiction_clause,[],[f3046])).
% 9.09/1.54  fof(f3046,plain,(
% 9.09/1.54    $false | (~spl7_14 | ~spl7_114 | spl7_125)),
% 9.09/1.54    inference(subsumption_resolution,[],[f3045,f212])).
% 9.09/1.54  fof(f3045,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3044,f123])).
% 9.09/1.54  fof(f3044,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_114 | spl7_125)),
% 9.09/1.54    inference(forward_demodulation,[],[f3039,f1466])).
% 9.09/1.54  fof(f3039,plain,(
% 9.09/1.54    r2_hidden(sK5(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0),k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))) | spl7_125),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1593,f98])).
% 9.09/1.54  fof(f3033,plain,(
% 9.09/1.54    ~spl7_206 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2972,f1433,f3030])).
% 9.09/1.54  fof(f3030,plain,(
% 9.09/1.54    spl7_206 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).
% 9.09/1.54  fof(f2972,plain,(
% 9.09/1.54    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | spl7_110),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1435,f82])).
% 9.09/1.54  fof(f3028,plain,(
% 9.09/1.54    ~spl7_205 | spl7_69 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2973,f1433,f875,f3025])).
% 9.09/1.54  fof(f3025,plain,(
% 9.09/1.54    spl7_205 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_205])])).
% 9.09/1.54  fof(f2973,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) | (spl7_69 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f876,f1435,f102])).
% 9.09/1.54  fof(f3023,plain,(
% 9.09/1.54    ~spl7_204 | spl7_65 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2974,f1433,f824,f3020])).
% 9.09/1.54  fof(f3020,plain,(
% 9.09/1.54    spl7_204 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).
% 9.09/1.54  fof(f2974,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK0)) | (spl7_65 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f825,f1435,f102])).
% 9.09/1.54  fof(f3018,plain,(
% 9.09/1.54    ~spl7_203 | spl7_86 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2975,f1433,f1070,f3015])).
% 9.09/1.54  fof(f3015,plain,(
% 9.09/1.54    spl7_203 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK1))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).
% 9.09/1.54  fof(f2975,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_pre_topc(sK1)) | (spl7_86 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1071,f1435,f102])).
% 9.09/1.54  fof(f3013,plain,(
% 9.09/1.54    ~spl7_199 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2976,f1433,f2994])).
% 9.09/1.54  fof(f2994,plain,(
% 9.09/1.54    spl7_199 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_199])])).
% 9.09/1.54  fof(f2976,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | spl7_110),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1435,f1435,f102])).
% 9.09/1.54  fof(f3012,plain,(
% 9.09/1.54    ~spl7_202 | spl7_69 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2978,f1433,f875,f3009])).
% 9.09/1.54  fof(f3009,plain,(
% 9.09/1.54    spl7_202 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_202])])).
% 9.09/1.54  fof(f2978,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | (spl7_69 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f876,f1435,f102])).
% 9.09/1.54  fof(f3007,plain,(
% 9.09/1.54    ~spl7_201 | spl7_65 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2979,f1433,f824,f3004])).
% 9.09/1.54  fof(f3004,plain,(
% 9.09/1.54    spl7_201 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).
% 9.09/1.54  fof(f2979,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | (spl7_65 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f825,f1435,f102])).
% 9.09/1.54  fof(f3002,plain,(
% 9.09/1.54    ~spl7_200 | spl7_86 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2980,f1433,f1070,f2999])).
% 9.09/1.54  fof(f2999,plain,(
% 9.09/1.54    spl7_200 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).
% 9.09/1.54  fof(f2980,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | (spl7_86 | spl7_110)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1071,f1435,f102])).
% 9.09/1.54  fof(f2997,plain,(
% 9.09/1.54    ~spl7_199 | spl7_110),
% 9.09/1.54    inference(avatar_split_clause,[],[f2981,f1433,f2994])).
% 9.09/1.54  fof(f2981,plain,(
% 9.09/1.54    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | spl7_110),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f1435,f1435,f102])).
% 9.09/1.54  fof(f2992,plain,(
% 9.09/1.54    ~spl7_198 | ~spl7_14 | ~spl7_41 | spl7_110 | spl7_153),
% 9.09/1.54    inference(avatar_split_clause,[],[f2983,f2040,f1433,f493,f197,f2989])).
% 9.09/1.54  fof(f2989,plain,(
% 9.09/1.54    spl7_198 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).
% 9.09/1.54  fof(f2983,plain,(
% 9.09/1.54    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) | (~spl7_14 | ~spl7_41 | spl7_110 | spl7_153)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1435,f125])).
% 9.09/1.54  fof(f2971,plain,(
% 9.09/1.54    ~spl7_195 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2946,f722,f2948])).
% 9.09/1.54  fof(f722,plain,(
% 9.09/1.54    spl7_55 <=> r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 9.09/1.54  fof(f2946,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_55),
% 9.09/1.54    inference(resolution,[],[f724,f90])).
% 9.09/1.54  fof(f724,plain,(
% 9.09/1.54    r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_55),
% 9.09/1.54    inference(avatar_component_clause,[],[f722])).
% 9.09/1.54  fof(f2970,plain,(
% 9.09/1.54    ~spl7_197 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2944,f722,f197,f2962])).
% 9.09/1.54  fof(f2962,plain,(
% 9.09/1.54    spl7_197 <=> m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_197])])).
% 9.09/1.54  fof(f2944,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(resolution,[],[f724,f298])).
% 9.09/1.54  fof(f298,plain,(
% 9.09/1.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl7_14),
% 9.09/1.54    inference(resolution,[],[f116,f199])).
% 9.09/1.54  fof(f2969,plain,(
% 9.09/1.54    ~spl7_197 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2935,f722,f197,f2962])).
% 9.09/1.54  fof(f2935,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f724,f298])).
% 9.09/1.54  fof(f2968,plain,(
% 9.09/1.54    ~spl7_197 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2936,f722,f197,f2962])).
% 9.09/1.54  fof(f2936,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f199,f724,f116])).
% 9.09/1.54  fof(f2967,plain,(
% 9.09/1.54    ~spl7_197 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2966,f722,f197,f2962])).
% 9.09/1.54  fof(f2966,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(forward_demodulation,[],[f2937,f348])).
% 9.09/1.54  fof(f2937,plain,(
% 9.09/1.54    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))) ) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f332,f724,f116])).
% 9.09/1.54  fof(f2965,plain,(
% 9.09/1.54    ~spl7_197 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2960,f722,f197,f2962])).
% 9.09/1.54  fof(f2960,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(forward_demodulation,[],[f2938,f571])).
% 9.09/1.54  fof(f2938,plain,(
% 9.09/1.54    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))) ) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f558,f724,f116])).
% 9.09/1.54  fof(f2959,plain,(
% 9.09/1.54    ~spl7_195 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2939,f722,f2948])).
% 9.09/1.54  fof(f2939,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_55),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f201,f724,f116])).
% 9.09/1.54  fof(f2958,plain,(
% 9.09/1.54    ~spl7_196 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2941,f722,f197,f2954])).
% 9.09/1.54  fof(f2954,plain,(
% 9.09/1.54    spl7_196 <=> r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).
% 9.09/1.54  fof(f2941,plain,(
% 9.09/1.54    ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f212,f724,f97])).
% 9.09/1.54  fof(f2957,plain,(
% 9.09/1.54    ~spl7_196 | ~spl7_14 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2952,f722,f197,f2954])).
% 9.09/1.54  fof(f2952,plain,(
% 9.09/1.54    ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(forward_demodulation,[],[f2942,f571])).
% 9.09/1.54  fof(f2942,plain,(
% 9.09/1.54    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(u1_struct_0(sK1)),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | ~spl7_55)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f551,f724,f97])).
% 9.09/1.54  fof(f2951,plain,(
% 9.09/1.54    ~spl7_195 | ~spl7_55),
% 9.09/1.54    inference(avatar_split_clause,[],[f2943,f722,f2948])).
% 9.09/1.54  fof(f2943,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_55),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f724,f90])).
% 9.09/1.54  fof(f2934,plain,(
% 9.09/1.54    spl7_194 | ~spl7_14 | spl7_190),
% 9.09/1.54    inference(avatar_split_clause,[],[f2904,f2870,f197,f2928])).
% 9.09/1.54  fof(f2928,plain,(
% 9.09/1.54    spl7_194 <=> r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).
% 9.09/1.54  fof(f2870,plain,(
% 9.09/1.54    spl7_190 <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).
% 9.09/1.54  fof(f2904,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_190)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f212,f2872,f701])).
% 9.09/1.54  fof(f2872,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | spl7_190),
% 9.09/1.54    inference(avatar_component_clause,[],[f2870])).
% 9.09/1.54  fof(f2933,plain,(
% 9.09/1.54    spl7_194 | ~spl7_14 | spl7_190),
% 9.09/1.54    inference(avatar_split_clause,[],[f2932,f2870,f197,f2928])).
% 9.09/1.54  fof(f2932,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_190)),
% 9.09/1.54    inference(forward_demodulation,[],[f2905,f571])).
% 9.09/1.54  fof(f2905,plain,(
% 9.09/1.54    ( ! [X0] : (r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),sK6(k1_xboole_0,X0)),k1_zfmisc_1(k1_xboole_0))) ) | (~spl7_14 | spl7_190)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f551,f2872,f701])).
% 9.09/1.54  fof(f2931,plain,(
% 9.09/1.54    spl7_194 | ~spl7_14 | spl7_190),
% 9.09/1.54    inference(avatar_split_clause,[],[f2906,f2870,f197,f2928])).
% 9.09/1.54  fof(f2906,plain,(
% 9.09/1.54    r2_hidden(sK5(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_190)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2872,f690])).
% 9.09/1.54  fof(f2926,plain,(
% 9.09/1.54    spl7_193 | spl7_190),
% 9.09/1.54    inference(avatar_split_clause,[],[f2907,f2870,f2916])).
% 9.09/1.54  fof(f2916,plain,(
% 9.09/1.54    spl7_193 <=> r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).
% 9.09/1.54  fof(f2907,plain,(
% 9.09/1.54    r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | spl7_190),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f216,f2872,f277])).
% 9.09/1.54  fof(f2919,plain,(
% 9.09/1.54    spl7_193 | spl7_190),
% 9.09/1.54    inference(avatar_split_clause,[],[f2914,f2870,f2916])).
% 9.09/1.54  fof(f2914,plain,(
% 9.09/1.54    r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | spl7_190),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f2872,f91])).
% 9.09/1.54  fof(f2903,plain,(
% 9.09/1.54    ~spl7_190 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2902,f1452,f713,f2870])).
% 9.09/1.54  fof(f713,plain,(
% 9.09/1.54    spl7_53 <=> r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 9.09/1.54  fof(f1452,plain,(
% 9.09/1.54    spl7_113 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 9.09/1.54  fof(f2902,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | (~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2866,f1454])).
% 9.09/1.54  fof(f1454,plain,(
% 9.09/1.54    k1_xboole_0 = u1_struct_0(sK0) | ~spl7_113),
% 9.09/1.54    inference(avatar_component_clause,[],[f1452])).
% 9.09/1.54  fof(f2866,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_53),
% 9.09/1.54    inference(resolution,[],[f715,f90])).
% 9.09/1.54  fof(f715,plain,(
% 9.09/1.54    r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_53),
% 9.09/1.54    inference(avatar_component_clause,[],[f713])).
% 9.09/1.54  fof(f2900,plain,(
% 9.09/1.54    ~spl7_192 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2899,f1452,f713,f197,f2888])).
% 9.09/1.54  fof(f2888,plain,(
% 9.09/1.54    spl7_192 <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).
% 9.09/1.54  fof(f2899,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2864,f1454])).
% 9.09/1.54  fof(f2864,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(resolution,[],[f715,f298])).
% 9.09/1.54  fof(f2898,plain,(
% 9.09/1.54    ~spl7_192 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2897,f1452,f713,f197,f2888])).
% 9.09/1.54  fof(f2897,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2855,f1454])).
% 9.09/1.54  fof(f2855,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f715,f298])).
% 9.09/1.54  fof(f2896,plain,(
% 9.09/1.54    ~spl7_192 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2895,f1452,f713,f197,f2888])).
% 9.09/1.54  fof(f2895,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2856,f1454])).
% 9.09/1.54  fof(f2856,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f199,f715,f116])).
% 9.09/1.54  fof(f2894,plain,(
% 9.09/1.54    ~spl7_192 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2893,f1452,f713,f197,f2888])).
% 9.09/1.54  fof(f2893,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2892,f1454])).
% 9.09/1.54  fof(f2892,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(forward_demodulation,[],[f2857,f348])).
% 9.09/1.54  fof(f2857,plain,(
% 9.09/1.54    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))) ) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f332,f715,f116])).
% 9.09/1.54  fof(f2891,plain,(
% 9.09/1.54    ~spl7_192 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2886,f1452,f713,f197,f2888])).
% 9.09/1.54  fof(f2886,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2885,f1454])).
% 9.09/1.54  fof(f2885,plain,(
% 9.09/1.54    ~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(forward_demodulation,[],[f2858,f571])).
% 9.09/1.54  fof(f2858,plain,(
% 9.09/1.54    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))) ) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f558,f715,f116])).
% 9.09/1.54  fof(f2884,plain,(
% 9.09/1.54    ~spl7_190 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2883,f1452,f713,f2870])).
% 9.09/1.54  fof(f2883,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | (~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2859,f1454])).
% 9.09/1.54  fof(f2859,plain,(
% 9.09/1.54    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_53),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f201,f715,f116])).
% 9.09/1.54  fof(f2882,plain,(
% 9.09/1.54    ~spl7_191 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.54    inference(avatar_split_clause,[],[f2881,f1452,f713,f197,f2877])).
% 9.09/1.54  fof(f2877,plain,(
% 9.09/1.54    spl7_191 <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)),
% 9.09/1.54    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).
% 9.09/1.54  fof(f2881,plain,(
% 9.09/1.54    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.54    inference(forward_demodulation,[],[f2861,f1454])).
% 9.09/1.54  fof(f2861,plain,(
% 9.09/1.54    ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0) | (~spl7_14 | ~spl7_53)),
% 9.09/1.54    inference(unit_resulting_resolution,[],[f212,f715,f97])).
% 9.09/1.54  % (28109)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 9.09/1.55  fof(f2880,plain,(
% 9.09/1.55    ~spl7_191 | ~spl7_14 | ~spl7_53 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2875,f1452,f713,f197,f2877])).
% 9.09/1.55  fof(f2875,plain,(
% 9.09/1.55    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (~spl7_14 | ~spl7_53 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2874,f1454])).
% 9.09/1.55  fof(f2874,plain,(
% 9.09/1.55    ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),k1_xboole_0) | (~spl7_14 | ~spl7_53)),
% 9.09/1.55    inference(forward_demodulation,[],[f2862,f571])).
% 9.09/1.55  fof(f2862,plain,(
% 9.09/1.55    ( ! [X0] : (~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | ~spl7_53)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f551,f715,f97])).
% 9.09/1.55  fof(f2873,plain,(
% 9.09/1.55    ~spl7_190 | ~spl7_53 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2868,f1452,f713,f2870])).
% 9.09/1.55  fof(f2868,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | (~spl7_53 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2863,f1454])).
% 9.09/1.55  fof(f2863,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_53),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f715,f90])).
% 9.09/1.55  fof(f2854,plain,(
% 9.09/1.55    spl7_189 | spl7_52 | ~spl7_175),
% 9.09/1.55    inference(avatar_split_clause,[],[f2853,f2542,f709,f2849])).
% 9.09/1.55  fof(f2849,plain,(
% 9.09/1.55    spl7_189 <=> r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).
% 9.09/1.55  fof(f709,plain,(
% 9.09/1.55    spl7_52 <=> v1_xboole_0(u1_pre_topc(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 9.09/1.55  fof(f2542,plain,(
% 9.09/1.55    spl7_175 <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_175])])).
% 9.09/1.55  fof(f2853,plain,(
% 9.09/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0)) | (spl7_52 | ~spl7_175)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2846,f710])).
% 9.09/1.55  fof(f710,plain,(
% 9.09/1.55    ~v1_xboole_0(u1_pre_topc(sK0)) | spl7_52),
% 9.09/1.55    inference(avatar_component_clause,[],[f709])).
% 9.09/1.55  fof(f2846,plain,(
% 9.09/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(u1_pre_topc(sK0)) | ~spl7_175),
% 9.09/1.55    inference(resolution,[],[f2544,f277])).
% 9.09/1.55  fof(f2544,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | ~spl7_175),
% 9.09/1.55    inference(avatar_component_clause,[],[f2542])).
% 9.09/1.55  fof(f2852,plain,(
% 9.09/1.55    spl7_189 | spl7_52 | ~spl7_175),
% 9.09/1.55    inference(avatar_split_clause,[],[f2844,f2542,f709,f2849])).
% 9.09/1.55  fof(f2844,plain,(
% 9.09/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(k1_xboole_0)) | (spl7_52 | ~spl7_175)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f710,f2544,f277])).
% 9.09/1.55  fof(f2802,plain,(
% 9.09/1.55    spl7_187 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2801,f887,f640,f2785])).
% 9.09/1.55  fof(f2785,plain,(
% 9.09/1.55    spl7_187 <=> r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).
% 9.09/1.55  fof(f640,plain,(
% 9.09/1.55    spl7_51 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 9.09/1.55  fof(f2801,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2782,f889])).
% 9.09/1.55  fof(f2782,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | ~spl7_51),
% 9.09/1.55    inference(resolution,[],[f1204,f642])).
% 9.09/1.55  fof(f642,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_51),
% 9.09/1.55    inference(avatar_component_clause,[],[f640])).
% 9.09/1.55  fof(f1204,plain,(
% 9.09/1.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | r1_tarski(u1_pre_topc(g1_pre_topc(X1,X0)),k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X0))))) )),
% 9.09/1.55    inference(resolution,[],[f272,f100])).
% 9.09/1.55  fof(f272,plain,(
% 9.09/1.55    ( ! [X0,X1] : (m1_subset_1(u1_pre_topc(g1_pre_topc(X1,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X0))))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 9.09/1.55    inference(resolution,[],[f94,f83])).
% 9.09/1.55  fof(f2800,plain,(
% 9.09/1.55    spl7_188 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2799,f1452,f610,f2791])).
% 9.09/1.55  fof(f2791,plain,(
% 9.09/1.55    spl7_188 <=> r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).
% 9.09/1.55  fof(f610,plain,(
% 9.09/1.55    spl7_48 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 9.09/1.55  fof(f2799,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2781,f1454])).
% 9.09/1.55  fof(f2781,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) | ~spl7_48),
% 9.09/1.55    inference(resolution,[],[f1204,f612])).
% 9.09/1.55  fof(f612,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~spl7_48),
% 9.09/1.55    inference(avatar_component_clause,[],[f610])).
% 9.09/1.55  fof(f2794,plain,(
% 9.09/1.55    spl7_188 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2789,f1452,f610,f2791])).
% 9.09/1.55  fof(f2789,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2772,f1454])).
% 9.09/1.55  fof(f2772,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) | ~spl7_48),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f612,f1204])).
% 9.09/1.55  fof(f2788,plain,(
% 9.09/1.55    spl7_187 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2783,f887,f640,f2785])).
% 9.09/1.55  fof(f2783,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2773,f889])).
% 9.09/1.55  fof(f2773,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | ~spl7_51),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f642,f1204])).
% 9.09/1.55  fof(f2766,plain,(
% 9.09/1.55    ~spl7_168 | spl7_167 | ~spl7_50 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2765,f887,f635,f2325,f2329])).
% 9.09/1.55  fof(f2325,plain,(
% 9.09/1.55    spl7_167 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).
% 9.09/1.55  fof(f635,plain,(
% 9.09/1.55    spl7_50 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 9.09/1.55  fof(f2765,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_50 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2690,f889])).
% 9.09/1.55  fof(f2690,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_50 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2688,f889])).
% 9.09/1.55  fof(f2688,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | ~spl7_50),
% 9.09/1.55    inference(resolution,[],[f637,f84])).
% 9.09/1.55  fof(f637,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_50),
% 9.09/1.55    inference(avatar_component_clause,[],[f635])).
% 9.09/1.55  fof(f2764,plain,(
% 9.09/1.55    spl7_168 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2753,f887,f640,f2329])).
% 9.09/1.55  fof(f2753,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2742,f889])).
% 9.09/1.55  fof(f2742,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_51),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f642,f94])).
% 9.09/1.55  fof(f2763,plain,(
% 9.09/1.55    spl7_185 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2762,f887,f640,f2749])).
% 9.09/1.55  fof(f2762,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0)) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2745,f889])).
% 9.09/1.55  fof(f2745,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_51),
% 9.09/1.55    inference(resolution,[],[f642,f100])).
% 9.09/1.55  fof(f2761,plain,(
% 9.09/1.55    spl7_186 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2756,f887,f640,f2758])).
% 9.09/1.55  fof(f2758,plain,(
% 9.09/1.55    spl7_186 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).
% 9.09/1.55  fof(f2756,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2741,f889])).
% 9.09/1.55  fof(f2741,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~spl7_51),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f642,f272])).
% 9.09/1.55  fof(f2755,plain,(
% 9.09/1.55    ~spl7_51 | ~spl7_71 | spl7_168),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2754])).
% 9.09/1.55  fof(f2754,plain,(
% 9.09/1.55    $false | (~spl7_51 | ~spl7_71 | spl7_168)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2753,f2331])).
% 9.09/1.55  fof(f2331,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl7_168),
% 9.09/1.55    inference(avatar_component_clause,[],[f2329])).
% 9.09/1.55  fof(f2752,plain,(
% 9.09/1.55    spl7_185 | ~spl7_51 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2747,f887,f640,f2749])).
% 9.09/1.55  fof(f2747,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_xboole_0)) | (~spl7_51 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2744,f889])).
% 9.09/1.55  fof(f2744,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_51),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f642,f100])).
% 9.09/1.55  fof(f2740,plain,(
% 9.09/1.55    spl7_184 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2720,f1452,f610,f2737])).
% 9.09/1.55  fof(f2737,plain,(
% 9.09/1.55    spl7_184 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).
% 9.09/1.55  fof(f2720,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f612,f1454])).
% 9.09/1.55  fof(f2735,plain,(
% 9.09/1.55    spl7_182 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2734,f1452,f610,f2723])).
% 9.09/1.55  fof(f2723,plain,(
% 9.09/1.55    spl7_182 <=> r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).
% 9.09/1.55  fof(f2734,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2719,f1454])).
% 9.09/1.55  fof(f2719,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl7_48),
% 9.09/1.55    inference(resolution,[],[f612,f100])).
% 9.09/1.55  fof(f2733,plain,(
% 9.09/1.55    spl7_183 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2728,f1452,f610,f2730])).
% 9.09/1.55  fof(f2730,plain,(
% 9.09/1.55    spl7_183 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).
% 9.09/1.55  fof(f2728,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2715,f1454])).
% 9.09/1.55  fof(f2715,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))) | ~spl7_48),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f612,f272])).
% 9.09/1.55  fof(f2726,plain,(
% 9.09/1.55    spl7_182 | ~spl7_48 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2721,f1452,f610,f2723])).
% 9.09/1.55  fof(f2721,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_48 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2718,f1454])).
% 9.09/1.55  fof(f2718,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl7_48),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f612,f100])).
% 9.09/1.55  fof(f2711,plain,(
% 9.09/1.55    spl7_180 | ~spl7_104 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2710,f1452,f1390,f2699])).
% 9.09/1.55  fof(f2699,plain,(
% 9.09/1.55    spl7_180 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).
% 9.09/1.55  fof(f1390,plain,(
% 9.09/1.55    spl7_104 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 9.09/1.55  fof(f2710,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_104 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1391,f1454])).
% 9.09/1.55  fof(f1391,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl7_104),
% 9.09/1.55    inference(avatar_component_clause,[],[f1390])).
% 9.09/1.55  fof(f2709,plain,(
% 9.09/1.55    ~spl7_180 | spl7_181 | ~spl7_47 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2704,f1452,f605,f2706,f2699])).
% 9.09/1.55  fof(f2706,plain,(
% 9.09/1.55    spl7_181 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_181])])).
% 9.09/1.55  fof(f605,plain,(
% 9.09/1.55    spl7_47 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 9.09/1.55  fof(f2704,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_47 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2703,f1454])).
% 9.09/1.55  fof(f2703,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) | (~spl7_47 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2612,f1454])).
% 9.09/1.55  fof(f2612,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) | ~spl7_47),
% 9.09/1.55    inference(resolution,[],[f607,f84])).
% 9.09/1.55  fof(f607,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl7_47),
% 9.09/1.55    inference(avatar_component_clause,[],[f605])).
% 9.09/1.55  fof(f2702,plain,(
% 9.09/1.55    ~spl7_180 | spl7_104 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2693,f1452,f1390,f2699])).
% 9.09/1.55  fof(f2693,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (spl7_104 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f1392,f1454])).
% 9.09/1.55  fof(f1392,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl7_104),
% 9.09/1.55    inference(avatar_component_clause,[],[f1390])).
% 9.09/1.55  fof(f2697,plain,(
% 9.09/1.55    ~spl7_48 | spl7_104),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2696])).
% 9.09/1.55  fof(f2696,plain,(
% 9.09/1.55    $false | (~spl7_48 | spl7_104)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2692,f612])).
% 9.09/1.55  fof(f2692,plain,(
% 9.09/1.55    ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | spl7_104),
% 9.09/1.55    inference(resolution,[],[f1392,f94])).
% 9.09/1.55  fof(f2695,plain,(
% 9.09/1.55    ~spl7_48 | spl7_104),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2694])).
% 9.09/1.55  fof(f2694,plain,(
% 9.09/1.55    $false | (~spl7_48 | spl7_104)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2691,f612])).
% 9.09/1.55  fof(f2691,plain,(
% 9.09/1.55    ~m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | spl7_104),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1392,f94])).
% 9.09/1.55  fof(f2686,plain,(
% 9.09/1.55    ~spl7_58 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2685])).
% 9.09/1.55  fof(f2685,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2635,f123])).
% 9.09/1.55  fof(f2635,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(superposition,[],[f1194,f748])).
% 9.09/1.55  fof(f1194,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(sK2,sK2) | spl7_95),
% 9.09/1.55    inference(avatar_component_clause,[],[f1192])).
% 9.09/1.55  fof(f1192,plain,(
% 9.09/1.55    spl7_95 <=> k1_xboole_0 = k2_zfmisc_1(sK2,sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).
% 9.09/1.55  fof(f2684,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2683])).
% 9.09/1.55  fof(f2683,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2682,f199])).
% 9.09/1.55  fof(f2682,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2681,f122])).
% 9.09/1.55  fof(f2681,plain,(
% 9.09/1.55    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2619,f748])).
% 9.09/1.55  fof(f2619,plain,(
% 9.09/1.55    ~v1_xboole_0(k2_zfmisc_1(sK2,sK2)) | spl7_95),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1194,f82])).
% 9.09/1.55  fof(f2680,plain,(
% 9.09/1.55    ~spl7_58 | spl7_69 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2679])).
% 9.09/1.55  fof(f2679,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2678,f123])).
% 9.09/1.55  fof(f2678,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)) | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2677,f122])).
% 9.09/1.55  fof(f2677,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_struct_0(sK1)) | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2620,f748])).
% 9.09/1.55  fof(f2620,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_struct_0(sK1)) | (spl7_69 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f1194,f102])).
% 9.09/1.55  fof(f2676,plain,(
% 9.09/1.55    ~spl7_58 | spl7_65 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2675])).
% 9.09/1.55  fof(f2675,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2674,f123])).
% 9.09/1.55  fof(f2674,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_pre_topc(sK0)) | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2673,f122])).
% 9.09/1.55  fof(f2673,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_pre_topc(sK0)) | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2621,f748])).
% 9.09/1.55  fof(f2621,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_pre_topc(sK0)) | (spl7_65 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f1194,f102])).
% 9.09/1.55  fof(f2672,plain,(
% 9.09/1.55    ~spl7_58 | spl7_86 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2671])).
% 9.09/1.55  fof(f2671,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2670,f123])).
% 9.09/1.55  fof(f2670,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,u1_pre_topc(sK1)) | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2669,f122])).
% 9.09/1.55  fof(f2669,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),u1_pre_topc(sK1)) | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2622,f748])).
% 9.09/1.55  fof(f2622,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),u1_pre_topc(sK1)) | (spl7_86 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1071,f1194,f102])).
% 9.09/1.55  fof(f2668,plain,(
% 9.09/1.55    ~spl7_58 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2667])).
% 9.09/1.55  fof(f2667,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2666,f123])).
% 9.09/1.55  fof(f2666,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2665,f122])).
% 9.09/1.55  fof(f2665,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2623,f748])).
% 9.09/1.55  fof(f2623,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(sK2,sK2)) | spl7_95),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1194,f1194,f102])).
% 9.09/1.55  fof(f2664,plain,(
% 9.09/1.55    ~spl7_58 | spl7_69 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2663])).
% 9.09/1.55  fof(f2663,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2662,f122])).
% 9.09/1.55  fof(f2662,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0) | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2661,f122])).
% 9.09/1.55  fof(f2661,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_69 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2625,f748])).
% 9.09/1.55  fof(f2625,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k2_zfmisc_1(sK2,sK2)) | (spl7_69 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f1194,f102])).
% 9.09/1.55  fof(f2660,plain,(
% 9.09/1.55    ~spl7_58 | spl7_65 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2659])).
% 9.09/1.55  fof(f2659,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2658,f122])).
% 9.09/1.55  fof(f2658,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k1_xboole_0) | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2657,f122])).
% 9.09/1.55  fof(f2657,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_65 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2626,f748])).
% 9.09/1.55  fof(f2626,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),k2_zfmisc_1(sK2,sK2)) | (spl7_65 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f1194,f102])).
% 9.09/1.55  fof(f2656,plain,(
% 9.09/1.55    ~spl7_58 | spl7_86 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2655])).
% 9.09/1.55  fof(f2655,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2654,f122])).
% 9.09/1.55  fof(f2654,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k1_xboole_0) | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2653,f122])).
% 9.09/1.55  fof(f2653,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_86 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2627,f748])).
% 9.09/1.55  fof(f2627,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),k2_zfmisc_1(sK2,sK2)) | (spl7_86 | spl7_95)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1071,f1194,f102])).
% 9.09/1.55  fof(f2652,plain,(
% 9.09/1.55    ~spl7_58 | spl7_95),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2651])).
% 9.09/1.55  fof(f2651,plain,(
% 9.09/1.55    $false | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2650,f123])).
% 9.09/1.55  fof(f2650,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2649,f122])).
% 9.09/1.55  fof(f2649,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_58 | spl7_95)),
% 9.09/1.55    inference(forward_demodulation,[],[f2628,f748])).
% 9.09/1.55  fof(f2628,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK2,sK2),k2_zfmisc_1(sK2,sK2)) | spl7_95),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1194,f1194,f102])).
% 9.09/1.55  fof(f2648,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_41 | ~spl7_58 | spl7_95 | spl7_153),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2647])).
% 9.09/1.55  fof(f2647,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_41 | ~spl7_58 | spl7_95 | spl7_153)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2646,f486])).
% 9.09/1.55  fof(f2646,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_14 | ~spl7_41 | ~spl7_58 | spl7_95 | spl7_153)),
% 9.09/1.55    inference(forward_demodulation,[],[f2645,f122])).
% 9.09/1.55  fof(f2645,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (~spl7_14 | ~spl7_41 | ~spl7_58 | spl7_95 | spl7_153)),
% 9.09/1.55    inference(forward_demodulation,[],[f2630,f748])).
% 9.09/1.55  fof(f2630,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k2_zfmisc_1(sK2,sK2)) | (~spl7_14 | ~spl7_41 | spl7_95 | spl7_153)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1194,f125])).
% 9.09/1.55  fof(f2618,plain,(
% 9.09/1.55    spl7_179 | ~spl7_47 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2613,f1452,f605,f2615])).
% 9.09/1.55  fof(f2615,plain,(
% 9.09/1.55    spl7_179 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_179])])).
% 9.09/1.55  fof(f2613,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_47 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f607,f1454])).
% 9.09/1.55  fof(f2607,plain,(
% 9.09/1.55    spl7_178 | ~spl7_44 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2602,f887,f525,f2604])).
% 9.09/1.55  fof(f2604,plain,(
% 9.09/1.55    spl7_178 <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).
% 9.09/1.55  fof(f525,plain,(
% 9.09/1.55    spl7_44 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 9.09/1.55  fof(f2602,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_44 | ~spl7_71)),
% 9.09/1.55    inference(superposition,[],[f527,f889])).
% 9.09/1.55  fof(f527,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_44),
% 9.09/1.55    inference(avatar_component_clause,[],[f525])).
% 9.09/1.55  fof(f2593,plain,(
% 9.09/1.55    ~spl7_174 | spl7_177 | ~spl7_12 | ~spl7_13 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2589,f1452,f192,f187,f2591,f2536])).
% 9.09/1.55  fof(f2536,plain,(
% 9.09/1.55    spl7_174 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).
% 9.09/1.55  fof(f2591,plain,(
% 9.09/1.55    spl7_177 <=> ! [X13,X12] : (~m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).
% 9.09/1.55  fof(f2589,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_12 | ~spl7_13 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2588,f122])).
% 9.09/1.55  fof(f2588,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_12 | ~spl7_13 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2587,f194])).
% 9.09/1.55  fof(f2587,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_12 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2499,f189])).
% 9.09/1.55  fof(f2499,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK0) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | ~spl7_113),
% 9.09/1.55    inference(superposition,[],[f481,f1454])).
% 9.09/1.55  fof(f481,plain,(
% 9.09/1.55    ( ! [X2,X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 9.09/1.55    inference(subsumption_resolution,[],[f480,f85])).
% 9.09/1.55  fof(f480,plain,(
% 9.09/1.55    ( ! [X2,X0,X1] : (v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 9.09/1.55    inference(subsumption_resolution,[],[f479,f85])).
% 9.09/1.55  fof(f479,plain,(
% 9.09/1.55    ( ! [X2,X0,X1] : (v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 9.09/1.55    inference(duplicate_literal_removal,[],[f478])).
% 9.09/1.55  fof(f478,plain,(
% 9.09/1.55    ( ! [X2,X0,X1] : (v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 9.09/1.55    inference(resolution,[],[f130,f127])).
% 9.09/1.55  fof(f127,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(duplicate_literal_removal,[],[f120])).
% 9.09/1.55  fof(f120,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(equality_resolution,[],[f88])).
% 9.09/1.55  fof(f88,plain,(
% 9.09/1.55    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(cnf_transformation,[],[f51])).
% 9.09/1.55  fof(f51,plain,(
% 9.09/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.09/1.55    inference(nnf_transformation,[],[f32])).
% 9.09/1.55  fof(f32,plain,(
% 9.09/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.09/1.55    inference(flattening,[],[f31])).
% 9.09/1.55  fof(f31,plain,(
% 9.09/1.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 9.09/1.55    inference(ennf_transformation,[],[f19])).
% 9.09/1.55  fof(f19,axiom,(
% 9.09/1.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 9.09/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 9.09/1.55  fof(f130,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(duplicate_literal_removal,[],[f117])).
% 9.09/1.55  fof(f117,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(equality_resolution,[],[f87])).
% 9.09/1.55  fof(f87,plain,(
% 9.09/1.55    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(cnf_transformation,[],[f50])).
% 9.09/1.55  fof(f2575,plain,(
% 9.09/1.55    spl7_176 | ~spl7_174 | ~spl7_12 | ~spl7_13 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2570,f1452,f192,f187,f2536,f2572])).
% 9.09/1.55  fof(f2572,plain,(
% 9.09/1.55    spl7_176 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).
% 9.09/1.55  fof(f2570,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_12 | ~spl7_13 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2569,f189])).
% 9.09/1.55  fof(f2569,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | (~spl7_13 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2496,f194])).
% 9.09/1.55  fof(f2496,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))))) | ~spl7_113),
% 9.09/1.55    inference(superposition,[],[f319,f1454])).
% 9.09/1.55  fof(f2551,plain,(
% 9.09/1.55    spl7_173 | ~spl7_12 | ~spl7_13 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2550,f1452,f192,f187,f2523])).
% 9.09/1.55  fof(f2523,plain,(
% 9.09/1.55    spl7_173 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).
% 9.09/1.55  fof(f2550,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_12 | ~spl7_13 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2549,f194])).
% 9.09/1.55  fof(f2549,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl7_12 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2490,f189])).
% 9.09/1.55  fof(f2490,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_113),
% 9.09/1.55    inference(superposition,[],[f85,f1454])).
% 9.09/1.55  fof(f2548,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_113 | spl7_142),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2547])).
% 9.09/1.55  fof(f2547,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_113 | spl7_142)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2489,f651])).
% 9.09/1.55  fof(f651,plain,(
% 9.09/1.55    ( ! [X7] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X7)) ) | ~spl7_14),
% 9.09/1.55    inference(superposition,[],[f110,f571])).
% 9.09/1.55  fof(f2489,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl7_113 | spl7_142)),
% 9.09/1.55    inference(superposition,[],[f1822,f1454])).
% 9.09/1.55  fof(f1822,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | spl7_142),
% 9.09/1.55    inference(avatar_component_clause,[],[f1820])).
% 9.09/1.55  fof(f1820,plain,(
% 9.09/1.55    spl7_142 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).
% 9.09/1.55  fof(f2545,plain,(
% 9.09/1.55    spl7_175 | ~spl7_46 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2487,f1452,f587,f2542])).
% 9.09/1.55  fof(f587,plain,(
% 9.09/1.55    spl7_46 <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 9.09/1.55  fof(f2487,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_46 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f589,f1454])).
% 9.09/1.55  fof(f589,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_46),
% 9.09/1.55    inference(avatar_component_clause,[],[f587])).
% 9.09/1.55  fof(f2539,plain,(
% 9.09/1.55    spl7_174 | ~spl7_37 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2485,f1452,f460,f2536])).
% 9.09/1.55  fof(f460,plain,(
% 9.09/1.55    spl7_37 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 9.09/1.55  fof(f2485,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_37 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f461,f1454])).
% 9.09/1.55  fof(f461,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_37),
% 9.09/1.55    inference(avatar_component_clause,[],[f460])).
% 9.09/1.55  fof(f2526,plain,(
% 9.09/1.55    spl7_173 | ~spl7_25 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2480,f1452,f321,f2523])).
% 9.09/1.55  fof(f321,plain,(
% 9.09/1.55    spl7_25 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 9.09/1.55  fof(f2480,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_25 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f323,f1454])).
% 9.09/1.55  fof(f323,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_25),
% 9.09/1.55    inference(avatar_component_clause,[],[f321])).
% 9.09/1.55  fof(f2521,plain,(
% 9.09/1.55    spl7_172 | ~spl7_23 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2479,f1452,f304,f2518])).
% 9.09/1.55  fof(f2518,plain,(
% 9.09/1.55    spl7_172 <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).
% 9.09/1.55  fof(f304,plain,(
% 9.09/1.55    spl7_23 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 9.09/1.55  fof(f2479,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_23 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f306,f1454])).
% 9.09/1.55  fof(f306,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_23),
% 9.09/1.55    inference(avatar_component_clause,[],[f304])).
% 9.09/1.55  fof(f2515,plain,(
% 9.09/1.55    spl7_171 | ~spl7_19 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2477,f1452,f257,f2512])).
% 9.09/1.55  fof(f2512,plain,(
% 9.09/1.55    spl7_171 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).
% 9.09/1.55  fof(f257,plain,(
% 9.09/1.55    spl7_19 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 9.09/1.55  fof(f2477,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_19 | ~spl7_113)),
% 9.09/1.55    inference(superposition,[],[f259,f1454])).
% 9.09/1.55  fof(f259,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl7_19),
% 9.09/1.55    inference(avatar_component_clause,[],[f257])).
% 9.09/1.55  fof(f2470,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2469])).
% 9.09/1.55  fof(f2469,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2412,f212])).
% 9.09/1.55  fof(f2412,plain,(
% 9.09/1.55    r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0) | (~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(superposition,[],[f1086,f748])).
% 9.09/1.55  fof(f1086,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2) | ~spl7_88),
% 9.09/1.55    inference(avatar_component_clause,[],[f1084])).
% 9.09/1.55  fof(f1084,plain,(
% 9.09/1.55    spl7_88 <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 9.09/1.55  fof(f2468,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_71 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2467])).
% 9.09/1.55  fof(f2467,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2466,f212])).
% 9.09/1.55  fof(f2466,plain,(
% 9.09/1.55    r2_hidden(sK5(k1_xboole_0,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k1_xboole_0) | (~spl7_58 | ~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2411,f748])).
% 9.09/1.55  fof(f2411,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),sK2) | (~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(superposition,[],[f1086,f889])).
% 9.09/1.55  fof(f2465,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2464])).
% 9.09/1.55  fof(f2464,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2463,f199])).
% 9.09/1.55  fof(f2463,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2410,f748])).
% 9.09/1.55  fof(f2410,plain,(
% 9.09/1.55    ~v1_xboole_0(sK2) | ~spl7_88),
% 9.09/1.55    inference(resolution,[],[f1086,f90])).
% 9.09/1.55  fof(f2457,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2456])).
% 9.09/1.55  fof(f2456,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2455,f230])).
% 9.09/1.55  fof(f2455,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2408,f748])).
% 9.09/1.55  fof(f2408,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(resolution,[],[f1086,f298])).
% 9.09/1.55  fof(f2454,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2453])).
% 9.09/1.55  fof(f2453,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2452,f230])).
% 9.09/1.55  fof(f2452,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2392,f748])).
% 9.09/1.55  fof(f2392,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1086,f298])).
% 9.09/1.55  fof(f2451,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2450])).
% 9.09/1.55  fof(f2450,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2449,f230])).
% 9.09/1.55  fof(f2449,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2393,f748])).
% 9.09/1.55  fof(f2393,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f199,f1086,f116])).
% 9.09/1.55  fof(f2448,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2447])).
% 9.09/1.55  fof(f2447,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2446,f230])).
% 9.09/1.55  fof(f2446,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2445,f748])).
% 9.09/1.55  fof(f2445,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2394,f348])).
% 9.09/1.55  fof(f2394,plain,(
% 9.09/1.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(sK6(X0,k1_xboole_0)))) ) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f332,f1086,f116])).
% 9.09/1.55  fof(f2444,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2443])).
% 9.09/1.55  fof(f2443,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2442,f230])).
% 9.09/1.55  fof(f2442,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2441,f748])).
% 9.09/1.55  fof(f2441,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2395,f571])).
% 9.09/1.55  fof(f2395,plain,(
% 9.09/1.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(sK6(k1_xboole_0,X0)))) ) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f558,f1086,f116])).
% 9.09/1.55  fof(f2440,plain,(
% 9.09/1.55    ~spl7_170 | ~spl7_39 | ~spl7_88 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2435,f1452,f1084,f468,f2437])).
% 9.09/1.55  fof(f2437,plain,(
% 9.09/1.55    spl7_170 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).
% 9.09/1.55  fof(f468,plain,(
% 9.09/1.55    spl7_39 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 9.09/1.55  fof(f2435,plain,(
% 9.09/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))) | (~spl7_39 | ~spl7_88 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2398,f1454])).
% 9.09/1.55  fof(f2398,plain,(
% 9.09/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | (~spl7_39 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f469,f1086,f116])).
% 9.09/1.55  fof(f469,plain,(
% 9.09/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl7_39),
% 9.09/1.55    inference(avatar_component_clause,[],[f468])).
% 9.09/1.55  fof(f2434,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2433])).
% 9.09/1.55  fof(f2433,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2432,f199])).
% 9.09/1.55  fof(f2432,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2399,f748])).
% 9.09/1.55  fof(f2399,plain,(
% 9.09/1.55    ~v1_xboole_0(sK2) | ~spl7_88),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f201,f1086,f116])).
% 9.09/1.55  fof(f2431,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_64 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2430])).
% 9.09/1.55  fof(f2430,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_64 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2401,f212])).
% 9.09/1.55  fof(f2401,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0) | (~spl7_64 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f801,f1086,f97])).
% 9.09/1.55  fof(f801,plain,(
% 9.09/1.55    r1_tarski(sK2,k1_xboole_0) | ~spl7_64),
% 9.09/1.55    inference(avatar_component_clause,[],[f800])).
% 9.09/1.55  fof(f800,plain,(
% 9.09/1.55    spl7_64 <=> r1_tarski(sK2,k1_xboole_0)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 9.09/1.55  fof(f2429,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_16 | ~spl7_88 | ~spl7_113),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2428])).
% 9.09/1.55  fof(f2428,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_16 | ~spl7_88 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2427,f212])).
% 9.09/1.55  fof(f2427,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k1_xboole_0) | (~spl7_16 | ~spl7_88 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2426,f123])).
% 9.09/1.55  fof(f2426,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_16 | ~spl7_88 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2402,f1454])).
% 9.09/1.55  fof(f2402,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl7_16 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f223,f1086,f97])).
% 9.09/1.55  fof(f223,plain,(
% 9.09/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl7_16),
% 9.09/1.55    inference(avatar_component_clause,[],[f221])).
% 9.09/1.55  fof(f221,plain,(
% 9.09/1.55    spl7_16 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 9.09/1.55  fof(f2425,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_29 | ~spl7_71 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2424])).
% 9.09/1.55  fof(f2424,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_29 | ~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2423,f212])).
% 9.09/1.55  fof(f2423,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k1_xboole_0) | (~spl7_29 | ~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2422,f122])).
% 9.09/1.55  fof(f2422,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) | (~spl7_29 | ~spl7_71 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2403,f889])).
% 9.09/1.55  fof(f2403,plain,(
% 9.09/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_29 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f387,f1086,f97])).
% 9.09/1.55  fof(f387,plain,(
% 9.09/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_29),
% 9.09/1.55    inference(avatar_component_clause,[],[f385])).
% 9.09/1.55  fof(f385,plain,(
% 9.09/1.55    spl7_29 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 9.09/1.55  fof(f2421,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_64 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2420])).
% 9.09/1.55  fof(f2420,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_64 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2404,f801])).
% 9.09/1.55  fof(f2404,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k1_xboole_0) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f212,f1086,f97])).
% 9.09/1.55  fof(f2419,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_64 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2418])).
% 9.09/1.55  fof(f2418,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_64 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2417,f801])).
% 9.09/1.55  fof(f2417,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k1_xboole_0) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2406,f571])).
% 9.09/1.55  fof(f2406,plain,(
% 9.09/1.55    ( ! [X0] : (~r1_tarski(sK2,sK6(k1_xboole_0,X0))) ) | (~spl7_14 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f551,f1086,f97])).
% 9.09/1.55  fof(f2416,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2415])).
% 9.09/1.55  fof(f2415,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2414,f199])).
% 9.09/1.55  fof(f2414,plain,(
% 9.09/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_58 | ~spl7_88)),
% 9.09/1.55    inference(forward_demodulation,[],[f2407,f748])).
% 9.09/1.55  fof(f2407,plain,(
% 9.09/1.55    ~v1_xboole_0(sK2) | ~spl7_88),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1086,f90])).
% 9.09/1.55  fof(f2413,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_64 | ~spl7_88),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2405])).
% 9.09/1.55  fof(f2405,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_64 | ~spl7_88)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f801,f212,f1086,f97])).
% 9.09/1.55  fof(f2350,plain,(
% 9.09/1.55    ~spl7_168 | spl7_169 | ~spl7_26 | ~spl7_33 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2346,f887,f425,f326,f2348,f2329])).
% 9.09/1.55  fof(f2348,plain,(
% 9.09/1.55    spl7_169 <=> ! [X16,X15] : (~m1_subset_1(X15,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X16) | ~l1_pre_topc(X16) | ~v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0) | ~v1_funct_1(X15) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).
% 9.09/1.55  fof(f326,plain,(
% 9.09/1.55    spl7_26 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 9.09/1.55  fof(f425,plain,(
% 9.09/1.55    spl7_33 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 9.09/1.55  fof(f2346,plain,(
% 9.09/1.55    ( ! [X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(X15) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))) | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) ) | (~spl7_26 | ~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2345,f122])).
% 9.09/1.55  fof(f2345,plain,(
% 9.09/1.55    ( ! [X15,X16] : (~v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(X15) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))) | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) ) | (~spl7_26 | ~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2344,f328])).
% 9.09/1.55  fof(f328,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_26),
% 9.09/1.55    inference(avatar_component_clause,[],[f326])).
% 9.09/1.55  fof(f2344,plain,(
% 9.09/1.55    ( ! [X15,X16] : (~v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(X15) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))) | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) ) | (~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2269,f426])).
% 9.09/1.55  fof(f426,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_33),
% 9.09/1.55    inference(avatar_component_clause,[],[f425])).
% 9.09/1.55  fof(f2269,plain,(
% 9.09/1.55    ( ! [X15,X16] : (~v5_pre_topc(X15,X16,g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_1(X15) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0))) | ~v1_funct_2(X15,u1_struct_0(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16))) | v5_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))))) | ~v1_funct_2(X15,u1_struct_0(X16),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(X16) | ~v2_pre_topc(X16)) ) | ~spl7_71),
% 9.09/1.55    inference(superposition,[],[f481,f889])).
% 9.09/1.55  fof(f2332,plain,(
% 9.09/1.55    spl7_167 | ~spl7_168 | ~spl7_26 | ~spl7_33 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2323,f887,f425,f326,f2329,f2325])).
% 9.09/1.55  fof(f2323,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_26 | ~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2322,f426])).
% 9.09/1.55  fof(f2322,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | (~spl7_26 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2266,f328])).
% 9.09/1.55  fof(f2266,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))) | ~spl7_71),
% 9.09/1.55    inference(superposition,[],[f319,f889])).
% 9.09/1.55  fof(f2304,plain,(
% 9.09/1.55    spl7_166 | ~spl7_26 | ~spl7_33 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2299,f887,f425,f326,f2301])).
% 9.09/1.55  fof(f2299,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_26 | ~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2298,f328])).
% 9.09/1.55  fof(f2298,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_33 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2260,f426])).
% 9.09/1.55  fof(f2260,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_71),
% 9.09/1.55    inference(superposition,[],[f85,f889])).
% 9.09/1.55  fof(f2297,plain,(
% 9.09/1.55    spl7_165 | ~spl7_20 | ~spl7_71),
% 9.09/1.55    inference(avatar_split_clause,[],[f2292,f887,f262,f2294])).
% 9.09/1.55  fof(f2294,plain,(
% 9.09/1.55    spl7_165 <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).
% 9.09/1.55  fof(f262,plain,(
% 9.09/1.55    spl7_20 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 9.09/1.55  fof(f2292,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_20 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2259,f264])).
% 9.09/1.55  fof(f264,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl7_20),
% 9.09/1.55    inference(avatar_component_clause,[],[f262])).
% 9.09/1.55  fof(f2259,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl7_71),
% 9.09/1.55    inference(superposition,[],[f272,f889])).
% 9.09/1.55  fof(f2249,plain,(
% 9.09/1.55    ~spl7_164 | ~spl7_14 | ~spl7_41 | spl7_86 | spl7_153),
% 9.09/1.55    inference(avatar_split_clause,[],[f2207,f2040,f1070,f493,f197,f2246])).
% 9.09/1.55  fof(f2246,plain,(
% 9.09/1.55    spl7_164 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).
% 9.09/1.55  fof(f2207,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK1)) | (~spl7_14 | ~spl7_41 | spl7_86 | spl7_153)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f2042,f495,f230,f1071,f125])).
% 9.09/1.55  fof(f2244,plain,(
% 9.09/1.55    ~spl7_163 | spl7_69 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2210,f1070,f875,f2241])).
% 9.09/1.55  fof(f2241,plain,(
% 9.09/1.55    spl7_163 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).
% 9.09/1.55  fof(f2210,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK1)) | (spl7_69 | spl7_86)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f1071,f102])).
% 9.09/1.55  fof(f2239,plain,(
% 9.09/1.55    ~spl7_162 | spl7_65 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2211,f1070,f824,f2236])).
% 9.09/1.55  fof(f2236,plain,(
% 9.09/1.55    spl7_162 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).
% 9.09/1.55  fof(f2211,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK1)) | (spl7_65 | spl7_86)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f1071,f102])).
% 9.09/1.55  fof(f2234,plain,(
% 9.09/1.55    ~spl7_159 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2212,f1070,f2220])).
% 9.09/1.55  fof(f2220,plain,(
% 9.09/1.55    spl7_159 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).
% 9.09/1.55  fof(f2212,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1)) | spl7_86),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1071,f1071,f102])).
% 9.09/1.55  fof(f2233,plain,(
% 9.09/1.55    ~spl7_161 | spl7_69 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2214,f1070,f875,f2230])).
% 9.09/1.55  fof(f2230,plain,(
% 9.09/1.55    spl7_161 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).
% 9.09/1.55  fof(f2214,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_struct_0(sK1)) | (spl7_69 | spl7_86)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f1071,f102])).
% 9.09/1.55  fof(f2228,plain,(
% 9.09/1.55    ~spl7_160 | spl7_65 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2215,f1070,f824,f2225])).
% 9.09/1.55  fof(f2225,plain,(
% 9.09/1.55    spl7_160 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).
% 9.09/1.55  fof(f2215,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK0)) | (spl7_65 | spl7_86)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f1071,f102])).
% 9.09/1.55  fof(f2223,plain,(
% 9.09/1.55    ~spl7_159 | spl7_86),
% 9.09/1.55    inference(avatar_split_clause,[],[f2216,f1070,f2220])).
% 9.09/1.55  fof(f2216,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK1),u1_pre_topc(sK1)) | spl7_86),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f1071,f1071,f102])).
% 9.09/1.55  fof(f2205,plain,(
% 9.09/1.55    ~spl7_158 | ~spl7_14 | ~spl7_41 | spl7_65 | spl7_153),
% 9.09/1.55    inference(avatar_split_clause,[],[f2199,f2040,f824,f493,f197,f2202])).
% 9.09/1.55  fof(f2202,plain,(
% 9.09/1.55    spl7_158 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).
% 9.09/1.55  fof(f2199,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_pre_topc(sK0)) | (~spl7_14 | ~spl7_41 | spl7_65 | spl7_153)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f495,f825,f230,f2042,f125])).
% 9.09/1.55  fof(f2174,plain,(
% 9.09/1.55    ~spl7_157 | spl7_65 | spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f2152,f875,f824,f2171])).
% 9.09/1.55  fof(f2171,plain,(
% 9.09/1.55    spl7_157 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).
% 9.09/1.55  fof(f2152,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl7_65 | spl7_69)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f825,f102])).
% 9.09/1.55  fof(f2169,plain,(
% 9.09/1.55    ~spl7_155 | spl7_65),
% 9.09/1.55    inference(avatar_split_clause,[],[f2153,f824,f2160])).
% 9.09/1.55  fof(f2160,plain,(
% 9.09/1.55    spl7_155 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_155])])).
% 9.09/1.55  fof(f2153,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0)) | spl7_65),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f825,f102])).
% 9.09/1.55  fof(f2168,plain,(
% 9.09/1.55    ~spl7_156 | spl7_65 | spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f2155,f875,f824,f2165])).
% 9.09/1.55  fof(f2165,plain,(
% 9.09/1.55    spl7_156 <=> k1_xboole_0 = k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).
% 9.09/1.55  fof(f2155,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_struct_0(sK1)) | (spl7_65 | spl7_69)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f825,f102])).
% 9.09/1.55  fof(f2163,plain,(
% 9.09/1.55    ~spl7_155 | spl7_65),
% 9.09/1.55    inference(avatar_split_clause,[],[f2156,f824,f2160])).
% 9.09/1.55  fof(f2156,plain,(
% 9.09/1.55    k1_xboole_0 != k2_zfmisc_1(u1_pre_topc(sK0),u1_pre_topc(sK0)) | spl7_65),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f825,f825,f102])).
% 9.09/1.55  fof(f2114,plain,(
% 9.09/1.55    ~spl7_154 | spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2113,f1452,f746,f142,f136,f2100])).
% 9.09/1.55  fof(f2100,plain,(
% 9.09/1.55    spl7_154 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).
% 9.09/1.55  fof(f136,plain,(
% 9.09/1.55    spl7_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 9.09/1.55  fof(f142,plain,(
% 9.09/1.55    spl7_3 <=> sK2 = sK3),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 9.09/1.55  fof(f2113,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2112,f748])).
% 9.09/1.55  fof(f2112,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2111,f144])).
% 9.09/1.55  fof(f144,plain,(
% 9.09/1.55    sK2 = sK3 | ~spl7_3),
% 9.09/1.55    inference(avatar_component_clause,[],[f142])).
% 9.09/1.55  fof(f2111,plain,(
% 9.09/1.55    ~v5_pre_topc(sK3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f138,f1454])).
% 9.09/1.55  fof(f138,plain,(
% 9.09/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_2),
% 9.09/1.55    inference(avatar_component_clause,[],[f136])).
% 9.09/1.55  fof(f2110,plain,(
% 9.09/1.55    ~spl7_154 | spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2109,f1452,f746,f142,f136,f2100])).
% 9.09/1.55  fof(f2109,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2108,f748])).
% 9.09/1.55  fof(f2108,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f203,f1454])).
% 9.09/1.55  fof(f203,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3)),
% 9.09/1.55    inference(forward_demodulation,[],[f138,f144])).
% 9.09/1.55  fof(f2107,plain,(
% 9.09/1.55    ~spl7_154 | spl7_15 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2106,f1452,f746,f205,f2100])).
% 9.09/1.55  fof(f205,plain,(
% 9.09/1.55    spl7_15 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 9.09/1.55  fof(f2106,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_15 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2105,f748])).
% 9.09/1.55  fof(f2105,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_15 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f207,f1454])).
% 9.09/1.55  fof(f207,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_15),
% 9.09/1.55    inference(avatar_component_clause,[],[f205])).
% 9.09/1.55  fof(f2103,plain,(
% 9.09/1.55    ~spl7_154 | spl7_82 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2098,f1452,f966,f2100])).
% 9.09/1.55  fof(f966,plain,(
% 9.09/1.55    spl7_82 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 9.09/1.55  fof(f2098,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_82 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f967,f1454])).
% 9.09/1.55  fof(f967,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_82),
% 9.09/1.55    inference(avatar_component_clause,[],[f966])).
% 9.09/1.55  fof(f2084,plain,(
% 9.09/1.55    ~spl7_14 | ~spl7_58 | ~spl7_71 | ~spl7_114 | spl7_128),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2083])).
% 9.09/1.55  fof(f2083,plain,(
% 9.09/1.55    $false | (~spl7_14 | ~spl7_58 | ~spl7_71 | ~spl7_114 | spl7_128)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2082,f651])).
% 9.09/1.55  fof(f2082,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl7_58 | ~spl7_71 | ~spl7_114 | spl7_128)),
% 9.09/1.55    inference(forward_demodulation,[],[f2081,f748])).
% 9.09/1.55  fof(f2081,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_71 | ~spl7_114 | spl7_128)),
% 9.09/1.55    inference(forward_demodulation,[],[f2080,f1466])).
% 9.09/1.55  fof(f2080,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl7_71 | spl7_128)),
% 9.09/1.55    inference(forward_demodulation,[],[f1638,f889])).
% 9.09/1.55  fof(f1638,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl7_128),
% 9.09/1.55    inference(avatar_component_clause,[],[f1636])).
% 9.09/1.55  fof(f1636,plain,(
% 9.09/1.55    spl7_128 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).
% 9.09/1.55  fof(f2078,plain,(
% 9.09/1.55    ~spl7_14 | spl7_35 | ~spl7_58 | ~spl7_71),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2077])).
% 9.09/1.55  fof(f2077,plain,(
% 9.09/1.55    $false | (~spl7_14 | spl7_35 | ~spl7_58 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2076,f230])).
% 9.09/1.55  fof(f2076,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl7_35 | ~spl7_58 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2075,f748])).
% 9.09/1.55  fof(f2075,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl7_35 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2074,f122])).
% 9.09/1.55  fof(f2074,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (spl7_35 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f435,f889])).
% 9.09/1.55  fof(f435,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl7_35),
% 9.09/1.55    inference(avatar_component_clause,[],[f433])).
% 9.09/1.55  fof(f433,plain,(
% 9.09/1.55    spl7_35 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 9.09/1.55  fof(f2073,plain,(
% 9.09/1.55    spl7_35 | ~spl7_64 | ~spl7_71),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2072])).
% 9.09/1.55  fof(f2072,plain,(
% 9.09/1.55    $false | (spl7_35 | ~spl7_64 | ~spl7_71)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2071,f801])).
% 9.09/1.55  fof(f2071,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k1_xboole_0) | (spl7_35 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f2070,f122])).
% 9.09/1.55  fof(f2070,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | (spl7_35 | ~spl7_71)),
% 9.09/1.55    inference(forward_demodulation,[],[f1076,f889])).
% 9.09/1.55  fof(f1076,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl7_35),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f435,f101])).
% 9.09/1.55  fof(f2069,plain,(
% 9.09/1.55    ~spl7_152 | spl7_38 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2068,f1452,f746,f464,f2027])).
% 9.09/1.55  fof(f2027,plain,(
% 9.09/1.55    spl7_152 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).
% 9.09/1.55  fof(f464,plain,(
% 9.09/1.55    spl7_38 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 9.09/1.55  fof(f2068,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (spl7_38 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2067,f748])).
% 9.09/1.55  fof(f2067,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (spl7_38 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f466,f1454])).
% 9.09/1.55  fof(f466,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl7_38),
% 9.09/1.55    inference(avatar_component_clause,[],[f464])).
% 9.09/1.55  fof(f2066,plain,(
% 9.09/1.55    ~spl7_150 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2065,f1452,f746,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f2011])).
% 9.09/1.55  fof(f2011,plain,(
% 9.09/1.55    spl7_150 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).
% 9.09/1.55  fof(f172,plain,(
% 9.09/1.55    spl7_9 <=> v1_funct_1(sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 9.09/1.55  fof(f373,plain,(
% 9.09/1.55    spl7_28 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 9.09/1.55  fof(f405,plain,(
% 9.09/1.55    spl7_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 9.09/1.55  fof(f2065,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2064,f748])).
% 9.09/1.55  fof(f2064,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1050,f1454])).
% 9.09/1.55  fof(f1050,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1049,f323])).
% 9.09/1.55  fof(f1049,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1048,f461])).
% 9.09/1.55  fof(f1048,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1047,f184])).
% 9.09/1.55  fof(f1047,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1046,f179])).
% 9.09/1.55  fof(f1046,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1045,f469])).
% 9.09/1.55  fof(f1045,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1044,f174])).
% 9.09/1.55  fof(f174,plain,(
% 9.09/1.55    v1_funct_1(sK2) | ~spl7_9),
% 9.09/1.55    inference(avatar_component_clause,[],[f172])).
% 9.09/1.55  fof(f1044,plain,(
% 9.09/1.55    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1043,f375])).
% 9.09/1.55  fof(f375,plain,(
% 9.09/1.55    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_28),
% 9.09/1.55    inference(avatar_component_clause,[],[f373])).
% 9.09/1.55  fof(f1043,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_15 | ~spl7_32 | spl7_38)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1042,f407])).
% 9.09/1.55  fof(f407,plain,(
% 9.09/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_32),
% 9.09/1.55    inference(avatar_component_clause,[],[f405])).
% 9.09/1.55  fof(f1042,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_15 | spl7_38)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1032,f466])).
% 9.09/1.55  fof(f1032,plain,(
% 9.09/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_15),
% 9.09/1.55    inference(resolution,[],[f206,f130])).
% 9.09/1.55  fof(f206,plain,(
% 9.09/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_15),
% 9.09/1.55    inference(avatar_component_clause,[],[f205])).
% 9.09/1.55  fof(f2063,plain,(
% 9.09/1.55    ~spl7_152 | spl7_38 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2062,f1452,f746,f464,f2027])).
% 9.09/1.55  fof(f2062,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (spl7_38 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1289,f1454])).
% 9.09/1.55  fof(f1289,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl7_38 | ~spl7_58)),
% 9.09/1.55    inference(superposition,[],[f466,f748])).
% 9.09/1.55  fof(f2061,plain,(
% 9.09/1.55    ~spl7_150 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2060,f1452,f746,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f2011])).
% 9.09/1.55  fof(f2060,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2059,f748])).
% 9.09/1.55  fof(f2059,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2058,f1454])).
% 9.09/1.55  fof(f2058,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1049,f323])).
% 9.09/1.55  fof(f2057,plain,(
% 9.09/1.55    ~spl7_150 | spl7_40 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2056,f1452,f746,f472,f2011])).
% 9.09/1.55  fof(f472,plain,(
% 9.09/1.55    spl7_40 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 9.09/1.55  fof(f2056,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_40 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2055,f748])).
% 9.09/1.55  fof(f2055,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_40 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f474,f1454])).
% 9.09/1.55  fof(f474,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl7_40),
% 9.09/1.55    inference(avatar_component_clause,[],[f472])).
% 9.09/1.55  fof(f2054,plain,(
% 9.09/1.55    ~spl7_150 | spl7_40 | ~spl7_58 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2053,f1452,f746,f472,f2011])).
% 9.09/1.55  fof(f2053,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_40 | ~spl7_58 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1300,f1454])).
% 9.09/1.55  fof(f1300,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_40 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f474,f748])).
% 9.09/1.55  fof(f2052,plain,(
% 9.09/1.55    ~spl7_62 | spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1431,f875,f781])).
% 9.09/1.55  fof(f781,plain,(
% 9.09/1.55    spl7_62 <=> v1_xboole_0(u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 9.09/1.55  fof(f1431,plain,(
% 9.09/1.55    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_69),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f876,f82])).
% 9.09/1.55  fof(f2043,plain,(
% 9.09/1.55    ~spl7_153 | ~spl7_58 | spl7_77 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2038,f1452,f917,f746,f2040])).
% 9.09/1.55  fof(f917,plain,(
% 9.09/1.55    spl7_77 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 9.09/1.55  fof(f2038,plain,(
% 9.09/1.55    ~v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (~spl7_58 | spl7_77 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2037,f748])).
% 9.09/1.55  fof(f2037,plain,(
% 9.09/1.55    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))) | (spl7_77 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f918,f1454])).
% 9.09/1.55  fof(f918,plain,(
% 9.09/1.55    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | spl7_77),
% 9.09/1.55    inference(avatar_component_clause,[],[f917])).
% 9.09/1.55  fof(f2036,plain,(
% 9.09/1.55    ~spl7_150 | spl7_84 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2035,f1452,f981,f2011])).
% 9.09/1.55  fof(f981,plain,(
% 9.09/1.55    spl7_84 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 9.09/1.55  fof(f2035,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl7_84 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f983,f1454])).
% 9.09/1.55  fof(f983,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl7_84),
% 9.09/1.55    inference(avatar_component_clause,[],[f981])).
% 9.09/1.55  fof(f2034,plain,(
% 9.09/1.55    ~spl7_64 | spl7_87 | ~spl7_113),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f2033])).
% 9.09/1.55  fof(f2033,plain,(
% 9.09/1.55    $false | (~spl7_64 | spl7_87 | ~spl7_113)),
% 9.09/1.55    inference(subsumption_resolution,[],[f2032,f801])).
% 9.09/1.55  fof(f2032,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k1_xboole_0) | (spl7_87 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f2031,f123])).
% 9.09/1.55  fof(f2031,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (spl7_87 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1081,f1454])).
% 9.09/1.55  fof(f1081,plain,(
% 9.09/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl7_87),
% 9.09/1.55    inference(avatar_component_clause,[],[f1079])).
% 9.09/1.55  fof(f1079,plain,(
% 9.09/1.55    spl7_87 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).
% 9.09/1.55  fof(f2030,plain,(
% 9.09/1.55    ~spl7_152 | spl7_101 | ~spl7_113),
% 9.09/1.55    inference(avatar_split_clause,[],[f2025,f1452,f1267,f2027])).
% 9.09/1.55  fof(f1267,plain,(
% 9.09/1.55    spl7_101 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).
% 9.09/1.55  fof(f2025,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (spl7_101 | ~spl7_113)),
% 9.09/1.55    inference(forward_demodulation,[],[f1268,f1454])).
% 9.09/1.55  fof(f1268,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl7_101),
% 9.09/1.55    inference(avatar_component_clause,[],[f1267])).
% 9.09/1.55  fof(f2024,plain,(
% 9.09/1.55    spl7_113 | ~spl7_114 | ~spl7_122),
% 9.09/1.55    inference(avatar_split_clause,[],[f2023,f1553,f1464,f1452])).
% 9.09/1.55  fof(f1553,plain,(
% 9.09/1.55    spl7_122 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).
% 9.09/1.55  fof(f2023,plain,(
% 9.09/1.55    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_114 | ~spl7_122)),
% 9.09/1.55    inference(forward_demodulation,[],[f1555,f1466])).
% 9.09/1.55  fof(f1555,plain,(
% 9.09/1.55    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl7_122),
% 9.09/1.55    inference(avatar_component_clause,[],[f1553])).
% 9.09/1.55  fof(f2020,plain,(
% 9.09/1.55    ~spl7_151 | ~spl7_114 | spl7_127),
% 9.09/1.55    inference(avatar_split_clause,[],[f2015,f1618,f1464,f2017])).
% 9.09/1.55  fof(f1618,plain,(
% 9.09/1.55    spl7_127 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).
% 9.09/1.55  fof(f2015,plain,(
% 9.09/1.55    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl7_114 | spl7_127)),
% 9.09/1.55    inference(forward_demodulation,[],[f1619,f1466])).
% 9.09/1.55  fof(f1619,plain,(
% 9.09/1.55    k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | spl7_127),
% 9.09/1.55    inference(avatar_component_clause,[],[f1618])).
% 9.09/1.55  fof(f2014,plain,(
% 9.09/1.55    ~spl7_150 | ~spl7_58 | ~spl7_114 | spl7_131),
% 9.09/1.55    inference(avatar_split_clause,[],[f2009,f1659,f1464,f746,f2011])).
% 9.09/1.55  fof(f1659,plain,(
% 9.09/1.55    spl7_131 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_131])])).
% 9.09/1.55  fof(f2009,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_58 | ~spl7_114 | spl7_131)),
% 9.09/1.55    inference(forward_demodulation,[],[f2008,f748])).
% 9.09/1.55  fof(f2008,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_114 | spl7_131)),
% 9.09/1.55    inference(forward_demodulation,[],[f1661,f1466])).
% 9.09/1.55  fof(f1661,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl7_131),
% 9.09/1.55    inference(avatar_component_clause,[],[f1659])).
% 9.09/1.55  fof(f2007,plain,(
% 9.09/1.55    ~spl7_141 | ~spl7_114 | spl7_140),
% 9.09/1.55    inference(avatar_split_clause,[],[f2006,f1766,f1464,f1797])).
% 9.09/1.55  fof(f1797,plain,(
% 9.09/1.55    spl7_141 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).
% 9.09/1.55  fof(f1766,plain,(
% 9.09/1.55    spl7_140 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).
% 9.09/1.55  fof(f2006,plain,(
% 9.09/1.55    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_114 | spl7_140)),
% 9.09/1.55    inference(forward_demodulation,[],[f1767,f1466])).
% 9.09/1.55  fof(f1767,plain,(
% 9.09/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(sK2) | spl7_140),
% 9.09/1.55    inference(avatar_component_clause,[],[f1766])).
% 9.09/1.55  fof(f2005,plain,(
% 9.09/1.55    spl7_69 | spl7_70 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).
% 9.09/1.55  fof(f879,plain,(
% 9.09/1.55    spl7_70 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 9.09/1.55  fof(f157,plain,(
% 9.09/1.55    spl7_6 <=> v1_funct_1(sK3)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 9.09/1.55  fof(f162,plain,(
% 9.09/1.55    spl7_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 9.09/1.55  fof(f167,plain,(
% 9.09/1.55    spl7_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 9.09/1.55  fof(f873,plain,(
% 9.09/1.55    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | (~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f872,f748])).
% 9.09/1.55  fof(f872,plain,(
% 9.09/1.55    v1_partfun1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | (~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 9.09/1.55    inference(subsumption_resolution,[],[f870,f164])).
% 9.09/1.55  fof(f164,plain,(
% 9.09/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl7_7),
% 9.09/1.55    inference(avatar_component_clause,[],[f162])).
% 9.09/1.55  fof(f870,plain,(
% 9.09/1.55    v1_partfun1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = u1_struct_0(sK1) | (~spl7_3 | ~spl7_6 | ~spl7_8)),
% 9.09/1.55    inference(resolution,[],[f414,f169])).
% 9.09/1.55  fof(f169,plain,(
% 9.09/1.55    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl7_8),
% 9.09/1.55    inference(avatar_component_clause,[],[f167])).
% 9.09/1.55  fof(f414,plain,(
% 9.09/1.55    ( ! [X0,X1] : (~v1_funct_2(sK2,X1,X0) | v1_partfun1(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0) ) | (~spl7_3 | ~spl7_6)),
% 9.09/1.55    inference(forward_demodulation,[],[f413,f144])).
% 9.09/1.55  fof(f413,plain,(
% 9.09/1.55    ( ! [X0,X1] : (~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | v1_partfun1(sK3,X1)) ) | (~spl7_3 | ~spl7_6)),
% 9.09/1.55    inference(forward_demodulation,[],[f412,f144])).
% 9.09/1.55  fof(f412,plain,(
% 9.09/1.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | ~v1_funct_2(sK3,X1,X0) | v1_partfun1(sK3,X1)) ) | (~spl7_3 | ~spl7_6)),
% 9.09/1.55    inference(forward_demodulation,[],[f409,f144])).
% 9.09/1.55  fof(f409,plain,(
% 9.09/1.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0) | v1_partfun1(sK3,X1)) ) | ~spl7_6),
% 9.09/1.55    inference(resolution,[],[f125,f159])).
% 9.09/1.55  fof(f159,plain,(
% 9.09/1.55    v1_funct_1(sK3) | ~spl7_6),
% 9.09/1.55    inference(avatar_component_clause,[],[f157])).
% 9.09/1.55  fof(f2003,plain,(
% 9.09/1.55    spl7_82 | ~spl7_15 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f1275,f746,f205,f966])).
% 9.09/1.55  fof(f1275,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_15 | ~spl7_58)),
% 9.09/1.55    inference(superposition,[],[f206,f748])).
% 9.09/1.55  fof(f2002,plain,(
% 9.09/1.55    spl7_82 | ~spl7_15 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f2001,f746,f205,f966])).
% 9.09/1.55  fof(f2001,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_15 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f206,f748])).
% 9.09/1.55  fof(f2000,plain,(
% 9.09/1.55    spl7_82 | ~spl7_2 | ~spl7_3 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f964,f746,f142,f136,f966])).
% 9.09/1.55  fof(f964,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f963,f748])).
% 9.09/1.55  fof(f963,plain,(
% 9.09/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3)),
% 9.09/1.55    inference(forward_demodulation,[],[f137,f144])).
% 9.09/1.55  fof(f137,plain,(
% 9.09/1.55    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_2),
% 9.09/1.55    inference(avatar_component_clause,[],[f136])).
% 9.09/1.55  fof(f1999,plain,(
% 9.09/1.55    spl7_82 | ~spl7_2 | ~spl7_3 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f1998,f746,f142,f136,f966])).
% 9.09/1.55  fof(f1998,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f963,f748])).
% 9.09/1.55  fof(f1997,plain,(
% 9.09/1.55    spl7_82 | ~spl7_2 | ~spl7_3 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f1996,f746,f142,f136,f966])).
% 9.09/1.55  fof(f1996,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f1995,f748])).
% 9.09/1.55  fof(f1995,plain,(
% 9.09/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3)),
% 9.09/1.55    inference(forward_demodulation,[],[f137,f144])).
% 9.09/1.55  fof(f1994,plain,(
% 9.09/1.55    ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_69 | spl7_81 | ~spl7_101 | ~spl7_102),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f1993])).
% 9.09/1.55  fof(f1993,plain,(
% 9.09/1.55    $false | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_69 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1992,f486])).
% 9.09/1.55  fof(f1992,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | ~spl7_69 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(forward_demodulation,[],[f1991,f877])).
% 9.09/1.55  fof(f877,plain,(
% 9.09/1.55    k1_xboole_0 = u1_struct_0(sK1) | ~spl7_69),
% 9.09/1.55    inference(avatar_component_clause,[],[f875])).
% 9.09/1.55  fof(f1991,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1990,f194])).
% 9.09/1.55  fof(f1990,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1989,f189])).
% 9.09/1.55  fof(f1989,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_11 | ~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1988,f184])).
% 9.09/1.55  fof(f1988,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1987,f179])).
% 9.09/1.55  fof(f1987,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101 | ~spl7_102)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1986,f1294])).
% 9.09/1.55  fof(f1986,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1985,f230])).
% 9.09/1.55  fof(f1985,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_41 | spl7_81 | ~spl7_101)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1984,f495])).
% 9.09/1.55  fof(f1984,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | spl7_81 | ~spl7_101)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1983,f230])).
% 9.09/1.55  fof(f1983,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_81 | ~spl7_101)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1982,f961])).
% 9.09/1.55  fof(f961,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl7_81),
% 9.09/1.55    inference(avatar_component_clause,[],[f959])).
% 9.09/1.55  fof(f1982,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_101),
% 9.09/1.55    inference(resolution,[],[f1269,f128])).
% 9.09/1.55  fof(f128,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(duplicate_literal_removal,[],[f119])).
% 9.09/1.55  fof(f119,plain,(
% 9.09/1.55    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(equality_resolution,[],[f89])).
% 9.09/1.55  fof(f89,plain,(
% 9.09/1.55    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.09/1.55    inference(cnf_transformation,[],[f51])).
% 9.09/1.55  fof(f1269,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl7_101),
% 9.09/1.55    inference(avatar_component_clause,[],[f1267])).
% 9.09/1.55  fof(f1981,plain,(
% 9.09/1.55    ~spl7_146 | spl7_149 | ~spl7_10 | ~spl7_11 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1977,f875,f182,f177,f1979,f1928])).
% 9.09/1.55  fof(f1928,plain,(
% 9.09/1.55    spl7_146 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).
% 9.09/1.55  fof(f1979,plain,(
% 9.09/1.55    spl7_149 <=> ! [X13,X12] : (~m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X13) | ~l1_pre_topc(X13) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).
% 9.09/1.55  fof(f1977,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_10 | ~spl7_11 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1976,f122])).
% 9.09/1.55  fof(f1976,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_10 | ~spl7_11 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1975,f184])).
% 9.09/1.55  fof(f1975,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | (~spl7_10 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1891,f179])).
% 9.09/1.55  fof(f1891,plain,(
% 9.09/1.55    ( ! [X12,X13] : (~v5_pre_topc(X12,X13,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_1(X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0))) | ~v1_funct_2(X12,u1_struct_0(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))),k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))) | v5_pre_topc(X12,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)),sK1) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(X12,u1_struct_0(X13),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13)) ) | ~spl7_69),
% 9.09/1.55    inference(superposition,[],[f481,f877])).
% 9.09/1.55  fof(f1963,plain,(
% 9.09/1.55    spl7_148 | ~spl7_146 | ~spl7_10 | ~spl7_11 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1958,f875,f182,f177,f1928,f1960])).
% 9.09/1.55  fof(f1960,plain,(
% 9.09/1.55    spl7_148 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).
% 9.09/1.55  fof(f1958,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | (~spl7_10 | ~spl7_11 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1957,f179])).
% 9.09/1.55  fof(f1957,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | (~spl7_11 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1888,f184])).
% 9.09/1.55  fof(f1888,plain,(
% 9.09/1.55    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | ~spl7_69),
% 9.09/1.55    inference(superposition,[],[f319,f877])).
% 9.09/1.55  fof(f1939,plain,(
% 9.09/1.55    spl7_145 | ~spl7_10 | ~spl7_11 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1938,f875,f182,f177,f1915])).
% 9.09/1.55  fof(f1915,plain,(
% 9.09/1.55    spl7_145 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).
% 9.09/1.55  fof(f1938,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_10 | ~spl7_11 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1937,f184])).
% 9.09/1.55  fof(f1937,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl7_10 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1882,f179])).
% 9.09/1.55  fof(f1882,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl7_69),
% 9.09/1.55    inference(superposition,[],[f85,f877])).
% 9.09/1.55  fof(f1936,plain,(
% 9.09/1.55    spl7_147 | ~spl7_49 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1879,f875,f620,f1933])).
% 9.09/1.55  fof(f1933,plain,(
% 9.09/1.55    spl7_147 <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).
% 9.09/1.55  fof(f620,plain,(
% 9.09/1.55    spl7_49 <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 9.09/1.55  fof(f1879,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_49 | ~spl7_69)),
% 9.09/1.55    inference(superposition,[],[f622,f877])).
% 9.09/1.55  fof(f622,plain,(
% 9.09/1.55    r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_49),
% 9.09/1.55    inference(avatar_component_clause,[],[f620])).
% 9.09/1.55  fof(f1931,plain,(
% 9.09/1.55    spl7_146 | ~spl7_33 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1878,f875,f425,f1928])).
% 9.09/1.55  fof(f1878,plain,(
% 9.09/1.55    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_33 | ~spl7_69)),
% 9.09/1.55    inference(superposition,[],[f426,f877])).
% 9.09/1.55  fof(f1918,plain,(
% 9.09/1.55    spl7_145 | ~spl7_26 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1873,f875,f326,f1915])).
% 9.09/1.55  fof(f1873,plain,(
% 9.09/1.55    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_26 | ~spl7_69)),
% 9.09/1.55    inference(superposition,[],[f328,f877])).
% 9.09/1.55  fof(f1913,plain,(
% 9.09/1.55    spl7_144 | ~spl7_24 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1872,f875,f309,f1910])).
% 9.09/1.55  fof(f1910,plain,(
% 9.09/1.55    spl7_144 <=> v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).
% 9.09/1.55  fof(f309,plain,(
% 9.09/1.55    spl7_24 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 9.09/1.55  fof(f1872,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_24 | ~spl7_69)),
% 9.09/1.55    inference(superposition,[],[f311,f877])).
% 9.09/1.55  fof(f311,plain,(
% 9.09/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_24),
% 9.09/1.55    inference(avatar_component_clause,[],[f309])).
% 9.09/1.55  fof(f1907,plain,(
% 9.09/1.55    spl7_143 | ~spl7_20 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1870,f875,f262,f1904])).
% 9.09/1.55  fof(f1904,plain,(
% 9.09/1.55    spl7_143 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).
% 9.09/1.55  fof(f1870,plain,(
% 9.09/1.55    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl7_20 | ~spl7_69)),
% 9.09/1.55    inference(superposition,[],[f264,f877])).
% 9.09/1.55  fof(f1823,plain,(
% 9.09/1.55    ~spl7_142 | spl7_34 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1818,f875,f746,f429,f1820])).
% 9.09/1.55  fof(f429,plain,(
% 9.09/1.55    spl7_34 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 9.09/1.55  fof(f1818,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl7_34 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1817,f748])).
% 9.09/1.55  fof(f1817,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (spl7_34 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f431,f877])).
% 9.09/1.55  fof(f431,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl7_34),
% 9.09/1.55    inference(avatar_component_clause,[],[f429])).
% 9.09/1.55  fof(f1804,plain,(
% 9.09/1.55    spl7_80 | ~spl7_69 | ~spl7_82),
% 9.09/1.55    inference(avatar_split_clause,[],[f1803,f966,f875,f953])).
% 9.09/1.55  fof(f953,plain,(
% 9.09/1.55    spl7_80 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 9.09/1.55  fof(f1803,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_69 | ~spl7_82)),
% 9.09/1.55    inference(forward_demodulation,[],[f968,f877])).
% 9.09/1.55  fof(f968,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_82),
% 9.09/1.55    inference(avatar_component_clause,[],[f966])).
% 9.09/1.55  fof(f1800,plain,(
% 9.09/1.55    spl7_141 | ~spl7_114 | ~spl7_140),
% 9.09/1.55    inference(avatar_split_clause,[],[f1795,f1766,f1464,f1797])).
% 9.09/1.55  fof(f1795,plain,(
% 9.09/1.55    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_114 | ~spl7_140)),
% 9.09/1.55    inference(forward_demodulation,[],[f1768,f1466])).
% 9.09/1.55  fof(f1768,plain,(
% 9.09/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~spl7_140),
% 9.09/1.55    inference(avatar_component_clause,[],[f1766])).
% 9.09/1.55  fof(f1794,plain,(
% 9.09/1.55    spl7_81 | ~spl7_1 | ~spl7_58),
% 9.09/1.55    inference(avatar_split_clause,[],[f1793,f746,f132,f959])).
% 9.09/1.55  fof(f132,plain,(
% 9.09/1.55    spl7_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 9.09/1.55  fof(f1793,plain,(
% 9.09/1.55    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_1 | ~spl7_58)),
% 9.09/1.55    inference(forward_demodulation,[],[f133,f748])).
% 9.09/1.55  fof(f133,plain,(
% 9.09/1.55    v5_pre_topc(sK2,sK0,sK1) | ~spl7_1),
% 9.09/1.55    inference(avatar_component_clause,[],[f132])).
% 9.09/1.55  fof(f1792,plain,(
% 9.09/1.55    ~spl7_80 | spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1791,f875,f746,f142,f136,f953])).
% 9.09/1.55  fof(f1791,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1790,f748])).
% 9.09/1.55  fof(f1790,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1789,f144])).
% 9.09/1.55  fof(f1789,plain,(
% 9.09/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_2 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f138,f877])).
% 9.09/1.55  fof(f1788,plain,(
% 9.09/1.55    ~spl7_80 | spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1787,f875,f746,f142,f136,f953])).
% 9.09/1.55  fof(f1787,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1786,f748])).
% 9.09/1.55  fof(f1786,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_2 | ~spl7_3 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f203,f877])).
% 9.09/1.55  fof(f1785,plain,(
% 9.09/1.55    ~spl7_80 | spl7_15 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f1784,f875,f746,f205,f953])).
% 9.09/1.55  fof(f1784,plain,(
% 9.09/1.55    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_15 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1783,f748])).
% 9.09/1.55  fof(f1783,plain,(
% 9.09/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_15 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f207,f877])).
% 9.09/1.55  fof(f1782,plain,(
% 9.09/1.55    ~spl7_14 | spl7_35 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f1781])).
% 9.09/1.55  fof(f1781,plain,(
% 9.09/1.55    $false | (~spl7_14 | spl7_35 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1780,f230])).
% 9.09/1.55  fof(f1780,plain,(
% 9.09/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (spl7_35 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1779,f748])).
% 9.09/1.55  fof(f1779,plain,(
% 9.09/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (spl7_35 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f435,f877])).
% 9.09/1.55  fof(f1778,plain,(
% 9.09/1.55    ~spl7_14 | spl7_40 | ~spl7_58 | ~spl7_69),
% 9.09/1.55    inference(avatar_contradiction_clause,[],[f1777])).
% 9.09/1.55  fof(f1777,plain,(
% 9.09/1.55    $false | (~spl7_14 | spl7_40 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(subsumption_resolution,[],[f1776,f486])).
% 9.09/1.55  fof(f1776,plain,(
% 9.09/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl7_40 | ~spl7_58 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f1775,f748])).
% 9.09/1.55  fof(f1775,plain,(
% 9.09/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (spl7_40 | ~spl7_69)),
% 9.09/1.55    inference(forward_demodulation,[],[f474,f877])).
% 9.09/1.55  fof(f1772,plain,(
% 9.09/1.55    spl7_56 | ~spl7_7 | ~spl7_62),
% 9.09/1.55    inference(avatar_split_clause,[],[f1306,f781,f162,f727])).
% 9.09/1.55  fof(f727,plain,(
% 9.09/1.55    spl7_56 <=> v1_xboole_0(sK2)),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 9.09/1.55  fof(f1306,plain,(
% 9.09/1.55    v1_xboole_0(sK2) | (~spl7_7 | ~spl7_62)),
% 9.09/1.55    inference(unit_resulting_resolution,[],[f164,f782,f92])).
% 9.09/1.55  fof(f782,plain,(
% 9.09/1.55    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_62),
% 9.09/1.55    inference(avatar_component_clause,[],[f781])).
% 9.09/1.55  fof(f1771,plain,(
% 9.09/1.55    spl7_63 | ~spl7_39 | ~spl7_69),
% 9.09/1.55    inference(avatar_split_clause,[],[f939,f875,f468,f788])).
% 9.09/1.55  fof(f788,plain,(
% 9.09/1.55    spl7_63 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 9.09/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 9.09/1.55  fof(f939,plain,(
% 9.09/1.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_39 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f938,f122])).
% 9.30/1.55  fof(f938,plain,(
% 9.30/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl7_39 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f469,f877])).
% 9.30/1.55  fof(f1770,plain,(
% 9.30/1.55    spl7_140 | ~spl7_17 | ~spl7_30 | ~spl7_77),
% 9.30/1.55    inference(avatar_split_clause,[],[f1614,f917,f392,f243,f1766])).
% 9.30/1.55  fof(f243,plain,(
% 9.30/1.55    spl7_17 <=> v1_relat_1(sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 9.30/1.55  fof(f392,plain,(
% 9.30/1.55    spl7_30 <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 9.30/1.55  fof(f1614,plain,(
% 9.30/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | (~spl7_17 | ~spl7_30 | ~spl7_77)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f245,f394,f919,f95])).
% 9.30/1.55  fof(f95,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 9.30/1.55    inference(cnf_transformation,[],[f56])).
% 9.30/1.55  fof(f56,plain,(
% 9.30/1.55    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 9.30/1.55    inference(nnf_transformation,[],[f36])).
% 9.30/1.55  fof(f36,plain,(
% 9.30/1.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 9.30/1.55    inference(flattening,[],[f35])).
% 9.30/1.55  fof(f35,plain,(
% 9.30/1.55    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 9.30/1.55    inference(ennf_transformation,[],[f13])).
% 9.30/1.55  fof(f13,axiom,(
% 9.30/1.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 9.30/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 9.30/1.55  fof(f919,plain,(
% 9.30/1.55    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl7_77),
% 9.30/1.55    inference(avatar_component_clause,[],[f917])).
% 9.30/1.55  fof(f394,plain,(
% 9.30/1.55    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl7_30),
% 9.30/1.55    inference(avatar_component_clause,[],[f392])).
% 9.30/1.55  fof(f245,plain,(
% 9.30/1.55    v1_relat_1(sK2) | ~spl7_17),
% 9.30/1.55    inference(avatar_component_clause,[],[f243])).
% 9.30/1.55  fof(f1769,plain,(
% 9.30/1.55    spl7_140 | ~spl7_17 | ~spl7_30 | ~spl7_77),
% 9.30/1.55    inference(avatar_split_clause,[],[f1623,f917,f392,f243,f1766])).
% 9.30/1.55  fof(f1623,plain,(
% 9.30/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | (~spl7_17 | ~spl7_30 | ~spl7_77)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1622,f245])).
% 9.30/1.55  fof(f1622,plain,(
% 9.30/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl7_30 | ~spl7_77)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1615,f394])).
% 9.30/1.55  fof(f1615,plain,(
% 9.30/1.55    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_relat_1(sK2) | ~spl7_77),
% 9.30/1.55    inference(resolution,[],[f919,f95])).
% 9.30/1.55  fof(f1764,plain,(
% 9.30/1.55    ~spl7_38 | spl7_15 | ~spl7_39 | ~spl7_40 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f1763,f460,f321,f182,f177,f157,f152,f147,f142,f472,f468,f205,f464])).
% 9.30/1.55  fof(f147,plain,(
% 9.30/1.55    spl7_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 9.30/1.55  fof(f152,plain,(
% 9.30/1.55    spl7_5 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 9.30/1.55  fof(f1763,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_37)),
% 9.30/1.55    inference(forward_demodulation,[],[f1762,f144])).
% 9.30/1.55  fof(f1762,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_37)),
% 9.30/1.55    inference(forward_demodulation,[],[f1761,f144])).
% 9.30/1.55  fof(f1761,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f455,f461])).
% 9.30/1.55  fof(f455,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25)),
% 9.30/1.55    inference(forward_demodulation,[],[f454,f144])).
% 9.30/1.55  fof(f454,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25)),
% 9.30/1.55    inference(forward_demodulation,[],[f453,f144])).
% 9.30/1.55  fof(f453,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | ~spl7_25)),
% 9.30/1.55    inference(subsumption_resolution,[],[f452,f323])).
% 9.30/1.55  fof(f452,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11)),
% 9.30/1.55    inference(subsumption_resolution,[],[f451,f184])).
% 9.30/1.55  fof(f451,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10)),
% 9.30/1.55    inference(subsumption_resolution,[],[f450,f179])).
% 9.30/1.55  fof(f450,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5 | ~spl7_6)),
% 9.30/1.55    inference(subsumption_resolution,[],[f449,f159])).
% 9.30/1.55  fof(f449,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_4 | ~spl7_5)),
% 9.30/1.55    inference(subsumption_resolution,[],[f446,f149])).
% 9.30/1.55  fof(f149,plain,(
% 9.30/1.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_4),
% 9.30/1.55    inference(avatar_component_clause,[],[f147])).
% 9.30/1.55  fof(f446,plain,(
% 9.30/1.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_5),
% 9.30/1.55    inference(resolution,[],[f129,f154])).
% 9.30/1.55  fof(f154,plain,(
% 9.30/1.55    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_5),
% 9.30/1.55    inference(avatar_component_clause,[],[f152])).
% 9.30/1.55  fof(f1760,plain,(
% 9.30/1.55    ~spl7_40 | ~spl7_39 | spl7_15 | ~spl7_38 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f1759,f460,f405,f373,f321,f182,f177,f172,f464,f205,f468,f472])).
% 9.30/1.55  fof(f1759,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1758,f323])).
% 9.30/1.55  fof(f1758,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_28 | ~spl7_32 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1757,f461])).
% 9.30/1.55  fof(f1757,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1756,f184])).
% 9.30/1.55  fof(f1756,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1755,f179])).
% 9.30/1.55  fof(f1755,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1754,f174])).
% 9.30/1.55  fof(f1754,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f807,f407])).
% 9.30/1.55  fof(f807,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_28),
% 9.30/1.55    inference(resolution,[],[f375,f129])).
% 9.30/1.55  fof(f1753,plain,(
% 9.30/1.55    ~spl7_128 | spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1752,f1553,f437,f433,f192,f187,f182,f177,f172,f167,f162,f132,f1636])).
% 9.30/1.55  fof(f437,plain,(
% 9.30/1.55    spl7_36 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 9.30/1.55  fof(f1752,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1751,f1555])).
% 9.30/1.55  fof(f1751,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1750,f194])).
% 9.30/1.55  fof(f1750,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1749,f189])).
% 9.30/1.55  fof(f1749,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1748,f184])).
% 9.30/1.55  fof(f1748,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1747,f179])).
% 9.30/1.55  fof(f1747,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1746,f169])).
% 9.30/1.55  fof(f1746,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_7 | ~spl7_9 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1745,f164])).
% 9.30/1.55  fof(f1745,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_9 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1744,f174])).
% 9.30/1.55  fof(f1744,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1743,f434])).
% 9.30/1.55  fof(f434,plain,(
% 9.30/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_35),
% 9.30/1.55    inference(avatar_component_clause,[],[f433])).
% 9.30/1.55  fof(f1743,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_1 | ~spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1724,f134])).
% 9.30/1.55  fof(f134,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | spl7_1),
% 9.30/1.55    inference(avatar_component_clause,[],[f132])).
% 9.30/1.55  fof(f1724,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_36),
% 9.30/1.55    inference(resolution,[],[f438,f130])).
% 9.30/1.55  fof(f438,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_36),
% 9.30/1.55    inference(avatar_component_clause,[],[f437])).
% 9.30/1.55  fof(f1726,plain,(
% 9.30/1.55    ~spl7_128 | spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1725,f1553,f437,f433,f192,f187,f182,f177,f172,f167,f162,f132,f1636])).
% 9.30/1.55  fof(f1725,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1722,f1555])).
% 9.30/1.55  fof(f1722,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_35 | ~spl7_36)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f194,f189,f184,f179,f174,f134,f169,f164,f434,f438,f130])).
% 9.30/1.55  fof(f1721,plain,(
% 9.30/1.55    ~spl7_139 | ~spl7_14 | ~spl7_41 | spl7_70 | spl7_114 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1716,f1553,f1464,f879,f493,f197,f1718])).
% 9.30/1.55  fof(f1718,plain,(
% 9.30/1.55    spl7_139 <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_relat_1(sK2))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_139])])).
% 9.30/1.55  fof(f1716,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),k1_relat_1(sK2)) | (~spl7_14 | ~spl7_41 | spl7_70 | spl7_114 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1673,f1555])).
% 9.30/1.55  fof(f1673,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_relat_1(sK2)) | (~spl7_14 | ~spl7_41 | spl7_70 | spl7_114)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f880,f495,f230,f1465,f125])).
% 9.30/1.55  fof(f1465,plain,(
% 9.30/1.55    k1_xboole_0 != k1_relat_1(sK2) | spl7_114),
% 9.30/1.55    inference(avatar_component_clause,[],[f1464])).
% 9.30/1.55  fof(f880,plain,(
% 9.30/1.55    ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | spl7_70),
% 9.30/1.55    inference(avatar_component_clause,[],[f879])).
% 9.30/1.55  fof(f1715,plain,(
% 9.30/1.55    ~spl7_138 | spl7_58 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1676,f1464,f746,f1712])).
% 9.30/1.55  fof(f1712,plain,(
% 9.30/1.55    spl7_138 <=> k1_xboole_0 = k2_zfmisc_1(sK2,k1_relat_1(sK2))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).
% 9.30/1.55  fof(f1676,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(sK2,k1_relat_1(sK2)) | (spl7_58 | spl7_114)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f1465,f102])).
% 9.30/1.55  fof(f747,plain,(
% 9.30/1.55    k1_xboole_0 != sK2 | spl7_58),
% 9.30/1.55    inference(avatar_component_clause,[],[f746])).
% 9.30/1.55  fof(f1710,plain,(
% 9.30/1.55    ~spl7_137 | spl7_69 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1677,f1464,f875,f1707])).
% 9.30/1.55  fof(f1707,plain,(
% 9.30/1.55    spl7_137 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).
% 9.30/1.55  fof(f1677,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)) | (spl7_69 | spl7_114)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f876,f1465,f102])).
% 9.30/1.55  fof(f1705,plain,(
% 9.30/1.55    ~spl7_134 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1678,f1464,f1691])).
% 9.30/1.55  fof(f1691,plain,(
% 9.30/1.55    spl7_134 <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).
% 9.30/1.55  fof(f1678,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)) | spl7_114),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f1465,f1465,f102])).
% 9.30/1.55  fof(f1704,plain,(
% 9.30/1.55    ~spl7_136 | spl7_58 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1680,f1464,f746,f1701])).
% 9.30/1.55  fof(f1701,plain,(
% 9.30/1.55    spl7_136 <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).
% 9.30/1.55  fof(f1680,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),sK2) | (spl7_58 | spl7_114)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f1465,f102])).
% 9.30/1.55  fof(f1699,plain,(
% 9.30/1.55    ~spl7_135 | spl7_69 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1681,f1464,f875,f1696])).
% 9.30/1.55  fof(f1696,plain,(
% 9.30/1.55    spl7_135 <=> k1_xboole_0 = k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).
% 9.30/1.55  fof(f1681,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)) | (spl7_69 | spl7_114)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f876,f1465,f102])).
% 9.30/1.55  fof(f1694,plain,(
% 9.30/1.55    ~spl7_134 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1682,f1464,f1691])).
% 9.30/1.55  fof(f1682,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(k1_relat_1(sK2),k1_relat_1(sK2)) | spl7_114),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f1465,f1465,f102])).
% 9.30/1.55  fof(f1689,plain,(
% 9.30/1.55    ~spl7_133 | spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1684,f1464,f1686])).
% 9.30/1.55  fof(f1686,plain,(
% 9.30/1.55    spl7_133 <=> v1_xboole_0(k1_relat_1(sK2))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).
% 9.30/1.55  fof(f1684,plain,(
% 9.30/1.55    ~v1_xboole_0(k1_relat_1(sK2)) | spl7_114),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f1465,f82])).
% 9.30/1.55  fof(f1671,plain,(
% 9.30/1.55    spl7_129 | ~spl7_38 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1670,f1553,f464,f1651])).
% 9.30/1.55  fof(f1651,plain,(
% 9.30/1.55    spl7_129 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).
% 9.30/1.55  fof(f1670,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_38 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f465,f1555])).
% 9.30/1.55  fof(f465,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl7_38),
% 9.30/1.55    inference(avatar_component_clause,[],[f464])).
% 9.30/1.55  fof(f1669,plain,(
% 9.30/1.55    spl7_132 | ~spl7_39 | ~spl7_122 | ~spl7_127),
% 9.30/1.55    inference(avatar_split_clause,[],[f1664,f1618,f1553,f468,f1666])).
% 9.30/1.55  fof(f1666,plain,(
% 9.30/1.55    spl7_132 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).
% 9.30/1.55  fof(f1664,plain,(
% 9.30/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl7_39 | ~spl7_122 | ~spl7_127)),
% 9.30/1.55    inference(forward_demodulation,[],[f1663,f1620])).
% 9.30/1.55  fof(f1620,plain,(
% 9.30/1.55    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl7_127),
% 9.30/1.55    inference(avatar_component_clause,[],[f1618])).
% 9.30/1.55  fof(f1663,plain,(
% 9.30/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl7_39 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f469,f1555])).
% 9.30/1.55  fof(f1662,plain,(
% 9.30/1.55    spl7_129 | ~spl7_130 | ~spl7_131 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1649,f1553,f460,f405,f373,f321,f205,f182,f177,f172,f1659,f1655,f1651])).
% 9.30/1.55  fof(f1655,plain,(
% 9.30/1.55    spl7_130 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).
% 9.30/1.55  fof(f1649,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1648,f1555])).
% 9.30/1.55  fof(f1648,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1647,f1555])).
% 9.30/1.55  fof(f1647,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1646,f1555])).
% 9.30/1.55  fof(f1646,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1645,f323])).
% 9.30/1.55  fof(f1645,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1644,f461])).
% 9.30/1.55  fof(f1644,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1643,f184])).
% 9.30/1.55  fof(f1643,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1642,f179])).
% 9.30/1.55  fof(f1642,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1641,f174])).
% 9.30/1.55  fof(f1641,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1640,f375])).
% 9.30/1.55  fof(f1640,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_15 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1032,f407])).
% 9.30/1.55  fof(f1639,plain,(
% 9.30/1.55    spl7_36 | ~spl7_128 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1634,f1553,f433,f425,f405,f373,f326,f205,f192,f187,f172,f1636,f437])).
% 9.30/1.55  fof(f1634,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1633,f1555])).
% 9.30/1.55  fof(f1633,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1632,f194])).
% 9.30/1.55  fof(f1632,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1631,f189])).
% 9.30/1.55  fof(f1631,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1630,f328])).
% 9.30/1.55  fof(f1630,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_35)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1629,f426])).
% 9.30/1.55  fof(f1629,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_35)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1628,f434])).
% 9.30/1.55  fof(f1628,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1627,f174])).
% 9.30/1.55  fof(f1627,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1626,f375])).
% 9.30/1.55  fof(f1626,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_15 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1031,f407])).
% 9.30/1.55  fof(f1031,plain,(
% 9.30/1.55    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_15),
% 9.30/1.55    inference(resolution,[],[f206,f128])).
% 9.30/1.55  fof(f1625,plain,(
% 9.30/1.55    spl7_127 | ~spl7_17 | ~spl7_30 | ~spl7_77 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1624,f1553,f917,f392,f243,f1618])).
% 9.30/1.55  fof(f1624,plain,(
% 9.30/1.55    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_17 | ~spl7_30 | ~spl7_77 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1623,f1555])).
% 9.30/1.55  fof(f1621,plain,(
% 9.30/1.55    spl7_127 | ~spl7_17 | ~spl7_30 | ~spl7_77 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1616,f1553,f917,f392,f243,f1618])).
% 9.30/1.55  fof(f1616,plain,(
% 9.30/1.55    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl7_17 | ~spl7_30 | ~spl7_77 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1614,f1555])).
% 9.30/1.55  fof(f1612,plain,(
% 9.30/1.55    ~spl7_126 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1611,f1553,f731,f197,f1600])).
% 9.30/1.55  fof(f731,plain,(
% 9.30/1.55    spl7_57 <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 9.30/1.55  fof(f1611,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1585,f1555])).
% 9.30/1.55  fof(f1585,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(resolution,[],[f733,f298])).
% 9.30/1.55  fof(f733,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl7_57),
% 9.30/1.55    inference(avatar_component_clause,[],[f731])).
% 9.30/1.55  fof(f1610,plain,(
% 9.30/1.55    ~spl7_126 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1609,f1553,f731,f197,f1600])).
% 9.30/1.55  fof(f1609,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1576,f1555])).
% 9.30/1.55  fof(f1576,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f733,f298])).
% 9.30/1.55  fof(f1608,plain,(
% 9.30/1.55    ~spl7_126 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1607,f1553,f731,f197,f1600])).
% 9.30/1.55  fof(f1607,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1577,f1555])).
% 9.30/1.55  fof(f1577,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f199,f733,f116])).
% 9.30/1.55  fof(f1606,plain,(
% 9.30/1.55    ~spl7_126 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1605,f1553,f731,f197,f1600])).
% 9.30/1.55  fof(f1605,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1604,f1555])).
% 9.30/1.55  fof(f1604,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(forward_demodulation,[],[f1578,f348])).
% 9.30/1.55  fof(f1578,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(sK6(X0,k1_xboole_0)))) ) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f332,f733,f116])).
% 9.30/1.55  fof(f1603,plain,(
% 9.30/1.55    ~spl7_126 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1598,f1553,f731,f197,f1600])).
% 9.30/1.55  fof(f1598,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1597,f1555])).
% 9.30/1.55  fof(f1597,plain,(
% 9.30/1.55    ~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(forward_demodulation,[],[f1579,f571])).
% 9.30/1.55  fof(f1579,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_xboole_0,X0)))) ) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f558,f733,f116])).
% 9.30/1.55  fof(f1596,plain,(
% 9.30/1.55    ~spl7_125 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1595,f1553,f731,f197,f1591])).
% 9.30/1.55  fof(f1595,plain,(
% 9.30/1.55    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1581,f1555])).
% 9.30/1.55  fof(f1581,plain,(
% 9.30/1.55    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f212,f733,f97])).
% 9.30/1.55  fof(f1594,plain,(
% 9.30/1.55    ~spl7_125 | ~spl7_14 | ~spl7_57 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1589,f1553,f731,f197,f1591])).
% 9.30/1.55  fof(f1589,plain,(
% 9.30/1.55    ~r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_57 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1588,f1555])).
% 9.30/1.55  fof(f1588,plain,(
% 9.30/1.55    ~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k1_xboole_0) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(forward_demodulation,[],[f1582,f571])).
% 9.30/1.55  fof(f1582,plain,(
% 9.30/1.55    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | ~spl7_57)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f551,f733,f97])).
% 9.30/1.55  fof(f1572,plain,(
% 9.30/1.55    ~spl7_124 | ~spl7_14 | ~spl7_41 | spl7_58 | spl7_70 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1567,f1553,f879,f746,f493,f197,f1569])).
% 9.30/1.55  fof(f1569,plain,(
% 9.30/1.55    spl7_124 <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).
% 9.30/1.55  fof(f1567,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),sK2) | (~spl7_14 | ~spl7_41 | spl7_58 | spl7_70 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1558,f1555])).
% 9.30/1.55  fof(f1558,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),sK2) | (~spl7_14 | ~spl7_41 | spl7_58 | spl7_70)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f495,f747,f230,f880,f125])).
% 9.30/1.55  fof(f1566,plain,(
% 9.30/1.55    ~spl7_123 | ~spl7_14 | ~spl7_41 | spl7_69 | spl7_70 | ~spl7_122),
% 9.30/1.55    inference(avatar_split_clause,[],[f1561,f1553,f879,f875,f493,f197,f1563])).
% 9.30/1.55  fof(f1563,plain,(
% 9.30/1.55    spl7_123 <=> v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).
% 9.30/1.55  fof(f1561,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl7_14 | ~spl7_41 | spl7_69 | spl7_70 | ~spl7_122)),
% 9.30/1.55    inference(forward_demodulation,[],[f1559,f1555])).
% 9.30/1.55  fof(f1559,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_14 | ~spl7_41 | spl7_69 | spl7_70)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f495,f876,f230,f880,f125])).
% 9.30/1.55  fof(f1557,plain,(
% 9.30/1.55    spl7_122 | ~spl7_17 | ~spl7_21 | ~spl7_74),
% 9.30/1.55    inference(avatar_split_clause,[],[f1469,f901,f283,f243,f1553])).
% 9.30/1.55  fof(f283,plain,(
% 9.30/1.55    spl7_21 <=> v4_relat_1(sK2,u1_struct_0(sK0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 9.30/1.55  fof(f901,plain,(
% 9.30/1.55    spl7_74 <=> v1_partfun1(sK2,u1_struct_0(sK0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 9.30/1.55  fof(f1469,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl7_17 | ~spl7_21 | ~spl7_74)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1468,f245])).
% 9.30/1.55  fof(f1468,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl7_21 | ~spl7_74)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1461,f285])).
% 9.30/1.55  fof(f285,plain,(
% 9.30/1.55    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl7_21),
% 9.30/1.55    inference(avatar_component_clause,[],[f283])).
% 9.30/1.55  fof(f1461,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl7_74),
% 9.30/1.55    inference(resolution,[],[f903,f95])).
% 9.30/1.55  fof(f903,plain,(
% 9.30/1.55    v1_partfun1(sK2,u1_struct_0(sK0)) | ~spl7_74),
% 9.30/1.55    inference(avatar_component_clause,[],[f901])).
% 9.30/1.55  fof(f1556,plain,(
% 9.30/1.55    spl7_122 | ~spl7_17 | ~spl7_21 | ~spl7_74),
% 9.30/1.55    inference(avatar_split_clause,[],[f1460,f901,f283,f243,f1553])).
% 9.30/1.55  fof(f1460,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl7_17 | ~spl7_21 | ~spl7_74)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f245,f285,f903,f95])).
% 9.30/1.55  fof(f1551,plain,(
% 9.30/1.55    spl7_113 | ~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1550,f1464,f901,f283,f243,f1452])).
% 9.30/1.55  fof(f1550,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_114)),
% 9.30/1.55    inference(forward_demodulation,[],[f1460,f1466])).
% 9.30/1.55  fof(f1549,plain,(
% 9.30/1.55    spl7_113 | ~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_114),
% 9.30/1.55    inference(avatar_split_clause,[],[f1548,f1464,f901,f283,f243,f1452])).
% 9.30/1.55  fof(f1548,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_114)),
% 9.30/1.55    inference(forward_demodulation,[],[f1469,f1466])).
% 9.30/1.55  fof(f1547,plain,(
% 9.30/1.55    ~spl7_121 | ~spl7_32 | ~spl7_61),
% 9.30/1.55    inference(avatar_split_clause,[],[f1505,f776,f405,f1544])).
% 9.30/1.55  fof(f1544,plain,(
% 9.30/1.55    spl7_121 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).
% 9.30/1.55  fof(f776,plain,(
% 9.30/1.55    spl7_61 <=> r2_hidden(sK4(sK2),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 9.30/1.55  fof(f1505,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_32 | ~spl7_61)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f407,f778,f116])).
% 9.30/1.55  fof(f778,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),sK2) | ~spl7_61),
% 9.30/1.55    inference(avatar_component_clause,[],[f776])).
% 9.30/1.55  fof(f1542,plain,(
% 9.30/1.55    ~spl7_120 | ~spl7_35 | ~spl7_61),
% 9.30/1.55    inference(avatar_split_clause,[],[f1504,f776,f433,f1539])).
% 9.30/1.55  fof(f1539,plain,(
% 9.30/1.55    spl7_120 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).
% 9.30/1.55  fof(f1504,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_35 | ~spl7_61)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f434,f778,f116])).
% 9.30/1.55  fof(f1537,plain,(
% 9.30/1.55    ~spl7_119 | ~spl7_7 | ~spl7_61),
% 9.30/1.55    inference(avatar_split_clause,[],[f1503,f776,f162,f1534])).
% 9.30/1.55  fof(f1534,plain,(
% 9.30/1.55    spl7_119 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).
% 9.30/1.55  fof(f1503,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl7_7 | ~spl7_61)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f164,f778,f116])).
% 9.30/1.55  fof(f1530,plain,(
% 9.30/1.55    ~spl7_7 | ~spl7_14 | ~spl7_61 | ~spl7_113),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1529])).
% 9.30/1.55  fof(f1529,plain,(
% 9.30/1.55    $false | (~spl7_7 | ~spl7_14 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1528,f199])).
% 9.30/1.55  fof(f1528,plain,(
% 9.30/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_7 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1527,f123])).
% 9.30/1.55  fof(f1527,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) | (~spl7_7 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1503,f1454])).
% 9.30/1.55  fof(f1526,plain,(
% 9.30/1.55    ~spl7_14 | ~spl7_35 | ~spl7_61 | ~spl7_113),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1525])).
% 9.30/1.55  fof(f1525,plain,(
% 9.30/1.55    $false | (~spl7_14 | ~spl7_35 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1524,f199])).
% 9.30/1.55  fof(f1524,plain,(
% 9.30/1.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_35 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1523,f123])).
% 9.30/1.55  fof(f1523,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_35 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1504,f1454])).
% 9.30/1.55  fof(f1522,plain,(
% 9.30/1.55    ~spl7_118 | ~spl7_32 | ~spl7_61 | ~spl7_113),
% 9.30/1.55    inference(avatar_split_clause,[],[f1517,f1452,f776,f405,f1519])).
% 9.30/1.55  fof(f1519,plain,(
% 9.30/1.55    spl7_118 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).
% 9.30/1.55  fof(f1517,plain,(
% 9.30/1.55    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_32 | ~spl7_61 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1505,f1454])).
% 9.30/1.55  fof(f1498,plain,(
% 9.30/1.55    spl7_117 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f1472,f709,f197,f1495])).
% 9.30/1.55  fof(f1495,plain,(
% 9.30/1.55    spl7_117 <=> r2_hidden(sK5(u1_pre_topc(sK0),k1_xboole_0),u1_pre_topc(sK0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).
% 9.30/1.55  fof(f1472,plain,(
% 9.30/1.55    r2_hidden(sK5(u1_pre_topc(sK0),k1_xboole_0),u1_pre_topc(sK0)) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f710,f690])).
% 9.30/1.55  fof(f1493,plain,(
% 9.30/1.55    spl7_116 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1473,f718,f197,f1490])).
% 9.30/1.55  fof(f1490,plain,(
% 9.30/1.55    spl7_116 <=> r2_hidden(sK5(u1_pre_topc(sK1),k1_xboole_0),u1_pre_topc(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).
% 9.30/1.55  fof(f718,plain,(
% 9.30/1.55    spl7_54 <=> v1_xboole_0(u1_pre_topc(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 9.30/1.55  fof(f1473,plain,(
% 9.30/1.55    r2_hidden(sK5(u1_pre_topc(sK1),k1_xboole_0),u1_pre_topc(sK1)) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f719,f690])).
% 9.30/1.55  fof(f719,plain,(
% 9.30/1.55    ~v1_xboole_0(u1_pre_topc(sK1)) | spl7_54),
% 9.30/1.55    inference(avatar_component_clause,[],[f718])).
% 9.30/1.55  fof(f1488,plain,(
% 9.30/1.55    spl7_115 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1475,f781,f197,f1485])).
% 9.30/1.55  fof(f1485,plain,(
% 9.30/1.55    spl7_115 <=> r2_hidden(sK5(u1_struct_0(sK1),k1_xboole_0),u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 9.30/1.55  fof(f1475,plain,(
% 9.30/1.55    r2_hidden(sK5(u1_struct_0(sK1),k1_xboole_0),u1_struct_0(sK1)) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f783,f690])).
% 9.30/1.55  fof(f783,plain,(
% 9.30/1.55    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_62),
% 9.30/1.55    inference(avatar_component_clause,[],[f781])).
% 9.30/1.55  fof(f1471,plain,(
% 9.30/1.55    spl7_114 | ~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_113),
% 9.30/1.55    inference(avatar_split_clause,[],[f1470,f1452,f901,f283,f243,f1464])).
% 9.30/1.55  fof(f1470,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1469,f1454])).
% 9.30/1.55  fof(f1467,plain,(
% 9.30/1.55    spl7_114 | ~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_113),
% 9.30/1.55    inference(avatar_split_clause,[],[f1462,f1452,f901,f283,f243,f1464])).
% 9.30/1.55  fof(f1462,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(sK2) | (~spl7_17 | ~spl7_21 | ~spl7_74 | ~spl7_113)),
% 9.30/1.55    inference(forward_demodulation,[],[f1460,f1454])).
% 9.30/1.55  fof(f1459,plain,(
% 9.30/1.55    spl7_113 | ~spl7_14 | ~spl7_18 | ~spl7_43 | ~spl7_70),
% 9.30/1.55    inference(avatar_split_clause,[],[f1458,f879,f508,f248,f197,f1452])).
% 9.30/1.55  fof(f248,plain,(
% 9.30/1.55    spl7_18 <=> v1_relat_1(k1_xboole_0)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 9.30/1.55  fof(f1458,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_14 | ~spl7_18 | ~spl7_43 | ~spl7_70)),
% 9.30/1.55    inference(forward_demodulation,[],[f1457,f510])).
% 9.30/1.55  fof(f1457,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_18 | ~spl7_70)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1456,f250])).
% 9.30/1.55  fof(f250,plain,(
% 9.30/1.55    v1_relat_1(k1_xboole_0) | ~spl7_18),
% 9.30/1.55    inference(avatar_component_clause,[],[f248])).
% 9.30/1.55  fof(f1456,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_70)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1449,f279])).
% 9.30/1.55  fof(f279,plain,(
% 9.30/1.55    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) ) | ~spl7_14),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f230,f112])).
% 9.30/1.55  fof(f112,plain,(
% 9.30/1.55    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.30/1.55    inference(cnf_transformation,[],[f39])).
% 9.30/1.55  fof(f39,plain,(
% 9.30/1.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.30/1.55    inference(ennf_transformation,[],[f11])).
% 9.30/1.55  fof(f11,axiom,(
% 9.30/1.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 9.30/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 9.30/1.55  fof(f1449,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,u1_struct_0(sK0)) | ~v1_relat_1(k1_xboole_0) | ~spl7_70),
% 9.30/1.55    inference(resolution,[],[f881,f95])).
% 9.30/1.55  fof(f881,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~spl7_70),
% 9.30/1.55    inference(avatar_component_clause,[],[f879])).
% 9.30/1.55  fof(f1455,plain,(
% 9.30/1.55    spl7_113 | ~spl7_14 | ~spl7_18 | ~spl7_43 | ~spl7_70),
% 9.30/1.55    inference(avatar_split_clause,[],[f1450,f879,f508,f248,f197,f1452])).
% 9.30/1.55  fof(f1450,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK0) | (~spl7_14 | ~spl7_18 | ~spl7_43 | ~spl7_70)),
% 9.30/1.55    inference(forward_demodulation,[],[f1448,f510])).
% 9.30/1.55  fof(f1448,plain,(
% 9.30/1.55    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_18 | ~spl7_70)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f250,f279,f881,f95])).
% 9.30/1.55  fof(f1447,plain,(
% 9.30/1.55    ~spl7_112 | spl7_58 | spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f1425,f875,f746,f1444])).
% 9.30/1.55  fof(f1444,plain,(
% 9.30/1.55    spl7_112 <=> k1_xboole_0 = k2_zfmisc_1(sK2,u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 9.30/1.55  fof(f1425,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(sK2,u1_struct_0(sK1)) | (spl7_58 | spl7_69)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f876,f102])).
% 9.30/1.55  fof(f1442,plain,(
% 9.30/1.55    ~spl7_110 | spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f1426,f875,f1433])).
% 9.30/1.55  fof(f1426,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) | spl7_69),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f876,f876,f102])).
% 9.30/1.55  fof(f1441,plain,(
% 9.30/1.55    ~spl7_111 | spl7_58 | spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f1428,f875,f746,f1438])).
% 9.30/1.55  fof(f1438,plain,(
% 9.30/1.55    spl7_111 <=> k1_xboole_0 = k2_zfmisc_1(u1_struct_0(sK1),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).
% 9.30/1.55  fof(f1428,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),sK2) | (spl7_58 | spl7_69)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f876,f102])).
% 9.30/1.55  fof(f1436,plain,(
% 9.30/1.55    ~spl7_110 | spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f1429,f875,f1433])).
% 9.30/1.55  fof(f1429,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) | spl7_69),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f876,f876,f102])).
% 9.30/1.55  fof(f1419,plain,(
% 9.30/1.55    spl7_109 | spl7_64),
% 9.30/1.55    inference(avatar_split_clause,[],[f1413,f800,f1415])).
% 9.30/1.55  fof(f1415,plain,(
% 9.30/1.55    spl7_109 <=> r2_hidden(sK5(sK2,k1_xboole_0),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).
% 9.30/1.55  fof(f1413,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k1_xboole_0),sK2) | spl7_64),
% 9.30/1.55    inference(resolution,[],[f802,f98])).
% 9.30/1.55  fof(f802,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k1_xboole_0) | spl7_64),
% 9.30/1.55    inference(avatar_component_clause,[],[f800])).
% 9.30/1.55  fof(f1418,plain,(
% 9.30/1.55    spl7_109 | spl7_64),
% 9.30/1.55    inference(avatar_split_clause,[],[f1411,f800,f1415])).
% 9.30/1.55  fof(f1411,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k1_xboole_0),sK2) | spl7_64),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f802,f98])).
% 9.30/1.55  fof(f1409,plain,(
% 9.30/1.55    spl7_103 | ~spl7_104 | ~spl7_105 | ~spl7_106 | ~spl7_107 | ~spl7_108 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f1384,f460,f425,f405,f373,f321,f205,f182,f177,f172,f1406,f1402,f1398,f1394,f1390,f1386])).
% 9.30/1.55  fof(f1386,plain,(
% 9.30/1.55    spl7_103 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 9.30/1.55  fof(f1394,plain,(
% 9.30/1.55    spl7_105 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 9.30/1.55  fof(f1398,plain,(
% 9.30/1.55    spl7_106 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 9.30/1.55  fof(f1402,plain,(
% 9.30/1.55    spl7_107 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).
% 9.30/1.55  fof(f1406,plain,(
% 9.30/1.55    spl7_108 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).
% 9.30/1.55  fof(f1384,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1383,f323])).
% 9.30/1.55  fof(f1383,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_33 | ~spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1382,f461])).
% 9.30/1.55  fof(f1382,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_33)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1381,f426])).
% 9.30/1.55  fof(f1381,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1380,f375])).
% 9.30/1.55  fof(f1380,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1379,f407])).
% 9.30/1.55  fof(f1379,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1378,f184])).
% 9.30/1.55  fof(f1378,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_15)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1377,f179])).
% 9.30/1.55  fof(f1377,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_15)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1373,f174])).
% 9.30/1.55  fof(f1373,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_15),
% 9.30/1.55    inference(resolution,[],[f481,f206])).
% 9.30/1.55  fof(f1320,plain,(
% 9.30/1.55    ~spl7_56 | spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1190,f746,f727])).
% 9.30/1.55  fof(f1190,plain,(
% 9.30/1.55    ~v1_xboole_0(sK2) | spl7_58),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f82])).
% 9.30/1.55  fof(f1319,plain,(
% 9.30/1.55    ~spl7_62 | spl7_69),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1318])).
% 9.30/1.55  fof(f1318,plain,(
% 9.30/1.55    $false | (~spl7_62 | spl7_69)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1314,f876])).
% 9.30/1.55  fof(f1314,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK1) | ~spl7_62),
% 9.30/1.55    inference(resolution,[],[f782,f82])).
% 9.30/1.55  fof(f1316,plain,(
% 9.30/1.55    ~spl7_62 | spl7_69),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1315])).
% 9.30/1.55  fof(f1315,plain,(
% 9.30/1.55    $false | (~spl7_62 | spl7_69)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1311,f876])).
% 9.30/1.55  fof(f1311,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(sK1) | ~spl7_62),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f782,f82])).
% 9.30/1.55  fof(f1299,plain,(
% 9.30/1.55    ~spl7_14 | spl7_39 | ~spl7_58),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1298])).
% 9.30/1.55  fof(f1298,plain,(
% 9.30/1.55    $false | (~spl7_14 | spl7_39 | ~spl7_58)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1290,f230])).
% 9.30/1.55  fof(f1290,plain,(
% 9.30/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (spl7_39 | ~spl7_58)),
% 9.30/1.55    inference(superposition,[],[f470,f748])).
% 9.30/1.55  fof(f470,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl7_39),
% 9.30/1.55    inference(avatar_component_clause,[],[f468])).
% 9.30/1.55  fof(f1297,plain,(
% 9.30/1.55    ~spl7_101 | spl7_38 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1289,f746,f464,f1267])).
% 9.30/1.55  fof(f1296,plain,(
% 9.30/1.55    spl7_100 | ~spl7_28 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1280,f746,f373,f1255])).
% 9.30/1.55  fof(f1255,plain,(
% 9.30/1.55    spl7_100 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).
% 9.30/1.55  fof(f1280,plain,(
% 9.30/1.55    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_28 | ~spl7_58)),
% 9.30/1.55    inference(superposition,[],[f375,f748])).
% 9.30/1.55  fof(f1295,plain,(
% 9.30/1.55    spl7_102 | ~spl7_8 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1273,f746,f167,f1292])).
% 9.30/1.55  fof(f1273,plain,(
% 9.30/1.55    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl7_8 | ~spl7_58)),
% 9.30/1.55    inference(superposition,[],[f169,f748])).
% 9.30/1.55  fof(f1270,plain,(
% 9.30/1.55    ~spl7_84 | ~spl7_100 | spl7_101 | ~spl7_10 | ~spl7_11 | ~spl7_14 | ~spl7_25 | ~spl7_37 | ~spl7_41 | ~spl7_82),
% 9.30/1.55    inference(avatar_split_clause,[],[f1265,f966,f493,f460,f321,f197,f182,f177,f1267,f1255,f981])).
% 9.30/1.55  fof(f1265,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_10 | ~spl7_11 | ~spl7_14 | ~spl7_25 | ~spl7_37 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1264,f323])).
% 9.30/1.55  fof(f1264,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_10 | ~spl7_11 | ~spl7_14 | ~spl7_37 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1263,f461])).
% 9.30/1.55  fof(f1263,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_10 | ~spl7_11 | ~spl7_14 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1262,f184])).
% 9.30/1.55  fof(f1262,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_10 | ~spl7_14 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1261,f179])).
% 9.30/1.55  fof(f1261,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_14 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1260,f230])).
% 9.30/1.55  fof(f1260,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_14 | ~spl7_41 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1259,f495])).
% 9.30/1.55  fof(f1259,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_14 | ~spl7_82)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1241,f230])).
% 9.30/1.55  fof(f1241,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_82),
% 9.30/1.55    inference(resolution,[],[f968,f130])).
% 9.30/1.55  fof(f1258,plain,(
% 9.30/1.55    ~spl7_99 | ~spl7_100 | ~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_26 | ~spl7_33 | ~spl7_41 | ~spl7_82 | spl7_83),
% 9.30/1.55    inference(avatar_split_clause,[],[f1249,f972,f966,f493,f425,f326,f197,f192,f187,f1255,f1251])).
% 9.30/1.55  fof(f1251,plain,(
% 9.30/1.55    spl7_99 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).
% 9.30/1.55  fof(f1249,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_12 | ~spl7_13 | ~spl7_14 | ~spl7_26 | ~spl7_33 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1248,f194])).
% 9.30/1.55  fof(f1248,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl7_12 | ~spl7_14 | ~spl7_26 | ~spl7_33 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1247,f189])).
% 9.30/1.55  fof(f1247,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_26 | ~spl7_33 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1246,f328])).
% 9.30/1.55  fof(f1246,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_33 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1245,f426])).
% 9.30/1.55  fof(f1245,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1244,f230])).
% 9.30/1.55  fof(f1244,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_41 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1243,f495])).
% 9.30/1.55  fof(f1243,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_14 | ~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1242,f230])).
% 9.30/1.55  fof(f1242,plain,(
% 9.30/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_82 | spl7_83)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1240,f974])).
% 9.30/1.55  fof(f1240,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_82),
% 9.30/1.55    inference(resolution,[],[f968,f128])).
% 9.30/1.55  fof(f1238,plain,(
% 9.30/1.55    spl7_96 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1205,f781,f1214])).
% 9.30/1.55  fof(f1214,plain,(
% 9.30/1.55    spl7_96 <=> r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).
% 9.30/1.55  fof(f1205,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl7_62),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f216,f783,f277])).
% 9.30/1.55  fof(f1237,plain,(
% 9.30/1.55    ~spl7_98 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1206,f781,f197,f1233])).
% 9.30/1.55  fof(f1233,plain,(
% 9.30/1.55    spl7_98 <=> r1_tarski(u1_struct_0(sK1),k1_xboole_0)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).
% 9.30/1.55  fof(f1206,plain,(
% 9.30/1.55    ~r1_tarski(u1_struct_0(sK1),k1_xboole_0) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f212,f783,f277])).
% 9.30/1.55  fof(f1236,plain,(
% 9.30/1.55    ~spl7_98 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1231,f781,f197,f1233])).
% 9.30/1.55  fof(f1231,plain,(
% 9.30/1.55    ~r1_tarski(u1_struct_0(sK1),k1_xboole_0) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1207,f571])).
% 9.30/1.55  fof(f1207,plain,(
% 9.30/1.55    ( ! [X0] : (~r1_tarski(u1_struct_0(sK1),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f551,f783,f277])).
% 9.30/1.55  fof(f1230,plain,(
% 9.30/1.55    ~spl7_97 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1208,f781,f197,f1221])).
% 9.30/1.55  fof(f1221,plain,(
% 9.30/1.55    spl7_97 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 9.30/1.55  fof(f1208,plain,(
% 9.30/1.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f783,f335])).
% 9.30/1.55  fof(f1229,plain,(
% 9.30/1.55    ~spl7_97 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1228,f781,f197,f1221])).
% 9.30/1.55  fof(f1228,plain,(
% 9.30/1.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1209,f122])).
% 9.30/1.55  fof(f1209,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f199,f783,f92])).
% 9.30/1.55  fof(f1227,plain,(
% 9.30/1.55    ~spl7_97 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1226,f781,f197,f1221])).
% 9.30/1.55  fof(f1226,plain,(
% 9.30/1.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1225,f122])).
% 9.30/1.55  fof(f1225,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1210,f348])).
% 9.30/1.55  fof(f1210,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f332,f783,f92])).
% 9.30/1.55  fof(f1224,plain,(
% 9.30/1.55    ~spl7_97 | ~spl7_14 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1219,f781,f197,f1221])).
% 9.30/1.55  fof(f1219,plain,(
% 9.30/1.55    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1218,f122])).
% 9.30/1.55  fof(f1218,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(forward_demodulation,[],[f1211,f571])).
% 9.30/1.55  fof(f1211,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))) ) | (~spl7_14 | spl7_62)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f558,f783,f92])).
% 9.30/1.55  fof(f1217,plain,(
% 9.30/1.55    spl7_96 | spl7_62),
% 9.30/1.55    inference(avatar_split_clause,[],[f1212,f781,f1214])).
% 9.30/1.55  fof(f1212,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl7_62),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f783,f91])).
% 9.30/1.55  fof(f1196,plain,(
% 9.30/1.55    ~spl7_95 | spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1186,f746,f1192])).
% 9.30/1.55  fof(f1186,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(sK2,sK2) | spl7_58),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f747,f102])).
% 9.30/1.55  fof(f1195,plain,(
% 9.30/1.55    ~spl7_95 | spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f1188,f746,f1192])).
% 9.30/1.55  fof(f1188,plain,(
% 9.30/1.55    k1_xboole_0 != k2_zfmisc_1(sK2,sK2) | spl7_58),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f747,f747,f102])).
% 9.30/1.55  fof(f1161,plain,(
% 9.30/1.55    spl7_87 | ~spl7_35),
% 9.30/1.55    inference(avatar_split_clause,[],[f1131,f433,f1079])).
% 9.30/1.55  fof(f1131,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_35),
% 9.30/1.55    inference(resolution,[],[f434,f100])).
% 9.30/1.55  fof(f1160,plain,(
% 9.30/1.55    spl7_87 | ~spl7_35),
% 9.30/1.55    inference(avatar_split_clause,[],[f1130,f433,f1079])).
% 9.30/1.55  fof(f1130,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_35),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f434,f100])).
% 9.30/1.55  fof(f1159,plain,(
% 9.30/1.55    ~spl7_35 | spl7_87),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1158])).
% 9.30/1.55  fof(f1158,plain,(
% 9.30/1.55    $false | (~spl7_35 | spl7_87)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1130,f1081])).
% 9.30/1.55  fof(f1157,plain,(
% 9.30/1.55    ~spl7_35 | spl7_87),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f1156])).
% 9.30/1.55  fof(f1156,plain,(
% 9.30/1.55    $false | (~spl7_35 | spl7_87)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1131,f1081])).
% 9.30/1.55  fof(f1155,plain,(
% 9.30/1.55    ~spl7_94 | spl7_35 | ~spl7_86),
% 9.30/1.55    inference(avatar_split_clause,[],[f1150,f1070,f433,f1152])).
% 9.30/1.55  fof(f1152,plain,(
% 9.30/1.55    spl7_94 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).
% 9.30/1.55  fof(f1150,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))) | (spl7_35 | ~spl7_86)),
% 9.30/1.55    inference(forward_demodulation,[],[f435,f1072])).
% 9.30/1.55  fof(f1072,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK1) | ~spl7_86),
% 9.30/1.55    inference(avatar_component_clause,[],[f1070])).
% 9.30/1.55  fof(f1149,plain,(
% 9.30/1.55    ~spl7_92 | spl7_35 | ~spl7_86),
% 9.30/1.55    inference(avatar_split_clause,[],[f1148,f1070,f433,f1134])).
% 9.30/1.55  fof(f1134,plain,(
% 9.30/1.55    spl7_92 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 9.30/1.55  fof(f1148,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))) | (spl7_35 | ~spl7_86)),
% 9.30/1.55    inference(forward_demodulation,[],[f1076,f1072])).
% 9.30/1.55  fof(f1147,plain,(
% 9.30/1.55    ~spl7_92 | ~spl7_86 | spl7_87),
% 9.30/1.55    inference(avatar_split_clause,[],[f1146,f1079,f1070,f1134])).
% 9.30/1.55  fof(f1146,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))) | (~spl7_86 | spl7_87)),
% 9.30/1.55    inference(forward_demodulation,[],[f1081,f1072])).
% 9.30/1.55  fof(f1145,plain,(
% 9.30/1.55    spl7_93 | ~spl7_86 | ~spl7_88),
% 9.30/1.55    inference(avatar_split_clause,[],[f1140,f1084,f1070,f1142])).
% 9.30/1.55  fof(f1142,plain,(
% 9.30/1.55    spl7_93 <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).
% 9.30/1.55  fof(f1140,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))),sK2) | (~spl7_86 | ~spl7_88)),
% 9.30/1.55    inference(forward_demodulation,[],[f1086,f1072])).
% 9.30/1.55  fof(f1139,plain,(
% 9.30/1.55    spl7_92 | ~spl7_35 | ~spl7_86),
% 9.30/1.55    inference(avatar_split_clause,[],[f1138,f1070,f433,f1134])).
% 9.30/1.55  fof(f1138,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))) | (~spl7_35 | ~spl7_86)),
% 9.30/1.55    inference(forward_demodulation,[],[f1131,f1072])).
% 9.30/1.55  fof(f1137,plain,(
% 9.30/1.55    spl7_92 | ~spl7_35 | ~spl7_86),
% 9.30/1.55    inference(avatar_split_clause,[],[f1132,f1070,f433,f1134])).
% 9.30/1.55  fof(f1132,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),k1_xboole_0)))) | (~spl7_35 | ~spl7_86)),
% 9.30/1.55    inference(forward_demodulation,[],[f1130,f1072])).
% 9.30/1.55  fof(f1123,plain,(
% 9.30/1.55    spl7_89 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1089,f718,f1099])).
% 9.30/1.55  fof(f1099,plain,(
% 9.30/1.55    spl7_89 <=> r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 9.30/1.55  fof(f1089,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1)) | spl7_54),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f216,f719,f277])).
% 9.30/1.55  fof(f1122,plain,(
% 9.30/1.55    ~spl7_91 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1091,f718,f197,f1118])).
% 9.30/1.55  fof(f1118,plain,(
% 9.30/1.55    spl7_91 <=> r1_tarski(u1_pre_topc(sK1),k1_xboole_0)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 9.30/1.55  fof(f1091,plain,(
% 9.30/1.55    ~r1_tarski(u1_pre_topc(sK1),k1_xboole_0) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f212,f719,f277])).
% 9.30/1.55  fof(f1121,plain,(
% 9.30/1.55    ~spl7_91 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1116,f718,f197,f1118])).
% 9.30/1.55  fof(f1116,plain,(
% 9.30/1.55    ~r1_tarski(u1_pre_topc(sK1),k1_xboole_0) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1092,f571])).
% 9.30/1.55  fof(f1092,plain,(
% 9.30/1.55    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK1),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f551,f719,f277])).
% 9.30/1.55  fof(f1115,plain,(
% 9.30/1.55    ~spl7_90 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1093,f718,f197,f1106])).
% 9.30/1.55  fof(f1106,plain,(
% 9.30/1.55    spl7_90 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 9.30/1.55  fof(f1093,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f719,f335])).
% 9.30/1.55  fof(f1114,plain,(
% 9.30/1.55    ~spl7_90 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1113,f718,f197,f1106])).
% 9.30/1.55  fof(f1113,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1094,f122])).
% 9.30/1.55  fof(f1094,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f199,f719,f92])).
% 9.30/1.55  fof(f1112,plain,(
% 9.30/1.55    ~spl7_90 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1111,f718,f197,f1106])).
% 9.30/1.55  fof(f1111,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1110,f122])).
% 9.30/1.55  fof(f1110,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1095,f348])).
% 9.30/1.55  fof(f1095,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f332,f719,f92])).
% 9.30/1.55  fof(f1109,plain,(
% 9.30/1.55    ~spl7_90 | ~spl7_14 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1104,f718,f197,f1106])).
% 9.30/1.55  fof(f1104,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1103,f122])).
% 9.30/1.55  fof(f1103,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(forward_demodulation,[],[f1096,f571])).
% 9.30/1.55  fof(f1096,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))) ) | (~spl7_14 | spl7_54)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f558,f719,f92])).
% 9.30/1.55  fof(f1102,plain,(
% 9.30/1.55    spl7_89 | spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1097,f718,f1099])).
% 9.30/1.55  fof(f1097,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK1)),u1_pre_topc(sK1)) | spl7_54),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f719,f91])).
% 9.30/1.55  fof(f1088,plain,(
% 9.30/1.55    spl7_88 | spl7_35),
% 9.30/1.55    inference(avatar_split_clause,[],[f1077,f433,f1084])).
% 9.30/1.55  fof(f1077,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2) | spl7_35),
% 9.30/1.55    inference(resolution,[],[f435,f229])).
% 9.30/1.55  fof(f1087,plain,(
% 9.30/1.55    spl7_88 | spl7_35),
% 9.30/1.55    inference(avatar_split_clause,[],[f1075,f433,f1084])).
% 9.30/1.55  fof(f1075,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),sK2) | spl7_35),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f435,f229])).
% 9.30/1.55  fof(f1082,plain,(
% 9.30/1.55    ~spl7_87 | spl7_35),
% 9.30/1.55    inference(avatar_split_clause,[],[f1076,f433,f1079])).
% 9.30/1.55  fof(f1074,plain,(
% 9.30/1.55    spl7_86 | ~spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1068,f718,f1070])).
% 9.30/1.55  fof(f1068,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK1) | ~spl7_54),
% 9.30/1.55    inference(resolution,[],[f720,f82])).
% 9.30/1.55  fof(f720,plain,(
% 9.30/1.55    v1_xboole_0(u1_pre_topc(sK1)) | ~spl7_54),
% 9.30/1.55    inference(avatar_component_clause,[],[f718])).
% 9.30/1.55  fof(f1073,plain,(
% 9.30/1.55    spl7_86 | ~spl7_54),
% 9.30/1.55    inference(avatar_split_clause,[],[f1065,f718,f1070])).
% 9.30/1.55  fof(f1065,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK1) | ~spl7_54),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f720,f82])).
% 9.30/1.55  fof(f1056,plain,(
% 9.30/1.55    ~spl7_40 | ~spl7_39 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38),
% 9.30/1.55    inference(avatar_split_clause,[],[f1055,f464,f460,f405,f373,f321,f205,f182,f177,f172,f468,f472])).
% 9.30/1.55  fof(f1055,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1054,f323])).
% 9.30/1.55  fof(f1054,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1053,f461])).
% 9.30/1.55  fof(f1053,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1052,f184])).
% 9.30/1.55  fof(f1052,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_9 | ~spl7_10 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1045,f179])).
% 9.30/1.55  fof(f1051,plain,(
% 9.30/1.55    ~spl7_40 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_15 | ~spl7_25 | ~spl7_28 | ~spl7_32 | ~spl7_37 | spl7_38 | ~spl7_39),
% 9.30/1.55    inference(avatar_split_clause,[],[f1050,f468,f464,f460,f405,f373,f321,f205,f182,f177,f172,f472])).
% 9.30/1.55  fof(f1041,plain,(
% 9.30/1.55    ~spl7_34 | ~spl7_35 | ~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | spl7_36),
% 9.30/1.55    inference(avatar_split_clause,[],[f1040,f437,f425,f405,f373,f326,f205,f192,f187,f172,f433,f429])).
% 9.30/1.55  fof(f1040,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_9 | ~spl7_12 | ~spl7_13 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1039,f194])).
% 9.30/1.55  fof(f1039,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_12 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1038,f189])).
% 9.30/1.55  fof(f1038,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32 | ~spl7_33 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1037,f328])).
% 9.30/1.55  fof(f1037,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | ~spl7_33 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1036,f426])).
% 9.30/1.55  fof(f1036,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1035,f174])).
% 9.30/1.55  fof(f1035,plain,(
% 9.30/1.55    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_15 | ~spl7_28 | ~spl7_32 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1034,f375])).
% 9.30/1.55  fof(f1034,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_15 | ~spl7_32 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1033,f407])).
% 9.30/1.55  fof(f1033,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_15 | spl7_36)),
% 9.30/1.55    inference(subsumption_resolution,[],[f1031,f439])).
% 9.30/1.55  fof(f439,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_36),
% 9.30/1.55    inference(avatar_component_clause,[],[f437])).
% 9.30/1.55  fof(f1009,plain,(
% 9.30/1.55    ~spl7_85 | ~spl7_32 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f1003,f727,f405,f1006])).
% 9.30/1.55  fof(f1006,plain,(
% 9.30/1.55    spl7_85 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 9.30/1.55  fof(f1003,plain,(
% 9.30/1.55    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_32 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f407,f728,f92])).
% 9.30/1.55  fof(f728,plain,(
% 9.30/1.55    ~v1_xboole_0(sK2) | spl7_56),
% 9.30/1.55    inference(avatar_component_clause,[],[f727])).
% 9.30/1.55  fof(f992,plain,(
% 9.30/1.55    ~spl7_14 | ~spl7_71 | ~spl7_76),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f991])).
% 9.30/1.55  fof(f991,plain,(
% 9.30/1.55    $false | (~spl7_14 | ~spl7_71 | ~spl7_76)),
% 9.30/1.55    inference(subsumption_resolution,[],[f990,f212])).
% 9.30/1.55  fof(f990,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k1_xboole_0) | (~spl7_71 | ~spl7_76)),
% 9.30/1.55    inference(forward_demodulation,[],[f989,f122])).
% 9.30/1.55  fof(f989,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)) | (~spl7_71 | ~spl7_76)),
% 9.30/1.55    inference(forward_demodulation,[],[f914,f889])).
% 9.30/1.55  fof(f914,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_76),
% 9.30/1.55    inference(avatar_component_clause,[],[f912])).
% 9.30/1.55  fof(f912,plain,(
% 9.30/1.55    spl7_76 <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 9.30/1.55  fof(f988,plain,(
% 9.30/1.55    spl7_15 | ~spl7_2 | ~spl7_3),
% 9.30/1.55    inference(avatar_split_clause,[],[f963,f142,f136,f205])).
% 9.30/1.55  fof(f987,plain,(
% 9.30/1.55    spl7_70 | ~spl7_58 | ~spl7_74),
% 9.30/1.55    inference(avatar_split_clause,[],[f986,f901,f746,f879])).
% 9.30/1.55  fof(f986,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | (~spl7_58 | ~spl7_74)),
% 9.30/1.55    inference(forward_demodulation,[],[f903,f748])).
% 9.30/1.55  fof(f985,plain,(
% 9.30/1.55    spl7_69 | spl7_70 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).
% 9.30/1.55  fof(f984,plain,(
% 9.30/1.55    ~spl7_81 | ~spl7_84 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | spl7_38 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f979,f746,f464,f197,f192,f187,f182,f177,f172,f167,f162,f981,f959])).
% 9.30/1.55  fof(f979,plain,(
% 9.30/1.55    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | spl7_38 | ~spl7_58)),
% 9.30/1.55    inference(forward_demodulation,[],[f978,f748])).
% 9.30/1.55  fof(f978,plain,(
% 9.30/1.55    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | spl7_38 | ~spl7_58)),
% 9.30/1.55    inference(subsumption_resolution,[],[f977,f230])).
% 9.30/1.55  fof(f977,plain,(
% 9.30/1.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_38 | ~spl7_58)),
% 9.30/1.55    inference(forward_demodulation,[],[f929,f748])).
% 9.30/1.55  fof(f929,plain,(
% 9.30/1.55    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_38 | ~spl7_58)),
% 9.30/1.55    inference(forward_demodulation,[],[f928,f748])).
% 9.30/1.55  fof(f928,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f927,f194])).
% 9.30/1.55  fof(f927,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f926,f189])).
% 9.30/1.55  fof(f926,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f925,f184])).
% 9.30/1.55  fof(f925,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f924,f179])).
% 9.30/1.55  fof(f924,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f923,f169])).
% 9.30/1.55  fof(f923,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_7 | ~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f922,f164])).
% 9.30/1.55  fof(f922,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f675,f174])).
% 9.30/1.55  fof(f675,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl7_38),
% 9.30/1.55    inference(resolution,[],[f466,f127])).
% 9.30/1.55  fof(f975,plain,(
% 9.30/1.55    ~spl7_83 | spl7_36 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f970,f746,f437,f972])).
% 9.30/1.55  fof(f970,plain,(
% 9.30/1.55    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl7_36 | ~spl7_58)),
% 9.30/1.55    inference(forward_demodulation,[],[f439,f748])).
% 9.30/1.55  fof(f969,plain,(
% 9.30/1.55    spl7_82 | ~spl7_2 | ~spl7_3 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f964,f746,f142,f136,f966])).
% 9.30/1.55  fof(f962,plain,(
% 9.30/1.55    ~spl7_81 | spl7_1 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f957,f746,f132,f959])).
% 9.30/1.55  fof(f957,plain,(
% 9.30/1.55    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl7_1 | ~spl7_58)),
% 9.30/1.55    inference(forward_demodulation,[],[f134,f748])).
% 9.30/1.55  fof(f956,plain,(
% 9.30/1.55    spl7_80 | ~spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f951,f875,f746,f142,f136,f953])).
% 9.30/1.55  fof(f951,plain,(
% 9.30/1.55    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_58 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f950,f748])).
% 9.30/1.55  fof(f950,plain,(
% 9.30/1.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_3 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f949,f144])).
% 9.30/1.55  fof(f949,plain,(
% 9.30/1.55    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_2 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f137,f877])).
% 9.30/1.55  fof(f948,plain,(
% 9.30/1.55    ~spl7_79 | spl7_36 | ~spl7_58 | ~spl7_69),
% 9.30/1.55    inference(avatar_split_clause,[],[f943,f875,f746,f437,f945])).
% 9.30/1.55  fof(f945,plain,(
% 9.30/1.55    spl7_79 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 9.30/1.55  fof(f943,plain,(
% 9.30/1.55    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_36 | ~spl7_58 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f942,f748])).
% 9.30/1.55  fof(f942,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl7_36 | ~spl7_69)),
% 9.30/1.55    inference(forward_demodulation,[],[f439,f877])).
% 9.30/1.55  fof(f941,plain,(
% 9.30/1.55    ~spl7_39 | spl7_63 | ~spl7_69),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f940])).
% 9.30/1.55  fof(f940,plain,(
% 9.30/1.55    $false | (~spl7_39 | spl7_63 | ~spl7_69)),
% 9.30/1.55    inference(subsumption_resolution,[],[f939,f790])).
% 9.30/1.55  fof(f790,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl7_63),
% 9.30/1.55    inference(avatar_component_clause,[],[f788])).
% 9.30/1.55  fof(f937,plain,(
% 9.30/1.55    spl7_78 | ~spl7_69 | ~spl7_71),
% 9.30/1.55    inference(avatar_split_clause,[],[f932,f887,f875,f934])).
% 9.30/1.55  fof(f934,plain,(
% 9.30/1.55    spl7_78 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 9.30/1.55  fof(f932,plain,(
% 9.30/1.55    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl7_69 | ~spl7_71)),
% 9.30/1.55    inference(forward_demodulation,[],[f889,f877])).
% 9.30/1.55  fof(f920,plain,(
% 9.30/1.55    spl7_71 | spl7_77 | ~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32),
% 9.30/1.55    inference(avatar_split_clause,[],[f883,f405,f373,f157,f142,f917,f887])).
% 9.30/1.55  fof(f883,plain,(
% 9.30/1.55    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f871,f407])).
% 9.30/1.55  fof(f871,plain,(
% 9.30/1.55    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_3 | ~spl7_6 | ~spl7_28)),
% 9.30/1.55    inference(resolution,[],[f414,f375])).
% 9.30/1.55  fof(f915,plain,(
% 9.30/1.55    spl7_56 | spl7_76 | ~spl7_29),
% 9.30/1.55    inference(avatar_split_clause,[],[f809,f385,f912,f727])).
% 9.30/1.55  fof(f809,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_xboole_0(sK2) | ~spl7_29),
% 9.30/1.55    inference(resolution,[],[f387,f277])).
% 9.30/1.55  fof(f910,plain,(
% 9.30/1.55    spl7_56 | spl7_75 | ~spl7_29 | ~spl7_65),
% 9.30/1.55    inference(avatar_split_clause,[],[f905,f824,f385,f907,f727])).
% 9.30/1.55  fof(f907,plain,(
% 9.30/1.55    spl7_75 <=> r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 9.30/1.55  fof(f905,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v1_xboole_0(sK2) | (~spl7_29 | ~spl7_65)),
% 9.30/1.55    inference(forward_demodulation,[],[f809,f826])).
% 9.30/1.55  fof(f826,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK0) | ~spl7_65),
% 9.30/1.55    inference(avatar_component_clause,[],[f824])).
% 9.30/1.55  fof(f904,plain,(
% 9.30/1.55    spl7_69 | spl7_74 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8),
% 9.30/1.55    inference(avatar_split_clause,[],[f872,f167,f162,f157,f142,f901,f875])).
% 9.30/1.55  fof(f899,plain,(
% 9.30/1.55    spl7_71 | spl7_73 | ~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32 | ~spl7_65),
% 9.30/1.55    inference(avatar_split_clause,[],[f884,f824,f405,f373,f157,f142,f896,f887])).
% 9.30/1.55  fof(f896,plain,(
% 9.30/1.55    spl7_73 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 9.30/1.55  fof(f884,plain,(
% 9.30/1.55    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32 | ~spl7_65)),
% 9.30/1.55    inference(forward_demodulation,[],[f883,f826])).
% 9.30/1.55  fof(f894,plain,(
% 9.30/1.55    spl7_71 | spl7_72 | ~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32 | ~spl7_58 | ~spl7_65),
% 9.30/1.55    inference(avatar_split_clause,[],[f885,f824,f746,f405,f373,f157,f142,f891,f887])).
% 9.30/1.55  fof(f891,plain,(
% 9.30/1.55    spl7_72 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 9.30/1.55  fof(f885,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k1_xboole_0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_3 | ~spl7_6 | ~spl7_28 | ~spl7_32 | ~spl7_58 | ~spl7_65)),
% 9.30/1.55    inference(forward_demodulation,[],[f884,f748])).
% 9.30/1.55  fof(f882,plain,(
% 9.30/1.55    spl7_69 | spl7_70 | ~spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_58),
% 9.30/1.55    inference(avatar_split_clause,[],[f873,f746,f167,f162,f157,f142,f879,f875])).
% 9.30/1.55  fof(f868,plain,(
% 9.30/1.55    spl7_66 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f834,f709,f844])).
% 9.30/1.55  fof(f844,plain,(
% 9.30/1.55    spl7_66 <=> r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 9.30/1.55  fof(f834,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | spl7_52),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f216,f710,f277])).
% 9.30/1.55  fof(f867,plain,(
% 9.30/1.55    ~spl7_68 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f836,f709,f197,f863])).
% 9.30/1.55  fof(f863,plain,(
% 9.30/1.55    spl7_68 <=> r1_tarski(u1_pre_topc(sK0),k1_xboole_0)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 9.30/1.55  fof(f836,plain,(
% 9.30/1.55    ~r1_tarski(u1_pre_topc(sK0),k1_xboole_0) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f212,f710,f277])).
% 9.30/1.55  fof(f866,plain,(
% 9.30/1.55    ~spl7_68 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f861,f709,f197,f863])).
% 9.30/1.55  fof(f861,plain,(
% 9.30/1.55    ~r1_tarski(u1_pre_topc(sK0),k1_xboole_0) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f837,f571])).
% 9.30/1.55  fof(f837,plain,(
% 9.30/1.55    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK0),sK6(k1_xboole_0,X0))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f551,f710,f277])).
% 9.30/1.55  fof(f860,plain,(
% 9.30/1.55    ~spl7_67 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f838,f709,f197,f851])).
% 9.30/1.55  fof(f851,plain,(
% 9.30/1.55    spl7_67 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 9.30/1.55  fof(f838,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f710,f335])).
% 9.30/1.55  fof(f859,plain,(
% 9.30/1.55    ~spl7_67 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f858,f709,f197,f851])).
% 9.30/1.55  fof(f858,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f839,f122])).
% 9.30/1.55  fof(f839,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f199,f710,f92])).
% 9.30/1.55  fof(f857,plain,(
% 9.30/1.55    ~spl7_67 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f856,f709,f197,f851])).
% 9.30/1.55  fof(f856,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f855,f122])).
% 9.30/1.55  fof(f855,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f840,f348])).
% 9.30/1.55  fof(f840,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f332,f710,f92])).
% 9.30/1.55  fof(f854,plain,(
% 9.30/1.55    ~spl7_67 | ~spl7_14 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f849,f709,f197,f851])).
% 9.30/1.55  fof(f849,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f848,f122])).
% 9.30/1.55  fof(f848,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(forward_demodulation,[],[f841,f571])).
% 9.30/1.55  fof(f841,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))) ) | (~spl7_14 | spl7_52)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f558,f710,f92])).
% 9.30/1.55  fof(f847,plain,(
% 9.30/1.55    spl7_66 | spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f842,f709,f844])).
% 9.30/1.55  fof(f842,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | spl7_52),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f710,f91])).
% 9.30/1.55  fof(f828,plain,(
% 9.30/1.55    spl7_65 | ~spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f822,f709,f824])).
% 9.30/1.55  fof(f822,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK0) | ~spl7_52),
% 9.30/1.55    inference(resolution,[],[f711,f82])).
% 9.30/1.55  fof(f711,plain,(
% 9.30/1.55    v1_xboole_0(u1_pre_topc(sK0)) | ~spl7_52),
% 9.30/1.55    inference(avatar_component_clause,[],[f709])).
% 9.30/1.55  fof(f827,plain,(
% 9.30/1.55    spl7_65 | ~spl7_52),
% 9.30/1.55    inference(avatar_split_clause,[],[f819,f709,f824])).
% 9.30/1.55  fof(f819,plain,(
% 9.30/1.55    k1_xboole_0 = u1_pre_topc(sK0) | ~spl7_52),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f711,f82])).
% 9.30/1.55  fof(f805,plain,(
% 9.30/1.55    spl7_61 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f765,f727,f776])).
% 9.30/1.55  fof(f765,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),sK2) | spl7_56),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f216,f728,f277])).
% 9.30/1.55  fof(f804,plain,(
% 9.30/1.55    ~spl7_64 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f767,f727,f197,f800])).
% 9.30/1.55  fof(f767,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k1_xboole_0) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f212,f728,f277])).
% 9.30/1.55  fof(f803,plain,(
% 9.30/1.55    ~spl7_64 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f798,f727,f197,f800])).
% 9.30/1.55  fof(f798,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k1_xboole_0) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f768,f571])).
% 9.30/1.55  fof(f768,plain,(
% 9.30/1.55    ( ! [X0] : (~r1_tarski(sK2,sK6(k1_xboole_0,X0))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f551,f728,f277])).
% 9.30/1.55  fof(f797,plain,(
% 9.30/1.55    ~spl7_63 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f769,f727,f197,f788])).
% 9.30/1.55  fof(f769,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f728,f335])).
% 9.30/1.55  fof(f796,plain,(
% 9.30/1.55    ~spl7_63 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f795,f727,f197,f788])).
% 9.30/1.55  fof(f795,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f770,f122])).
% 9.30/1.55  fof(f770,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f199,f728,f92])).
% 9.30/1.55  fof(f794,plain,(
% 9.30/1.55    ~spl7_63 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f793,f727,f197,f788])).
% 9.30/1.55  fof(f793,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f792,f122])).
% 9.30/1.55  fof(f792,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f771,f348])).
% 9.30/1.55  fof(f771,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK6(X1,k1_xboole_0))))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f332,f728,f92])).
% 9.30/1.55  fof(f791,plain,(
% 9.30/1.55    ~spl7_63 | ~spl7_14 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f786,f727,f197,f788])).
% 9.30/1.55  fof(f786,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f785,f122])).
% 9.30/1.55  fof(f785,plain,(
% 9.30/1.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(forward_demodulation,[],[f772,f571])).
% 9.30/1.55  fof(f772,plain,(
% 9.30/1.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK6(k1_xboole_0,X1))))) ) | (~spl7_14 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f558,f728,f92])).
% 9.30/1.55  fof(f784,plain,(
% 9.30/1.55    ~spl7_62 | ~spl7_7 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f773,f727,f162,f781])).
% 9.30/1.55  fof(f773,plain,(
% 9.30/1.55    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl7_7 | spl7_56)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f164,f728,f92])).
% 9.30/1.55  fof(f779,plain,(
% 9.30/1.55    spl7_61 | spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f774,f727,f776])).
% 9.30/1.55  fof(f774,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),sK2) | spl7_56),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f728,f91])).
% 9.30/1.55  fof(f764,plain,(
% 9.30/1.55    spl7_60 | spl7_39),
% 9.30/1.55    inference(avatar_split_clause,[],[f753,f468,f760])).
% 9.30/1.55  fof(f760,plain,(
% 9.30/1.55    spl7_60 <=> r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 9.30/1.55  fof(f753,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2) | spl7_39),
% 9.30/1.55    inference(resolution,[],[f470,f229])).
% 9.30/1.55  fof(f763,plain,(
% 9.30/1.55    spl7_60 | spl7_39),
% 9.30/1.55    inference(avatar_split_clause,[],[f751,f468,f760])).
% 9.30/1.55  fof(f751,plain,(
% 9.30/1.55    r2_hidden(sK5(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),sK2) | spl7_39),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f470,f229])).
% 9.30/1.55  fof(f758,plain,(
% 9.30/1.55    ~spl7_59 | spl7_39),
% 9.30/1.55    inference(avatar_split_clause,[],[f752,f468,f755])).
% 9.30/1.55  fof(f755,plain,(
% 9.30/1.55    spl7_59 <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 9.30/1.55  fof(f752,plain,(
% 9.30/1.55    ~r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | spl7_39),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f470,f101])).
% 9.30/1.55  fof(f750,plain,(
% 9.30/1.55    spl7_58 | ~spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f744,f727,f746])).
% 9.30/1.55  fof(f744,plain,(
% 9.30/1.55    k1_xboole_0 = sK2 | ~spl7_56),
% 9.30/1.55    inference(resolution,[],[f729,f82])).
% 9.30/1.55  fof(f729,plain,(
% 9.30/1.55    v1_xboole_0(sK2) | ~spl7_56),
% 9.30/1.55    inference(avatar_component_clause,[],[f727])).
% 9.30/1.55  fof(f749,plain,(
% 9.30/1.55    spl7_58 | ~spl7_56),
% 9.30/1.55    inference(avatar_split_clause,[],[f741,f727,f746])).
% 9.30/1.55  fof(f741,plain,(
% 9.30/1.55    k1_xboole_0 = sK2 | ~spl7_56),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f729,f82])).
% 9.30/1.55  fof(f734,plain,(
% 9.30/1.55    spl7_56 | spl7_57 | ~spl7_16),
% 9.30/1.55    inference(avatar_split_clause,[],[f705,f221,f731,f727])).
% 9.30/1.55  fof(f705,plain,(
% 9.30/1.55    r2_hidden(sK4(sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | v1_xboole_0(sK2) | ~spl7_16),
% 9.30/1.55    inference(resolution,[],[f277,f223])).
% 9.30/1.55  fof(f725,plain,(
% 9.30/1.55    spl7_54 | spl7_55 | ~spl7_49),
% 9.30/1.55    inference(avatar_split_clause,[],[f704,f620,f722,f718])).
% 9.30/1.55  fof(f704,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_pre_topc(sK1)) | ~spl7_49),
% 9.30/1.55    inference(resolution,[],[f277,f622])).
% 9.30/1.55  fof(f716,plain,(
% 9.30/1.55    spl7_52 | spl7_53 | ~spl7_46),
% 9.30/1.55    inference(avatar_split_clause,[],[f703,f587,f713,f709])).
% 9.30/1.55  fof(f703,plain,(
% 9.30/1.55    r2_hidden(sK4(u1_pre_topc(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_pre_topc(sK0)) | ~spl7_46),
% 9.30/1.55    inference(resolution,[],[f277,f589])).
% 9.30/1.55  fof(f684,plain,(
% 9.30/1.55    ~spl7_40 | ~spl7_39 | ~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_38),
% 9.30/1.55    inference(avatar_split_clause,[],[f683,f464,f192,f187,f182,f177,f172,f167,f162,f132,f468,f472])).
% 9.30/1.55  fof(f683,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_13 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f682,f194])).
% 9.30/1.55  fof(f682,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f681,f189])).
% 9.30/1.55  fof(f681,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f680,f184])).
% 9.30/1.55  fof(f680,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f679,f179])).
% 9.30/1.55  fof(f679,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_7 | ~spl7_8 | ~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f678,f169])).
% 9.30/1.55  fof(f678,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_7 | ~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f677,f164])).
% 9.30/1.55  fof(f677,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | ~spl7_9 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f676,f174])).
% 9.30/1.55  fof(f676,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_1 | spl7_38)),
% 9.30/1.55    inference(subsumption_resolution,[],[f675,f133])).
% 9.30/1.55  fof(f644,plain,(
% 9.30/1.55    spl7_51 | ~spl7_33),
% 9.30/1.55    inference(avatar_split_clause,[],[f633,f425,f640])).
% 9.30/1.55  fof(f633,plain,(
% 9.30/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_33),
% 9.30/1.55    inference(resolution,[],[f426,f83])).
% 9.30/1.55  fof(f643,plain,(
% 9.30/1.55    spl7_51 | ~spl7_33),
% 9.30/1.55    inference(avatar_split_clause,[],[f630,f425,f640])).
% 9.30/1.55  fof(f630,plain,(
% 9.30/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl7_33),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f426,f83])).
% 9.30/1.55  fof(f638,plain,(
% 9.30/1.55    spl7_50 | ~spl7_26 | ~spl7_33),
% 9.30/1.55    inference(avatar_split_clause,[],[f632,f425,f326,f635])).
% 9.30/1.55  fof(f632,plain,(
% 9.30/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_26 | ~spl7_33)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f328,f426,f85])).
% 9.30/1.55  fof(f625,plain,(
% 9.30/1.55    spl7_49 | ~spl7_20),
% 9.30/1.55    inference(avatar_split_clause,[],[f618,f262,f620])).
% 9.30/1.55  fof(f618,plain,(
% 9.30/1.55    r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_20),
% 9.30/1.55    inference(resolution,[],[f264,f100])).
% 9.30/1.55  fof(f624,plain,(
% 9.30/1.55    spl7_33 | ~spl7_20),
% 9.30/1.55    inference(avatar_split_clause,[],[f615,f262,f425])).
% 9.30/1.55  fof(f615,plain,(
% 9.30/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_20),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f264,f94])).
% 9.30/1.55  fof(f623,plain,(
% 9.30/1.55    spl7_49 | ~spl7_20),
% 9.30/1.55    inference(avatar_split_clause,[],[f617,f262,f620])).
% 9.30/1.55  fof(f617,plain,(
% 9.30/1.55    r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_20),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f264,f100])).
% 9.30/1.55  fof(f614,plain,(
% 9.30/1.55    spl7_48 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f603,f460,f610])).
% 9.30/1.55  fof(f603,plain,(
% 9.30/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~spl7_37),
% 9.30/1.55    inference(resolution,[],[f461,f83])).
% 9.30/1.55  fof(f613,plain,(
% 9.30/1.55    spl7_48 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f600,f460,f610])).
% 9.30/1.55  fof(f600,plain,(
% 9.30/1.55    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~spl7_37),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f461,f83])).
% 9.30/1.55  fof(f608,plain,(
% 9.30/1.55    spl7_47 | ~spl7_25 | ~spl7_37),
% 9.30/1.55    inference(avatar_split_clause,[],[f602,f460,f321,f605])).
% 9.30/1.55  fof(f602,plain,(
% 9.30/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | (~spl7_25 | ~spl7_37)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f323,f461,f85])).
% 9.30/1.55  fof(f592,plain,(
% 9.30/1.55    spl7_46 | ~spl7_19),
% 9.30/1.55    inference(avatar_split_clause,[],[f585,f257,f587])).
% 9.30/1.55  fof(f585,plain,(
% 9.30/1.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_19),
% 9.30/1.55    inference(resolution,[],[f259,f100])).
% 9.30/1.55  fof(f591,plain,(
% 9.30/1.55    spl7_37 | ~spl7_19),
% 9.30/1.55    inference(avatar_split_clause,[],[f582,f257,f460])).
% 9.30/1.55  fof(f582,plain,(
% 9.30/1.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_19),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f259,f94])).
% 9.30/1.55  fof(f590,plain,(
% 9.30/1.55    spl7_46 | ~spl7_19),
% 9.30/1.55    inference(avatar_split_clause,[],[f584,f257,f587])).
% 9.30/1.55  fof(f584,plain,(
% 9.30/1.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_19),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f259,f100])).
% 9.30/1.55  fof(f539,plain,(
% 9.30/1.55    spl7_45 | ~spl7_37 | ~spl7_25),
% 9.30/1.55    inference(avatar_split_clause,[],[f504,f321,f460,f536])).
% 9.30/1.55  fof(f536,plain,(
% 9.30/1.55    spl7_45 <=> v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 9.30/1.55  fof(f504,plain,(
% 9.30/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl7_25),
% 9.30/1.55    inference(resolution,[],[f323,f84])).
% 9.30/1.55  fof(f534,plain,(
% 9.30/1.55    ~spl7_19 | spl7_37),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f533])).
% 9.30/1.55  fof(f533,plain,(
% 9.30/1.55    $false | (~spl7_19 | spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f530,f259])).
% 9.30/1.55  fof(f530,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl7_37),
% 9.30/1.55    inference(resolution,[],[f462,f94])).
% 9.30/1.55  fof(f462,plain,(
% 9.30/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl7_37),
% 9.30/1.55    inference(avatar_component_clause,[],[f460])).
% 9.30/1.55  fof(f532,plain,(
% 9.30/1.55    ~spl7_19 | spl7_37),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f531])).
% 9.30/1.55  fof(f531,plain,(
% 9.30/1.55    $false | (~spl7_19 | spl7_37)),
% 9.30/1.55    inference(subsumption_resolution,[],[f529,f259])).
% 9.30/1.55  fof(f529,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl7_37),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f462,f94])).
% 9.30/1.55  fof(f528,plain,(
% 9.30/1.55    spl7_44 | ~spl7_33 | ~spl7_26),
% 9.30/1.55    inference(avatar_split_clause,[],[f515,f326,f425,f525])).
% 9.30/1.55  fof(f515,plain,(
% 9.30/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_26),
% 9.30/1.55    inference(resolution,[],[f328,f84])).
% 9.30/1.55  fof(f523,plain,(
% 9.30/1.55    ~spl7_20 | spl7_33),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f522])).
% 9.30/1.55  fof(f522,plain,(
% 9.30/1.55    $false | (~spl7_20 | spl7_33)),
% 9.30/1.55    inference(subsumption_resolution,[],[f519,f264])).
% 9.30/1.55  fof(f519,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl7_33),
% 9.30/1.55    inference(resolution,[],[f427,f94])).
% 9.30/1.55  fof(f427,plain,(
% 9.30/1.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl7_33),
% 9.30/1.55    inference(avatar_component_clause,[],[f425])).
% 9.30/1.55  fof(f521,plain,(
% 9.30/1.55    ~spl7_20 | spl7_33),
% 9.30/1.55    inference(avatar_contradiction_clause,[],[f520])).
% 9.30/1.55  fof(f520,plain,(
% 9.30/1.55    $false | (~spl7_20 | spl7_33)),
% 9.30/1.55    inference(subsumption_resolution,[],[f518,f264])).
% 9.30/1.55  fof(f518,plain,(
% 9.30/1.55    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl7_33),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f427,f94])).
% 9.30/1.55  fof(f514,plain,(
% 9.30/1.55    spl7_43 | ~spl7_14 | ~spl7_18 | ~spl7_42),
% 9.30/1.55    inference(avatar_split_clause,[],[f513,f498,f248,f197,f508])).
% 9.30/1.55  fof(f498,plain,(
% 9.30/1.55    spl7_42 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 9.30/1.55  fof(f513,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_18 | ~spl7_42)),
% 9.30/1.55    inference(subsumption_resolution,[],[f512,f250])).
% 9.30/1.55  fof(f512,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_42)),
% 9.30/1.55    inference(subsumption_resolution,[],[f506,f279])).
% 9.30/1.55  fof(f506,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v4_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_42),
% 9.30/1.55    inference(resolution,[],[f500,f95])).
% 9.30/1.55  fof(f500,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl7_42),
% 9.30/1.55    inference(avatar_component_clause,[],[f498])).
% 9.30/1.55  fof(f511,plain,(
% 9.30/1.55    spl7_43 | ~spl7_14 | ~spl7_18 | ~spl7_42),
% 9.30/1.55    inference(avatar_split_clause,[],[f505,f498,f248,f197,f508])).
% 9.30/1.55  fof(f505,plain,(
% 9.30/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl7_14 | ~spl7_18 | ~spl7_42)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f250,f279,f500,f95])).
% 9.30/1.55  fof(f501,plain,(
% 9.30/1.55    spl7_42 | ~spl7_14),
% 9.30/1.55    inference(avatar_split_clause,[],[f491,f197,f498])).
% 9.30/1.55  fof(f491,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl7_14),
% 9.30/1.55    inference(superposition,[],[f368,f348])).
% 9.30/1.55  fof(f368,plain,(
% 9.30/1.55    ( ! [X0] : (v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0)) )),
% 9.30/1.55    inference(subsumption_resolution,[],[f367,f109])).
% 9.30/1.55  fof(f109,plain,(
% 9.30/1.55    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 9.30/1.55    inference(cnf_transformation,[],[f65])).
% 9.30/1.55  fof(f367,plain,(
% 9.30/1.55    ( ! [X0] : (v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0) | ~v1_funct_1(sK6(k1_xboole_0,X0))) )),
% 9.30/1.55    inference(subsumption_resolution,[],[f366,f235])).
% 9.30/1.55  fof(f366,plain,(
% 9.30/1.55    ( ! [X0] : (v1_partfun1(sK6(k1_xboole_0,X0),k1_xboole_0) | ~m1_subset_1(sK6(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK6(k1_xboole_0,X0))) )),
% 9.30/1.55    inference(resolution,[],[f202,f110])).
% 9.30/1.55  fof(f202,plain,(
% 9.30/1.55    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2)) )),
% 9.30/1.55    inference(forward_demodulation,[],[f126,f123])).
% 9.30/1.55  fof(f126,plain,(
% 9.30/1.55    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 9.30/1.55    inference(duplicate_literal_removal,[],[f124])).
% 9.30/1.55  fof(f124,plain,(
% 9.30/1.55    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 9.30/1.55    inference(equality_resolution,[],[f115])).
% 9.30/1.55  fof(f115,plain,(
% 9.30/1.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 9.30/1.55    inference(cnf_transformation,[],[f41])).
% 9.30/1.55  fof(f496,plain,(
% 9.30/1.55    spl7_41 | ~spl7_14),
% 9.30/1.55    inference(avatar_split_clause,[],[f489,f197,f493])).
% 9.30/1.55  fof(f489,plain,(
% 9.30/1.55    v1_funct_1(k1_xboole_0) | ~spl7_14),
% 9.30/1.55    inference(superposition,[],[f109,f348])).
% 9.30/1.55  fof(f475,plain,(
% 9.30/1.55    ~spl7_37 | ~spl7_38 | ~spl7_39 | ~spl7_40 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | spl7_15 | ~spl7_25),
% 9.30/1.55    inference(avatar_split_clause,[],[f458,f321,f205,f182,f177,f157,f152,f147,f142,f472,f468,f464,f460])).
% 9.30/1.55  fof(f458,plain,(
% 9.30/1.55    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | spl7_15 | ~spl7_25)),
% 9.30/1.55    inference(forward_demodulation,[],[f457,f144])).
% 9.30/1.55  fof(f457,plain,(
% 9.30/1.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | spl7_15 | ~spl7_25)),
% 9.30/1.55    inference(forward_demodulation,[],[f456,f144])).
% 9.30/1.55  fof(f456,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_10 | ~spl7_11 | spl7_15 | ~spl7_25)),
% 9.30/1.55    inference(subsumption_resolution,[],[f455,f207])).
% 9.30/1.55  fof(f440,plain,(
% 9.30/1.55    ~spl7_33 | ~spl7_34 | ~spl7_35 | ~spl7_36 | ~spl7_9 | ~spl7_12 | ~spl7_13 | spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32),
% 9.30/1.55    inference(avatar_split_clause,[],[f423,f405,f373,f326,f205,f192,f187,f172,f437,f433,f429,f425])).
% 9.30/1.55  fof(f423,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_9 | ~spl7_12 | ~spl7_13 | spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f422,f194])).
% 9.30/1.55  fof(f422,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl7_9 | ~spl7_12 | spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f421,f189])).
% 9.30/1.55  fof(f421,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | spl7_15 | ~spl7_26 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f420,f328])).
% 9.30/1.55  fof(f420,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_9 | spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f419,f174])).
% 9.30/1.55  fof(f419,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_15 | ~spl7_28 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f418,f375])).
% 9.30/1.55  fof(f418,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl7_15 | ~spl7_32)),
% 9.30/1.55    inference(subsumption_resolution,[],[f417,f407])).
% 9.30/1.55  fof(f417,plain,(
% 9.30/1.55    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl7_15),
% 9.30/1.55    inference(resolution,[],[f127,f207])).
% 9.30/1.55  fof(f408,plain,(
% 9.30/1.55    spl7_32 | ~spl7_3 | ~spl7_4),
% 9.30/1.55    inference(avatar_split_clause,[],[f382,f147,f142,f405])).
% 9.30/1.55  fof(f382,plain,(
% 9.30/1.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl7_3 | ~spl7_4)),
% 9.30/1.55    inference(superposition,[],[f149,f144])).
% 9.30/1.55  fof(f403,plain,(
% 9.30/1.55    spl7_29 | ~spl7_3 | ~spl7_4),
% 9.30/1.55    inference(avatar_split_clause,[],[f402,f147,f142,f385])).
% 9.30/1.55  fof(f402,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_3 | ~spl7_4)),
% 9.30/1.55    inference(forward_demodulation,[],[f381,f144])).
% 9.30/1.55  fof(f381,plain,(
% 9.30/1.55    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_4),
% 9.30/1.55    inference(resolution,[],[f149,f100])).
% 9.30/1.55  fof(f401,plain,(
% 9.30/1.55    spl7_31 | ~spl7_3 | ~spl7_4),
% 9.30/1.55    inference(avatar_split_clause,[],[f396,f147,f142,f398])).
% 9.30/1.55  fof(f398,plain,(
% 9.30/1.55    spl7_31 <=> v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 9.30/1.55  fof(f396,plain,(
% 9.30/1.55    v5_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_3 | ~spl7_4)),
% 9.30/1.55    inference(forward_demodulation,[],[f377,f144])).
% 9.30/1.55  fof(f377,plain,(
% 9.30/1.55    v5_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl7_4),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f149,f113])).
% 9.30/1.55  fof(f113,plain,(
% 9.30/1.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.30/1.55    inference(cnf_transformation,[],[f39])).
% 9.30/1.55  fof(f395,plain,(
% 9.30/1.55    spl7_30 | ~spl7_3 | ~spl7_4),
% 9.30/1.55    inference(avatar_split_clause,[],[f390,f147,f142,f392])).
% 9.30/1.55  fof(f390,plain,(
% 9.30/1.55    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl7_3 | ~spl7_4)),
% 9.30/1.55    inference(forward_demodulation,[],[f378,f144])).
% 9.30/1.55  fof(f378,plain,(
% 9.30/1.55    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl7_4),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f149,f112])).
% 9.30/1.55  fof(f388,plain,(
% 9.30/1.55    spl7_29 | ~spl7_3 | ~spl7_4),
% 9.30/1.55    inference(avatar_split_clause,[],[f383,f147,f142,f385])).
% 9.30/1.55  fof(f383,plain,(
% 9.30/1.55    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl7_3 | ~spl7_4)),
% 9.30/1.55    inference(forward_demodulation,[],[f380,f144])).
% 9.30/1.55  fof(f380,plain,(
% 9.30/1.55    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl7_4),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f149,f100])).
% 9.30/1.55  fof(f376,plain,(
% 9.30/1.55    spl7_28 | ~spl7_3 | ~spl7_5),
% 9.30/1.55    inference(avatar_split_clause,[],[f371,f152,f142,f373])).
% 9.30/1.55  fof(f371,plain,(
% 9.30/1.55    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl7_3 | ~spl7_5)),
% 9.30/1.55    inference(superposition,[],[f154,f144])).
% 9.30/1.55  fof(f341,plain,(
% 9.30/1.55    spl7_27 | ~spl7_14 | ~spl7_18),
% 9.30/1.55    inference(avatar_split_clause,[],[f336,f248,f197,f338])).
% 9.30/1.55  fof(f338,plain,(
% 9.30/1.55    spl7_27 <=> v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 9.30/1.55    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 9.30/1.55  fof(f336,plain,(
% 9.30/1.55    v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | (~spl7_14 | ~spl7_18)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f250,f279,f121])).
% 9.30/1.55  fof(f121,plain,(
% 9.30/1.55    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 9.30/1.55    inference(equality_resolution,[],[f96])).
% 9.30/1.55  fof(f96,plain,(
% 9.30/1.55    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 9.30/1.55    inference(cnf_transformation,[],[f56])).
% 9.30/1.55  fof(f329,plain,(
% 9.30/1.55    spl7_26 | ~spl7_10 | ~spl7_11),
% 9.30/1.55    inference(avatar_split_clause,[],[f317,f182,f177,f326])).
% 9.30/1.55  fof(f317,plain,(
% 9.30/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_10 | ~spl7_11)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f184,f179,f85])).
% 9.30/1.55  fof(f324,plain,(
% 9.30/1.55    spl7_25 | ~spl7_12 | ~spl7_13),
% 9.30/1.55    inference(avatar_split_clause,[],[f318,f192,f187,f321])).
% 9.30/1.55  fof(f318,plain,(
% 9.30/1.55    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_12 | ~spl7_13)),
% 9.30/1.55    inference(unit_resulting_resolution,[],[f194,f189,f85])).
% 9.30/1.55  fof(f316,plain,(
% 9.30/1.55    spl7_23 | ~spl7_12 | ~spl7_13),
% 9.30/1.55    inference(avatar_split_clause,[],[f315,f192,f187,f304])).
% 9.30/1.55  fof(f315,plain,(
% 9.30/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_12 | ~spl7_13)),
% 9.30/1.55    inference(subsumption_resolution,[],[f302,f189])).
% 9.30/1.55  fof(f302,plain,(
% 9.30/1.55    ~l1_pre_topc(sK0) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl7_13),
% 9.30/1.55    inference(resolution,[],[f84,f194])).
% 9.30/1.55  fof(f314,plain,(
% 9.30/1.55    spl7_24 | ~spl7_10 | ~spl7_11),
% 9.30/1.55    inference(avatar_split_clause,[],[f313,f182,f177,f309])).
% 9.30/1.55  fof(f313,plain,(
% 9.30/1.55    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_10 | ~spl7_11)),
% 9.30/1.56    inference(subsumption_resolution,[],[f301,f179])).
% 9.30/1.56  fof(f301,plain,(
% 9.30/1.56    ~l1_pre_topc(sK1) | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl7_11),
% 9.30/1.56    inference(resolution,[],[f84,f184])).
% 9.30/1.56  fof(f312,plain,(
% 9.30/1.56    spl7_24 | ~spl7_10 | ~spl7_11),
% 9.30/1.56    inference(avatar_split_clause,[],[f299,f182,f177,f309])).
% 9.30/1.56  fof(f299,plain,(
% 9.30/1.56    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl7_10 | ~spl7_11)),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f184,f179,f84])).
% 9.30/1.56  fof(f307,plain,(
% 9.30/1.56    spl7_23 | ~spl7_12 | ~spl7_13),
% 9.30/1.56    inference(avatar_split_clause,[],[f300,f192,f187,f304])).
% 9.30/1.56  fof(f300,plain,(
% 9.30/1.56    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl7_12 | ~spl7_13)),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f194,f189,f84])).
% 9.30/1.56  fof(f295,plain,(
% 9.30/1.56    spl7_22 | ~spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f289,f162,f292])).
% 9.30/1.56  fof(f292,plain,(
% 9.30/1.56    spl7_22 <=> v5_relat_1(sK2,u1_struct_0(sK1))),
% 9.30/1.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 9.30/1.56  fof(f289,plain,(
% 9.30/1.56    v5_relat_1(sK2,u1_struct_0(sK1)) | ~spl7_7),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f164,f113])).
% 9.30/1.56  fof(f286,plain,(
% 9.30/1.56    spl7_21 | ~spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f280,f162,f283])).
% 9.30/1.56  fof(f280,plain,(
% 9.30/1.56    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl7_7),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f164,f112])).
% 9.30/1.56  fof(f267,plain,(
% 9.30/1.56    spl7_19 | ~spl7_12),
% 9.30/1.56    inference(avatar_split_clause,[],[f255,f187,f257])).
% 9.30/1.56  fof(f255,plain,(
% 9.30/1.56    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl7_12),
% 9.30/1.56    inference(resolution,[],[f83,f189])).
% 9.30/1.56  fof(f266,plain,(
% 9.30/1.56    spl7_20 | ~spl7_10),
% 9.30/1.56    inference(avatar_split_clause,[],[f254,f177,f262])).
% 9.30/1.56  fof(f254,plain,(
% 9.30/1.56    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl7_10),
% 9.30/1.56    inference(resolution,[],[f83,f179])).
% 9.30/1.56  fof(f265,plain,(
% 9.30/1.56    spl7_20 | ~spl7_10),
% 9.30/1.56    inference(avatar_split_clause,[],[f252,f177,f262])).
% 9.30/1.56  fof(f252,plain,(
% 9.30/1.56    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl7_10),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f179,f83])).
% 9.30/1.56  fof(f260,plain,(
% 9.30/1.56    spl7_19 | ~spl7_12),
% 9.30/1.56    inference(avatar_split_clause,[],[f253,f187,f257])).
% 9.30/1.56  fof(f253,plain,(
% 9.30/1.56    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl7_12),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f189,f83])).
% 9.30/1.56  fof(f251,plain,(
% 9.30/1.56    spl7_18 | ~spl7_14),
% 9.30/1.56    inference(avatar_split_clause,[],[f239,f197,f248])).
% 9.30/1.56  fof(f239,plain,(
% 9.30/1.56    v1_relat_1(k1_xboole_0) | ~spl7_14),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f230,f111])).
% 9.30/1.56  fof(f111,plain,(
% 9.30/1.56    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 9.30/1.56    inference(cnf_transformation,[],[f38])).
% 9.30/1.56  fof(f38,plain,(
% 9.30/1.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.30/1.56    inference(ennf_transformation,[],[f10])).
% 9.30/1.56  fof(f10,axiom,(
% 9.30/1.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 9.30/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 9.30/1.56  fof(f246,plain,(
% 9.30/1.56    spl7_17 | ~spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f240,f162,f243])).
% 9.30/1.56  fof(f240,plain,(
% 9.30/1.56    v1_relat_1(sK2) | ~spl7_7),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f164,f111])).
% 9.30/1.56  fof(f225,plain,(
% 9.30/1.56    spl7_16 | ~spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f219,f162,f221])).
% 9.30/1.56  fof(f219,plain,(
% 9.30/1.56    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl7_7),
% 9.30/1.56    inference(resolution,[],[f164,f100])).
% 9.30/1.56  fof(f224,plain,(
% 9.30/1.56    spl7_16 | ~spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f218,f162,f221])).
% 9.30/1.56  fof(f218,plain,(
% 9.30/1.56    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl7_7),
% 9.30/1.56    inference(unit_resulting_resolution,[],[f164,f100])).
% 9.30/1.56  fof(f208,plain,(
% 9.30/1.56    ~spl7_15 | spl7_2 | ~spl7_3),
% 9.30/1.56    inference(avatar_split_clause,[],[f203,f142,f136,f205])).
% 9.30/1.56  fof(f200,plain,(
% 9.30/1.56    spl7_14),
% 9.30/1.56    inference(avatar_split_clause,[],[f79,f197])).
% 9.30/1.56  fof(f79,plain,(
% 9.30/1.56    v1_xboole_0(k1_xboole_0)),
% 9.30/1.56    inference(cnf_transformation,[],[f3])).
% 9.30/1.56  fof(f3,axiom,(
% 9.30/1.56    v1_xboole_0(k1_xboole_0)),
% 9.30/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 9.30/1.56  fof(f195,plain,(
% 9.30/1.56    spl7_13),
% 9.30/1.56    inference(avatar_split_clause,[],[f66,f192])).
% 9.30/1.56  fof(f66,plain,(
% 9.30/1.56    v2_pre_topc(sK0)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f49,plain,(
% 9.30/1.56    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 9.30/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f48,f47,f46,f45])).
% 9.30/1.56  fof(f45,plain,(
% 9.30/1.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 9.30/1.56    introduced(choice_axiom,[])).
% 9.30/1.56  fof(f46,plain,(
% 9.30/1.56    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 9.30/1.56    introduced(choice_axiom,[])).
% 9.30/1.56  fof(f47,plain,(
% 9.30/1.56    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 9.30/1.56    introduced(choice_axiom,[])).
% 9.30/1.56  fof(f48,plain,(
% 9.30/1.56    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 9.30/1.56    introduced(choice_axiom,[])).
% 9.30/1.56  fof(f44,plain,(
% 9.30/1.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.30/1.56    inference(flattening,[],[f43])).
% 9.30/1.56  fof(f43,plain,(
% 9.30/1.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.30/1.56    inference(nnf_transformation,[],[f24])).
% 9.30/1.56  fof(f24,plain,(
% 9.30/1.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 9.30/1.56    inference(flattening,[],[f23])).
% 9.30/1.56  fof(f23,plain,(
% 9.30/1.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 9.30/1.56    inference(ennf_transformation,[],[f22])).
% 9.30/1.56  fof(f22,negated_conjecture,(
% 9.30/1.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 9.30/1.56    inference(negated_conjecture,[],[f21])).
% 9.30/1.56  fof(f21,conjecture,(
% 9.30/1.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 9.30/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 9.30/1.56  fof(f190,plain,(
% 9.30/1.56    spl7_12),
% 9.30/1.56    inference(avatar_split_clause,[],[f67,f187])).
% 9.30/1.56  fof(f67,plain,(
% 9.30/1.56    l1_pre_topc(sK0)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f185,plain,(
% 9.30/1.56    spl7_11),
% 9.30/1.56    inference(avatar_split_clause,[],[f68,f182])).
% 9.30/1.56  fof(f68,plain,(
% 9.30/1.56    v2_pre_topc(sK1)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f180,plain,(
% 9.30/1.56    spl7_10),
% 9.30/1.56    inference(avatar_split_clause,[],[f69,f177])).
% 9.30/1.56  fof(f69,plain,(
% 9.30/1.56    l1_pre_topc(sK1)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f175,plain,(
% 9.30/1.56    spl7_9),
% 9.30/1.56    inference(avatar_split_clause,[],[f70,f172])).
% 9.30/1.56  fof(f70,plain,(
% 9.30/1.56    v1_funct_1(sK2)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f170,plain,(
% 9.30/1.56    spl7_8),
% 9.30/1.56    inference(avatar_split_clause,[],[f71,f167])).
% 9.30/1.56  fof(f71,plain,(
% 9.30/1.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f165,plain,(
% 9.30/1.56    spl7_7),
% 9.30/1.56    inference(avatar_split_clause,[],[f72,f162])).
% 9.30/1.56  fof(f72,plain,(
% 9.30/1.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f160,plain,(
% 9.30/1.56    spl7_6),
% 9.30/1.56    inference(avatar_split_clause,[],[f73,f157])).
% 9.30/1.56  fof(f73,plain,(
% 9.30/1.56    v1_funct_1(sK3)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f155,plain,(
% 9.30/1.56    spl7_5),
% 9.30/1.56    inference(avatar_split_clause,[],[f74,f152])).
% 9.30/1.56  fof(f74,plain,(
% 9.30/1.56    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f150,plain,(
% 9.30/1.56    spl7_4),
% 9.30/1.56    inference(avatar_split_clause,[],[f75,f147])).
% 9.30/1.56  fof(f75,plain,(
% 9.30/1.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f145,plain,(
% 9.30/1.56    spl7_3),
% 9.30/1.56    inference(avatar_split_clause,[],[f76,f142])).
% 9.30/1.56  fof(f76,plain,(
% 9.30/1.56    sK2 = sK3),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f140,plain,(
% 9.30/1.56    spl7_1 | spl7_2),
% 9.30/1.56    inference(avatar_split_clause,[],[f77,f136,f132])).
% 9.30/1.56  fof(f77,plain,(
% 9.30/1.56    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  fof(f139,plain,(
% 9.30/1.56    ~spl7_1 | ~spl7_2),
% 9.30/1.56    inference(avatar_split_clause,[],[f78,f136,f132])).
% 9.30/1.56  fof(f78,plain,(
% 9.30/1.56    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 9.30/1.56    inference(cnf_transformation,[],[f49])).
% 9.30/1.56  % SZS output end Proof for theBenchmark
% 9.30/1.56  % (27879)------------------------------
% 9.30/1.56  % (27879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.30/1.56  % (27879)Termination reason: Refutation
% 9.30/1.56  
% 9.30/1.56  % (27879)Memory used [KB]: 3965
% 9.30/1.56  % (27879)Time elapsed: 0.913 s
% 9.30/1.56  % (27879)------------------------------
% 9.30/1.56  % (27879)------------------------------
% 9.30/1.57  % (27792)Success in time 1.188 s
%------------------------------------------------------------------------------

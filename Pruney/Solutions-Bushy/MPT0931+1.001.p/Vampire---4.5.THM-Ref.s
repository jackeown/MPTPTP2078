%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0931+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:55 EST 2020

% Result     : Theorem 9.83s
% Output     : Refutation 10.42s
% Verified   : 
% Statistics : Number of formulae       : 1596 (12550 expanded)
%              Number of leaves         :  217 (4098 expanded)
%              Depth                    :   20
%              Number of atoms          : 5068 (36015 expanded)
%              Number of equality atoms :  377 (10153 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5789,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f107,f112,f122,f141,f147,f156,f302,f313,f318,f319,f320,f327,f328,f351,f360,f365,f372,f373,f389,f394,f395,f400,f429,f434,f439,f441,f451,f465,f466,f475,f480,f485,f487,f500,f537,f588,f593,f603,f608,f615,f620,f641,f646,f662,f670,f679,f684,f711,f721,f726,f727,f728,f735,f736,f1375,f1377,f1389,f1393,f1411,f1419,f1420,f1421,f1424,f1426,f1438,f1443,f1448,f1467,f1496,f1685,f1690,f1695,f1700,f1705,f1710,f1715,f1720,f1725,f1730,f1735,f1740,f1745,f1750,f1757,f1758,f1804,f1805,f1807,f1809,f1811,f1816,f1821,f1826,f1831,f1836,f1841,f1846,f1851,f1852,f1853,f1854,f1859,f1864,f1865,f1866,f1867,f1872,f1873,f1878,f1883,f1886,f1889,f1891,f1893,f1895,f1900,f1902,f1904,f1906,f1908,f1910,f1911,f1927,f1928,f1933,f1938,f1943,f1948,f1987,f1992,f1997,f2002,f2004,f2009,f2014,f2015,f2016,f2017,f2022,f2026,f2030,f2036,f2038,f2039,f2041,f2047,f2049,f2050,f2082,f2083,f2096,f2097,f2139,f2144,f2149,f2154,f2159,f2166,f2167,f2170,f2235,f2240,f2242,f2243,f2260,f2265,f2266,f2325,f2330,f2331,f2333,f2350,f2351,f2384,f2389,f2391,f2395,f2396,f2398,f2399,f2400,f2427,f2432,f2437,f2442,f2443,f2444,f2446,f2447,f2448,f2450,f2451,f2453,f2454,f2461,f2464,f2553,f2555,f2556,f2564,f2566,f2567,f2571,f2572,f2574,f2575,f2577,f2578,f2579,f2601,f2606,f2607,f2687,f2692,f2693,f2695,f2712,f2713,f2899,f2908,f2942,f2951,f2984,f2993,f2998,f2999,f3000,f3003,f3004,f3005,f3006,f3009,f3010,f3011,f3012,f3017,f3019,f3021,f3024,f3028,f3031,f3038,f3039,f3048,f3049,f3051,f3053,f3066,f3075,f3076,f3079,f3098,f3102,f3105,f3116,f3117,f3120,f3128,f3132,f3139,f3141,f3143,f3144,f3146,f3148,f3150,f3152,f3153,f3156,f3158,f3163,f3165,f3166,f3174,f3175,f3180,f3181,f3250,f3266,f3267,f3329,f3350,f3355,f3356,f3431,f3432,f3449,f3459,f3477,f3478,f3488,f3498,f3738,f3742,f3746,f3753,f3813,f3814,f3819,f3820,f3828,f3909,f3918,f3932,f3934,f3935,f3957,f3962,f3964,f3966,f4001,f4010,f4040,f4044,f4048,f4055,f4100,f4105,f4110,f4115,f4117,f4118,f4136,f4138,f4140,f4141,f4142,f4182,f4213,f4220,f4243,f4245,f4248,f4250,f4251,f4253,f4255,f4256,f4257,f4352,f4357,f4359,f4363,f4365,f4366,f4367,f4368,f4369,f4370,f4371,f4372,f4374,f4375,f4377,f4384,f4447,f4452,f4457,f4462,f4526,f5015,f5020,f5025,f5030,f5035,f5040,f5049,f5051,f5053,f5057,f5058,f5061,f5130,f5137,f5139,f5144,f5145,f5150,f5151,f5156,f5163,f5165,f5166,f5170,f5171,f5174,f5175,f5176,f5224,f5235,f5249,f5263,f5288,f5293,f5298,f5303,f5308,f5313,f5315,f5319,f5323,f5326,f5411,f5418,f5420,f5425,f5426,f5431,f5432,f5437,f5453,f5455,f5459,f5461,f5464,f5467,f5469,f5472,f5474,f5475,f5477,f5480,f5483,f5486,f5487,f5488,f5755,f5761,f5768,f5769,f5770,f5771,f5772,f5773,f5778,f5779,f5781,f5784,f5786,f5788])).

fof(f5788,plain,
    ( ~ spl13_109
    | spl13_110 ),
    inference(avatar_contradiction_clause,[],[f5787])).

fof(f5787,plain,
    ( $false
    | ~ spl13_109
    | spl13_110 ),
    inference(subsumption_resolution,[],[f4229,f2238])).

fof(f2238,plain,
    ( ~ m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_110 ),
    inference(avatar_component_clause,[],[f2237])).

fof(f2237,plain,
    ( spl13_110
  <=> m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f4229,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_109 ),
    inference(unit_resulting_resolution,[],[f2234,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f2234,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_109 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2232,plain,
    ( spl13_109
  <=> r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_109])])).

fof(f5786,plain,
    ( spl13_1
    | ~ spl13_101
    | ~ spl13_109 ),
    inference(avatar_contradiction_clause,[],[f5785])).

fof(f5785,plain,
    ( $false
    | spl13_1
    | ~ spl13_101
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f4225,f2046])).

fof(f2046,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_101 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f2044,plain,
    ( spl13_101
  <=> r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_101])])).

fof(f4225,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_109 ),
    inference(unit_resulting_resolution,[],[f82,f2234,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | ~ r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f82,plain,
    ( k11_relat_1(sK0,sK1) != a_2_0_mcart_1(sK0,sK1)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl13_1
  <=> k11_relat_1(sK0,sK1) = a_2_0_mcart_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f5784,plain,
    ( spl13_1
    | ~ spl13_101
    | ~ spl13_109 ),
    inference(avatar_contradiction_clause,[],[f5783])).

fof(f5783,plain,
    ( $false
    | spl13_1
    | ~ spl13_101
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f5782,f82])).

fof(f5782,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(sK0,sK1)
    | ~ spl13_101
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f4231,f2046])).

fof(f4231,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | k11_relat_1(sK0,sK1) = a_2_0_mcart_1(sK0,sK1)
    | ~ spl13_109 ),
    inference(resolution,[],[f2234,f53])).

fof(f5781,plain,
    ( ~ spl13_109
    | spl13_110 ),
    inference(avatar_contradiction_clause,[],[f5780])).

fof(f5780,plain,
    ( $false
    | ~ spl13_109
    | spl13_110 ),
    inference(subsumption_resolution,[],[f4235,f2238])).

fof(f4235,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_109 ),
    inference(resolution,[],[f2234,f50])).

fof(f5779,plain,
    ( spl13_175
    | ~ spl13_171
    | ~ spl13_205 ),
    inference(avatar_split_clause,[],[f5777,f5765,f4112,f4240])).

fof(f4240,plain,
    ( spl13_175
  <=> r2_hidden(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_175])])).

fof(f4112,plain,
    ( spl13_171
  <=> r2_hidden(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_171])])).

fof(f5765,plain,
    ( spl13_205
  <=> sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_205])])).

fof(f5777,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_171
    | ~ spl13_205 ),
    inference(backward_demodulation,[],[f4114,f5767])).

fof(f5767,plain,
    ( sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)))
    | ~ spl13_205 ),
    inference(avatar_component_clause,[],[f5765])).

fof(f4114,plain,
    ( r2_hidden(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_171 ),
    inference(avatar_component_clause,[],[f4112])).

fof(f5778,plain,
    ( spl13_172
    | ~ spl13_168
    | ~ spl13_205 ),
    inference(avatar_split_clause,[],[f5774,f5765,f4097,f4133])).

fof(f4133,plain,
    ( spl13_172
  <=> m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_172])])).

fof(f4097,plain,
    ( spl13_168
  <=> m1_subset_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_168])])).

fof(f5774,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_168
    | ~ spl13_205 ),
    inference(backward_demodulation,[],[f4099,f5767])).

fof(f4099,plain,
    ( m1_subset_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_168 ),
    inference(avatar_component_clause,[],[f4097])).

fof(f5773,plain,
    ( ~ spl13_109
    | spl13_1
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4085,f2044,f80,f2232])).

fof(f4085,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f82,f2046,f53])).

fof(f5772,plain,
    ( ~ spl13_109
    | spl13_1
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4262,f2044,f80,f2232])).

fof(f4262,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f82,f2046,f53])).

fof(f5771,plain,
    ( ~ spl13_109
    | spl13_110 ),
    inference(avatar_split_clause,[],[f4279,f2237,f2232])).

fof(f4279,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_110 ),
    inference(unit_resulting_resolution,[],[f2238,f50])).

fof(f5770,plain,
    ( spl13_109
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(avatar_split_clause,[],[f5753,f4112,f4107,f4102,f85,f2232])).

fof(f85,plain,
    ( spl13_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f4102,plain,
    ( spl13_169
  <=> sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_169])])).

fof(f4107,plain,
    ( spl13_170
  <=> sK1 = k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_170])])).

fof(f5753,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5752,f4104])).

fof(f4104,plain,
    ( sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_169 ),
    inference(avatar_component_clause,[],[f4102])).

fof(f5752,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5751,f4109])).

fof(f4109,plain,
    ( sK1 = k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_170 ),
    inference(avatar_component_clause,[],[f4107])).

fof(f5751,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k11_relat_1(sK0,k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5743,f150])).

fof(f150,plain,
    ( ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0))
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f87,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f87,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f5743,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k9_relat_1(sK0,k1_tarski(k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_171 ),
    inference(unit_resulting_resolution,[],[f87,f87,f4114,f76,f4114,f489])).

fof(f489,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_mcart_1(X0),k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k1_mcart_1(X0),X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f63,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f63,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f76,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f5769,plain,
    ( spl13_109
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(avatar_split_clause,[],[f5759,f4112,f4107,f4102,f85,f2232])).

fof(f5759,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5758,f4104])).

fof(f5758,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5757,f4109])).

fof(f5757,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k11_relat_1(sK0,k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5741,f150])).

fof(f5741,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k9_relat_1(sK0,k1_tarski(k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_171 ),
    inference(unit_resulting_resolution,[],[f87,f87,f4114,f76,f4114,f489])).

fof(f5768,plain,
    ( spl13_205
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(avatar_split_clause,[],[f5763,f4112,f4107,f4102,f85,f5765])).

fof(f5763,plain,
    ( sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5762,f4109])).

fof(f5762,plain,
    ( sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_169
    | ~ spl13_171 ),
    inference(forward_demodulation,[],[f5738,f4104])).

fof(f5738,plain,
    ( sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)),k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_171 ),
    inference(unit_resulting_resolution,[],[f87,f4114,f49])).

fof(f5761,plain,
    ( ~ spl13_2
    | spl13_109
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(avatar_contradiction_clause,[],[f5760])).

fof(f5760,plain,
    ( $false
    | ~ spl13_2
    | spl13_109
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(subsumption_resolution,[],[f5759,f2233])).

fof(f2233,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_109 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f5755,plain,
    ( ~ spl13_2
    | spl13_109
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(avatar_contradiction_clause,[],[f5754])).

fof(f5754,plain,
    ( $false
    | ~ spl13_2
    | spl13_109
    | ~ spl13_169
    | ~ spl13_170
    | ~ spl13_171 ),
    inference(subsumption_resolution,[],[f5753,f2233])).

fof(f5488,plain,
    ( ~ spl13_99
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5273,f2093,f2019])).

fof(f2019,plain,
    ( spl13_99
  <=> v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_99])])).

fof(f2093,plain,
    ( spl13_103
  <=> r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_103])])).

fof(f5273,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f2095,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2095,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_103 ),
    inference(avatar_component_clause,[],[f2093])).

fof(f5487,plain,
    ( ~ spl13_99
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5277,f2093,f2019])).

fof(f5277,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_103 ),
    inference(resolution,[],[f2095,f58])).

fof(f5486,plain,
    ( ~ spl13_99
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5485,f2603,f2598,f2019])).

fof(f2598,plain,
    ( spl13_122
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f2603,plain,
    ( spl13_123
  <=> k9_relat_1(sK0,k11_relat_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_123])])).

fof(f5485,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5484,f2605])).

fof(f2605,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_123 ),
    inference(avatar_component_clause,[],[f2603])).

fof(f5484,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f2599,f2605])).

fof(f2599,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | spl13_122 ),
    inference(avatar_component_clause,[],[f2598])).

fof(f5483,plain,
    ( spl13_103
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5482,f2603,f2598,f2093])).

fof(f5482,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5481,f2605])).

fof(f5481,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f3464,f2605])).

fof(f3464,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))),k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | spl13_122 ),
    inference(unit_resulting_resolution,[],[f2599,f116])).

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f5480,plain,
    ( spl13_103
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5479,f2603,f2598,f2093])).

fof(f5479,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5478,f2605])).

fof(f5478,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f3463,f2605])).

fof(f3463,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))),k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | spl13_122 ),
    inference(unit_resulting_resolution,[],[f48,f2599,f51])).

fof(f5477,plain,
    ( ~ spl13_99
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5476,f2603,f2598,f85,f2019])).

fof(f5476,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f3462,f2605])).

fof(f3462,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | spl13_122 ),
    inference(unit_resulting_resolution,[],[f87,f2599,f181])).

fof(f181,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k9_relat_1(X4,X5))
      | ~ v1_xboole_0(X5)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f178,f116])).

fof(f178,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(X3,X5))
      | ~ v1_relat_1(X3)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f64,f58])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X3),X1)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5475,plain,
    ( ~ spl13_99
    | ~ spl13_2
    | spl13_122 ),
    inference(avatar_split_clause,[],[f3460,f2598,f85,f2019])).

fof(f3460,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | spl13_122 ),
    inference(unit_resulting_resolution,[],[f87,f87,f2599,f275])).

fof(f275,plain,(
    ! [X6,X7,X5] :
      ( v1_xboole_0(k9_relat_1(X6,k9_relat_1(X7,X5)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f180,f116])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X2,k9_relat_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f178,f64])).

fof(f5474,plain,
    ( ~ spl13_99
    | ~ spl13_2
    | spl13_122 ),
    inference(avatar_split_clause,[],[f5473,f2598,f85,f2019])).

fof(f5473,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f5448,f87])).

fof(f5448,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122 ),
    inference(duplicate_literal_removal,[],[f3465])).

fof(f3465,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122 ),
    inference(resolution,[],[f2599,f275])).

fof(f5472,plain,
    ( ~ spl13_99
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5471,f2603,f2598,f85,f2019])).

fof(f5471,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5470,f2605])).

fof(f5470,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f3467,f87])).

fof(f3467,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ v1_relat_1(sK0)
    | spl13_122 ),
    inference(resolution,[],[f2599,f181])).

fof(f5469,plain,
    ( ~ spl13_99
    | spl13_136
    | ~ spl13_2
    | spl13_122 ),
    inference(avatar_split_clause,[],[f5468,f2598,f85,f3161,f2019])).

fof(f3161,plain,
    ( spl13_136
  <=> ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_136])])).

fof(f5468,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f3469,f87])).

fof(f3469,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_122 ),
    inference(superposition,[],[f2599,f183])).

fof(f183,plain,(
    ! [X10,X11,X9] :
      ( k9_relat_1(X9,X10) = X11
      | ~ v1_xboole_0(X10)
      | ~ v1_relat_1(X9)
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f178,f158])).

fof(f158,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK10(X2,X3),X2)
      | X2 = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f52,f58])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | r2_hidden(sK10(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5467,plain,
    ( spl13_135
    | ~ spl13_99
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5466,f2603,f2598,f85,f2019,f3137])).

fof(f3137,plain,
    ( spl13_135
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_135])])).

fof(f5466,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5465,f2605])).

fof(f5465,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) )
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f5449,f87])).

fof(f5449,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
        | ~ v1_relat_1(sK0) )
    | spl13_122 ),
    inference(duplicate_literal_removal,[],[f3470])).

fof(f3470,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_122 ),
    inference(superposition,[],[f2599,f183])).

fof(f5464,plain,
    ( spl13_135
    | ~ spl13_99
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5463,f2603,f2598,f85,f2019,f3137])).

fof(f5463,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5462,f2605])).

fof(f5462,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) )
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f3471,f87])).

fof(f3471,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
        | ~ v1_relat_1(sK0) )
    | spl13_122 ),
    inference(duplicate_literal_removal,[],[f3470])).

fof(f5461,plain,
    ( ~ spl13_99
    | ~ spl13_2
    | spl13_122 ),
    inference(avatar_split_clause,[],[f5460,f2598,f85,f2019])).

fof(f5460,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | spl13_122 ),
    inference(subsumption_resolution,[],[f3472,f87])).

fof(f3472,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_122 ),
    inference(duplicate_literal_removal,[],[f3465])).

fof(f5459,plain,
    ( ~ spl13_99
    | ~ spl13_123
    | spl13_124 ),
    inference(avatar_split_clause,[],[f5458,f2684,f2603,f2019])).

fof(f2684,plain,
    ( spl13_124
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f5458,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_123
    | spl13_124 ),
    inference(forward_demodulation,[],[f5457,f2605])).

fof(f5457,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_123
    | spl13_124 ),
    inference(forward_demodulation,[],[f5456,f2605])).

fof(f5456,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_123
    | spl13_124 ),
    inference(forward_demodulation,[],[f2685,f2605])).

fof(f2685,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))))
    | spl13_124 ),
    inference(avatar_component_clause,[],[f2684])).

fof(f5455,plain,
    ( spl13_103
    | ~ spl13_123
    | ~ spl13_126 ),
    inference(avatar_split_clause,[],[f5454,f2709,f2603,f2093])).

fof(f2709,plain,
    ( spl13_126
  <=> r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f5454,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_123
    | ~ spl13_126 ),
    inference(forward_demodulation,[],[f2711,f2605])).

fof(f2711,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_126 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f5453,plain,
    ( spl13_103
    | ~ spl13_123
    | ~ spl13_146 ),
    inference(avatar_split_clause,[],[f5452,f3474,f2603,f2093])).

fof(f3474,plain,
    ( spl13_146
  <=> r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))),k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_146])])).

fof(f5452,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_123
    | ~ spl13_146 ),
    inference(forward_demodulation,[],[f5451,f2605])).

fof(f5451,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_123
    | ~ spl13_146 ),
    inference(forward_demodulation,[],[f3476,f2605])).

fof(f3476,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))),k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_146 ),
    inference(avatar_component_clause,[],[f3474])).

fof(f5437,plain,
    ( spl13_204
    | spl13_98
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5380,f2019,f2011,f5434])).

fof(f5434,plain,
    ( spl13_204
  <=> r2_hidden(sK10(k11_relat_1(sK0,sK1),k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_204])])).

fof(f2011,plain,
    ( spl13_98
  <=> k11_relat_1(sK0,sK1) = k9_relat_1(sK0,k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f5380,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1))
    | spl13_98
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f2012,f2021,f158])).

fof(f2021,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_99 ),
    inference(avatar_component_clause,[],[f2019])).

fof(f2012,plain,
    ( k11_relat_1(sK0,sK1) != k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | spl13_98 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f5432,plain,
    ( spl13_201
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5381,f2019,f397,f5408])).

fof(f5408,plain,
    ( spl13_201
  <=> k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_201])])).

fof(f397,plain,
    ( spl13_21
  <=> v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f5381,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f3334,f2021,f158])).

fof(f3334,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_21 ),
    inference(unit_resulting_resolution,[],[f399,f58])).

fof(f399,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f397])).

fof(f5431,plain,
    ( spl13_203
    | spl13_98
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5382,f2019,f2011,f5428])).

fof(f5428,plain,
    ( spl13_203
  <=> m1_subset_1(sK10(k11_relat_1(sK0,sK1),k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_203])])).

fof(f5382,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1))
    | spl13_98
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f2012,f2021,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),X0)
      | ~ v1_xboole_0(X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f158,f50])).

fof(f5426,plain,
    ( spl13_201
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5383,f2019,f397,f5408])).

fof(f5383,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f399,f2021,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ v1_xboole_0(X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f158,f58])).

fof(f5425,plain,
    ( spl13_201
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5386,f2019,f397,f5408])).

fof(f5386,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f399,f2021,f162])).

fof(f5420,plain,
    ( spl13_201
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5419,f2603,f2019,f397,f85,f5408])).

fof(f5419,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5392,f2605])).

fof(f5392,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f399,f87,f2021,f183])).

fof(f5418,plain,
    ( spl13_202
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f5394,f2019,f397,f85,f5415])).

fof(f5415,plain,
    ( spl13_202
  <=> k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_202])])).

fof(f5394,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f399,f87,f2021,f183])).

fof(f5411,plain,
    ( spl13_201
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5406,f2603,f2019,f397,f85,f5408])).

fof(f5406,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5397,f2605])).

fof(f5397,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f87,f3334,f2021,f992])).

fof(f992,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(X3,X4,X5),X5)
      | ~ v1_relat_1(X3)
      | k9_relat_1(X3,X4) = X5
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f38,f58])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5326,plain,
    ( spl13_99
    | ~ spl13_122
    | ~ spl13_123 ),
    inference(avatar_split_clause,[],[f5325,f2603,f2598,f2019])).

fof(f5325,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f5324,f2605])).

fof(f5324,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_122
    | ~ spl13_123 ),
    inference(forward_demodulation,[],[f2600,f2605])).

fof(f2600,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_122 ),
    inference(avatar_component_clause,[],[f2598])).

fof(f5323,plain,
    ( ~ spl13_103
    | ~ spl13_123
    | spl13_126 ),
    inference(avatar_split_clause,[],[f5322,f2709,f2603,f2093])).

fof(f5322,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_123
    | spl13_126 ),
    inference(backward_demodulation,[],[f2710,f2605])).

fof(f2710,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_126 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f5319,plain,
    ( spl13_97
    | ~ spl13_124
    | ~ spl13_125 ),
    inference(avatar_split_clause,[],[f5318,f2689,f2684,f2006])).

fof(f2006,plain,
    ( spl13_97
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_97])])).

fof(f2689,plain,
    ( spl13_125
  <=> k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_125])])).

fof(f5318,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_124
    | ~ spl13_125 ),
    inference(forward_demodulation,[],[f5317,f2691])).

fof(f2691,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_125 ),
    inference(avatar_component_clause,[],[f2689])).

fof(f5317,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_124
    | ~ spl13_125 ),
    inference(forward_demodulation,[],[f2686,f2691])).

fof(f2686,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))))
    | ~ spl13_124 ),
    inference(avatar_component_clause,[],[f2684])).

fof(f5315,plain,
    ( ~ spl13_99
    | spl13_108
    | ~ spl13_2
    | spl13_94 ),
    inference(avatar_split_clause,[],[f5314,f1989,f85,f2157,f2019])).

fof(f2157,plain,
    ( spl13_108
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f1989,plain,
    ( spl13_94
  <=> v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f5314,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_94 ),
    inference(subsumption_resolution,[],[f2671,f87])).

fof(f2671,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_94 ),
    inference(superposition,[],[f1991,f183])).

fof(f1991,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_94 ),
    inference(avatar_component_clause,[],[f1989])).

fof(f5313,plain,
    ( spl13_200
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5264,f2093,f85,f5310])).

fof(f5310,plain,
    ( spl13_200
  <=> r2_hidden(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_200])])).

fof(f5264,plain,
    ( r2_hidden(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f2095,f64])).

fof(f5308,plain,
    ( spl13_199
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5265,f2093,f85,f5305])).

fof(f5305,plain,
    ( spl13_199
  <=> r2_hidden(k4_tarski(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_199])])).

fof(f5265,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK0)
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f2095,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5303,plain,
    ( spl13_198
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5266,f2093,f85,f5300])).

fof(f5300,plain,
    ( spl13_198
  <=> m1_subset_1(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_198])])).

fof(f5266,plain,
    ( m1_subset_1(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f2095,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X2,X1),X2)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f64,f50])).

fof(f5298,plain,
    ( spl13_197
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5268,f2093,f85,f5295])).

fof(f5295,plain,
    ( spl13_197
  <=> m1_subset_1(k4_tarski(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_197])])).

fof(f5268,plain,
    ( m1_subset_1(k4_tarski(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),sK0)
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f2095,f522])).

fof(f522,plain,(
    ! [X6,X4,X5] :
      ( m1_subset_1(k4_tarski(sK3(X4,X6,X5),X5),X4)
      | ~ r2_hidden(X5,k9_relat_1(X4,X6))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f65,f50])).

fof(f5293,plain,
    ( ~ spl13_196
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5270,f2093,f397,f85,f5290])).

fof(f5290,plain,
    ( spl13_196
  <=> r2_hidden(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_196])])).

fof(f5270,plain,
    ( ~ r2_hidden(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f3334,f2095,f529])).

fof(f529,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X2,X1),X3)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k9_relat_1(X0,X3)) ) ),
    inference(duplicate_literal_removal,[],[f521])).

fof(f521,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK3(X0,X2,X1),X3)
      | r2_hidden(X1,k9_relat_1(X0,X3)) ) ),
    inference(resolution,[],[f65,f63])).

fof(f5288,plain,
    ( spl13_195
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(avatar_split_clause,[],[f5283,f2093,f85,f5285])).

fof(f5285,plain,
    ( spl13_195
  <=> r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_195])])).

fof(f5283,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(forward_demodulation,[],[f5271,f150])).

fof(f5271,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k1_tarski(sK3(sK0,k11_relat_1(sK0,sK1),sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))))
    | ~ spl13_2
    | ~ spl13_103 ),
    inference(unit_resulting_resolution,[],[f87,f76,f2095,f529])).

fof(f5263,plain,
    ( ~ spl13_194
    | spl13_162 ),
    inference(avatar_split_clause,[],[f5251,f4007,f5260])).

fof(f5260,plain,
    ( spl13_194
  <=> m1_subset_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_194])])).

fof(f4007,plain,
    ( spl13_162
  <=> r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_162])])).

fof(f5251,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_162 ),
    inference(unit_resulting_resolution,[],[f95,f4009,f51])).

fof(f4009,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_162 ),
    inference(avatar_component_clause,[],[f4007])).

fof(f95,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f76,f58])).

fof(f5249,plain,
    ( ~ spl13_193
    | spl13_161 ),
    inference(avatar_split_clause,[],[f5237,f3998,f5246])).

fof(f5246,plain,
    ( spl13_193
  <=> m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_193])])).

fof(f3998,plain,
    ( spl13_161
  <=> r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_161])])).

fof(f5237,plain,
    ( ~ m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_161 ),
    inference(unit_resulting_resolution,[],[f95,f4000,f51])).

fof(f4000,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_161 ),
    inference(avatar_component_clause,[],[f3998])).

fof(f5235,plain,
    ( ~ spl13_192
    | spl13_158 ),
    inference(avatar_split_clause,[],[f5226,f3915,f5232])).

fof(f5232,plain,
    ( spl13_192
  <=> m1_subset_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_192])])).

fof(f3915,plain,
    ( spl13_158
  <=> r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_158])])).

fof(f5226,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_158 ),
    inference(unit_resulting_resolution,[],[f95,f3917,f51])).

fof(f3917,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_158 ),
    inference(avatar_component_clause,[],[f3915])).

fof(f5224,plain,
    ( ~ spl13_191
    | spl13_157 ),
    inference(avatar_split_clause,[],[f5215,f3906,f5221])).

fof(f5221,plain,
    ( spl13_191
  <=> m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_191])])).

fof(f3906,plain,
    ( spl13_157
  <=> r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_157])])).

fof(f5215,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_157 ),
    inference(unit_resulting_resolution,[],[f95,f3908,f51])).

fof(f3908,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_157 ),
    inference(avatar_component_clause,[],[f3906])).

fof(f5176,plain,
    ( ~ spl13_82
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f5003,f2079,f1856])).

fof(f1856,plain,
    ( spl13_82
  <=> v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f2079,plain,
    ( spl13_102
  <=> r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f5003,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f2081,f58])).

fof(f2081,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_102 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f5175,plain,
    ( ~ spl13_82
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f5007,f2079,f1856])).

fof(f5007,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_102 ),
    inference(resolution,[],[f2081,f58])).

fof(f5174,plain,
    ( ~ spl13_82
    | spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f5173,f2262,f2257,f1856])).

fof(f2257,plain,
    ( spl13_111
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_111])])).

fof(f2262,plain,
    ( spl13_112
  <=> k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f5173,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f5172,f2264])).

fof(f2264,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f2262])).

fof(f5172,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f2258,f2264])).

fof(f2258,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | spl13_111 ),
    inference(avatar_component_clause,[],[f2257])).

fof(f5171,plain,
    ( ~ spl13_82
    | spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f3104,f2262,f2257,f1856])).

fof(f3104,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f3103,f2264])).

fof(f3103,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f2258,f2264])).

fof(f5170,plain,
    ( ~ spl13_82
    | ~ spl13_112
    | spl13_113 ),
    inference(avatar_split_clause,[],[f5169,f2322,f2262,f1856])).

fof(f2322,plain,
    ( spl13_113
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_113])])).

fof(f5169,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f5168,f2264])).

fof(f5168,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f5167,f2264])).

fof(f5167,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f2323,f2264])).

fof(f2323,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))))
    | spl13_113 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f5166,plain,
    ( ~ spl13_82
    | ~ spl13_112
    | spl13_113 ),
    inference(avatar_split_clause,[],[f3101,f2322,f2262,f1856])).

fof(f3101,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f3100,f2264])).

fof(f3100,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f3099,f2264])).

fof(f3099,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_112
    | spl13_113 ),
    inference(forward_demodulation,[],[f2323,f2264])).

fof(f5165,plain,
    ( spl13_102
    | ~ spl13_112
    | ~ spl13_115 ),
    inference(avatar_split_clause,[],[f5164,f2347,f2262,f2079])).

fof(f2347,plain,
    ( spl13_115
  <=> r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_115])])).

fof(f5164,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | ~ spl13_115 ),
    inference(forward_demodulation,[],[f2349,f2264])).

fof(f2349,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_115 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f5163,plain,
    ( spl13_102
    | ~ spl13_112
    | ~ spl13_115 ),
    inference(avatar_split_clause,[],[f3097,f2347,f2262,f2079])).

fof(f3097,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | ~ spl13_115 ),
    inference(forward_demodulation,[],[f2349,f2264])).

fof(f5156,plain,
    ( spl13_190
    | spl13_81
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5103,f1856,f1848,f5153])).

fof(f5153,plain,
    ( spl13_190
  <=> r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_190])])).

fof(f1848,plain,
    ( spl13_81
  <=> a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_81])])).

fof(f5103,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),a_2_0_mcart_1(sK0,sK1))
    | spl13_81
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f1849,f1858,f158])).

fof(f1858,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f1856])).

fof(f1849,plain,
    ( a_2_0_mcart_1(sK0,sK1) != k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | spl13_81 ),
    inference(avatar_component_clause,[],[f1848])).

fof(f5151,plain,
    ( spl13_187
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5104,f1856,f397,f5127])).

fof(f5127,plain,
    ( spl13_187
  <=> k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_187])])).

fof(f5104,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f3334,f1858,f158])).

fof(f5150,plain,
    ( spl13_189
    | spl13_81
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5105,f1856,f1848,f5147])).

fof(f5147,plain,
    ( spl13_189
  <=> m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_189])])).

fof(f5105,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),a_2_0_mcart_1(sK0,sK1))
    | spl13_81
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f1849,f1858,f161])).

fof(f5145,plain,
    ( spl13_187
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5106,f1856,f397,f5127])).

fof(f5106,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f399,f1858,f162])).

fof(f5144,plain,
    ( spl13_187
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5109,f1856,f397,f5127])).

fof(f5109,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f399,f1858,f162])).

fof(f5139,plain,
    ( spl13_187
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f5138,f2262,f1856,f397,f85,f5127])).

fof(f5138,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f5115,f2264])).

fof(f5115,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f399,f87,f1858,f183])).

fof(f5137,plain,
    ( spl13_188
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f5117,f1856,f397,f85,f5134])).

fof(f5134,plain,
    ( spl13_188
  <=> k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_188])])).

fof(f5117,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f399,f87,f1858,f183])).

fof(f5130,plain,
    ( spl13_187
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f5125,f2262,f1856,f397,f85,f5127])).

fof(f5125,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f5120,f2264])).

fof(f5120,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f87,f3334,f1858,f992])).

fof(f5061,plain,
    ( spl13_82
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f5060,f2262,f2257,f1856])).

fof(f5060,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f5059,f2264])).

fof(f5059,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f2259,f2264])).

fof(f2259,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_111 ),
    inference(avatar_component_clause,[],[f2257])).

fof(f5058,plain,
    ( spl13_82
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f3030,f2262,f2257,f1856])).

fof(f3030,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f3029,f2264])).

fof(f3029,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(forward_demodulation,[],[f2259,f2264])).

fof(f5057,plain,
    ( spl13_82
    | ~ spl13_112
    | ~ spl13_113 ),
    inference(avatar_split_clause,[],[f5056,f2322,f2262,f1856])).

fof(f5056,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | ~ spl13_113 ),
    inference(forward_demodulation,[],[f5055,f2264])).

fof(f5055,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_112
    | ~ spl13_113 ),
    inference(forward_demodulation,[],[f5054,f2264])).

fof(f5054,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_112
    | ~ spl13_113 ),
    inference(forward_demodulation,[],[f2324,f2264])).

fof(f2324,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_113 ),
    inference(avatar_component_clause,[],[f2322])).

fof(f5053,plain,
    ( spl13_82
    | ~ spl13_112
    | ~ spl13_113
    | ~ spl13_114 ),
    inference(avatar_split_clause,[],[f5052,f2327,f2322,f2262,f1856])).

fof(f2327,plain,
    ( spl13_114
  <=> k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f5052,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | ~ spl13_113
    | ~ spl13_114 ),
    inference(forward_demodulation,[],[f3023,f2264])).

fof(f3023,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_113
    | ~ spl13_114 ),
    inference(forward_demodulation,[],[f3022,f2329])).

fof(f2329,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_114 ),
    inference(avatar_component_clause,[],[f2327])).

fof(f3022,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_113
    | ~ spl13_114 ),
    inference(forward_demodulation,[],[f2324,f2329])).

fof(f5051,plain,
    ( ~ spl13_102
    | ~ spl13_112
    | spl13_115 ),
    inference(avatar_split_clause,[],[f5050,f2347,f2262,f2079])).

fof(f5050,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | spl13_115 ),
    inference(forward_demodulation,[],[f2348,f2264])).

fof(f2348,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_115 ),
    inference(avatar_component_clause,[],[f2347])).

fof(f5049,plain,
    ( ~ spl13_102
    | ~ spl13_112
    | spl13_115 ),
    inference(avatar_split_clause,[],[f3027,f2347,f2262,f2079])).

fof(f3027,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_112
    | spl13_115 ),
    inference(backward_demodulation,[],[f2348,f2264])).

fof(f5040,plain,
    ( spl13_186
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f4994,f2079,f85,f5037])).

fof(f5037,plain,
    ( spl13_186
  <=> r2_hidden(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_186])])).

fof(f4994,plain,
    ( r2_hidden(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f2081,f64])).

fof(f5035,plain,
    ( spl13_185
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f4995,f2079,f85,f5032])).

fof(f5032,plain,
    ( spl13_185
  <=> r2_hidden(k4_tarski(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_185])])).

fof(f4995,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK0)
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f2081,f65])).

fof(f5030,plain,
    ( spl13_184
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f4996,f2079,f85,f5027])).

fof(f5027,plain,
    ( spl13_184
  <=> m1_subset_1(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_184])])).

fof(f4996,plain,
    ( m1_subset_1(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f2081,f177])).

fof(f5025,plain,
    ( spl13_183
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f4998,f2079,f85,f5022])).

fof(f5022,plain,
    ( spl13_183
  <=> m1_subset_1(k4_tarski(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_183])])).

fof(f4998,plain,
    ( m1_subset_1(k4_tarski(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),sK0)
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f2081,f522])).

fof(f5020,plain,
    ( ~ spl13_182
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f5000,f2079,f397,f85,f5017])).

fof(f5017,plain,
    ( spl13_182
  <=> r2_hidden(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_182])])).

fof(f5000,plain,
    ( ~ r2_hidden(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f3334,f2081,f529])).

fof(f5015,plain,
    ( spl13_181
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f5010,f2079,f85,f5012])).

fof(f5012,plain,
    ( spl13_181
  <=> r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k11_relat_1(sK0,sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_181])])).

fof(f5010,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k11_relat_1(sK0,sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(forward_demodulation,[],[f5001,f150])).

fof(f5001,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,k1_tarski(sK3(sK0,a_2_0_mcart_1(sK0,sK1),sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))))
    | ~ spl13_2
    | ~ spl13_102 ),
    inference(unit_resulting_resolution,[],[f87,f76,f2081,f529])).

fof(f4526,plain,
    ( ~ spl13_180
    | spl13_15
    | spl13_155 ),
    inference(avatar_split_clause,[],[f4519,f3816,f348,f4523])).

fof(f4523,plain,
    ( spl13_180
  <=> m1_subset_1(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_180])])).

fof(f348,plain,
    ( spl13_15
  <=> v1_xboole_0(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f3816,plain,
    ( spl13_155
  <=> r2_hidden(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_155])])).

fof(f4519,plain,
    ( ~ m1_subset_1(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_15
    | spl13_155 ),
    inference(unit_resulting_resolution,[],[f350,f3818,f51])).

fof(f3818,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_155 ),
    inference(avatar_component_clause,[],[f3816])).

fof(f350,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_15 ),
    inference(avatar_component_clause,[],[f348])).

fof(f4462,plain,
    ( spl13_179
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(avatar_split_clause,[],[f4432,f2550,f90,f85,f4459])).

fof(f4459,plain,
    ( spl13_179
  <=> r2_hidden(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_179])])).

fof(f90,plain,
    ( spl13_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f2550,plain,
    ( spl13_120
  <=> r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f4432,plain,
    ( r2_hidden(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2552,f355])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X1,X0,X2),X0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,a_2_0_mcart_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,a_2_0_mcart_1(X0,X2))
      | v1_xboole_0(X0)
      | r2_hidden(sK12(X1,X0,X2),X0) ) ),
    inference(resolution,[],[f59,f51])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X1) )
     => ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_mcart_1)).

fof(f2552,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_120 ),
    inference(avatar_component_clause,[],[f2550])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK0)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f4457,plain,
    ( spl13_178
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(avatar_split_clause,[],[f4433,f2550,f90,f85,f4454])).

fof(f4454,plain,
    ( spl13_178
  <=> sK1 = k1_mcart_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_178])])).

fof(f4433,plain,
    ( sK1 = k1_mcart_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2552,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(sK12(X0,X1,X2)) = X2
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4452,plain,
    ( spl13_177
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(avatar_split_clause,[],[f4434,f2550,f90,f85,f4449])).

fof(f4449,plain,
    ( spl13_177
  <=> sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)) = k2_mcart_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_177])])).

fof(f4434,plain,
    ( sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)) = k2_mcart_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2552,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(sK12(X0,X1,X2)) = X0
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4447,plain,
    ( spl13_176
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(avatar_split_clause,[],[f4435,f2550,f90,f85,f4444])).

fof(f4444,plain,
    ( spl13_176
  <=> m1_subset_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_176])])).

fof(f4435,plain,
    ( m1_subset_1(sK12(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_120 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2552,f59])).

fof(f4384,plain,
    ( ~ spl13_84
    | spl13_83
    | spl13_85 ),
    inference(avatar_split_clause,[],[f3927,f1875,f1861,f1869])).

fof(f1869,plain,
    ( spl13_84
  <=> m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f1861,plain,
    ( spl13_83
  <=> v1_xboole_0(k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_83])])).

fof(f1875,plain,
    ( spl13_85
  <=> r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_85])])).

fof(f3927,plain,
    ( ~ m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_83
    | spl13_85 ),
    inference(unit_resulting_resolution,[],[f1863,f1876,f51])).

fof(f1876,plain,
    ( ~ r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_85 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f1863,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | spl13_83 ),
    inference(avatar_component_clause,[],[f1861])).

fof(f4377,plain,
    ( spl13_83
    | ~ spl13_84
    | spl13_85 ),
    inference(avatar_contradiction_clause,[],[f4376])).

fof(f4376,plain,
    ( $false
    | spl13_83
    | ~ spl13_84
    | spl13_85 ),
    inference(subsumption_resolution,[],[f3927,f1871])).

fof(f1871,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_84 ),
    inference(avatar_component_clause,[],[f1869])).

fof(f4375,plain,
    ( spl13_85
    | spl13_83
    | ~ spl13_84 ),
    inference(avatar_split_clause,[],[f3936,f1869,f1861,f1875])).

fof(f3936,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_83
    | ~ spl13_84 ),
    inference(unit_resulting_resolution,[],[f1863,f1871,f51])).

fof(f4374,plain,
    ( spl13_85
    | spl13_83
    | ~ spl13_84 ),
    inference(avatar_split_clause,[],[f4373,f1869,f1861,f1875])).

fof(f4373,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_83
    | ~ spl13_84 ),
    inference(subsumption_resolution,[],[f3937,f1863])).

fof(f3937,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_84 ),
    inference(resolution,[],[f1871,f51])).

fof(f4372,plain,
    ( spl13_85
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(avatar_split_clause,[],[f4300,f3954,f85,f1875])).

fof(f3954,plain,
    ( spl13_159
  <=> r2_hidden(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_159])])).

fof(f4300,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4299,f234])).

fof(f234,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k2_mcart_1(k4_tarski(X1,X2)) = X5 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X5
      | k2_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X5
      | k2_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f4299,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4298,f208])).

fof(f208,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k1_mcart_1(k4_tarski(X1,X2)) = X4 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X4
      | k1_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X4
      | k1_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f4298,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k11_relat_1(sK0,k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4290,f150])).

fof(f4290,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k1_tarski(k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))))))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(unit_resulting_resolution,[],[f87,f87,f3956,f76,f3956,f489])).

fof(f3956,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_159 ),
    inference(avatar_component_clause,[],[f3954])).

fof(f4371,plain,
    ( spl13_85
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(avatar_split_clause,[],[f4304,f3954,f85,f1875])).

fof(f4304,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4303,f234])).

fof(f4303,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4302,f208])).

fof(f4302,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k11_relat_1(sK0,k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4288,f150])).

fof(f4288,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k1_tarski(k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))))))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(unit_resulting_resolution,[],[f87,f87,f3956,f76,f3956,f489])).

fof(f4370,plain,
    ( spl13_85
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(avatar_split_clause,[],[f4306,f3954,f85,f1875])).

fof(f4306,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(forward_demodulation,[],[f4283,f150])).

fof(f4283,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl13_2
    | ~ spl13_159 ),
    inference(unit_resulting_resolution,[],[f87,f76,f3956,f63])).

fof(f4369,plain,
    ( spl13_121
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(avatar_split_clause,[],[f4355,f3959,f90,f85,f2561])).

fof(f2561,plain,
    ( spl13_121
  <=> m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_121])])).

fof(f3959,plain,
    ( spl13_160
  <=> m1_subset_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_160])])).

fof(f4355,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(forward_demodulation,[],[f4354,f234])).

fof(f4354,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(forward_demodulation,[],[f4340,f208])).

fof(f4340,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(unit_resulting_resolution,[],[f87,f92,f3961,f294])).

fof(f294,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_mcart_1(X1),a_2_0_mcart_1(X0,k1_mcart_1(X1)))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f78,f50])).

fof(f78,plain,(
    ! [X3,X1] :
      ( r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,k1_mcart_1(X3)))
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k1_mcart_1(X3) != X2
      | r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k2_mcart_1(X3) != X0
      | k1_mcart_1(X3) != X2
      | r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3961,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_160 ),
    inference(avatar_component_clause,[],[f3959])).

fof(f4368,plain,
    ( ~ spl13_120
    | spl13_1
    | ~ spl13_85 ),
    inference(avatar_split_clause,[],[f3940,f1875,f80,f2550])).

fof(f3940,plain,
    ( ~ r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_85 ),
    inference(unit_resulting_resolution,[],[f82,f1877,f53])).

fof(f1877,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_85 ),
    inference(avatar_component_clause,[],[f1875])).

fof(f4367,plain,
    ( spl13_120
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(avatar_split_clause,[],[f4350,f3959,f90,f85,f2550])).

fof(f4350,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(forward_demodulation,[],[f4349,f234])).

fof(f4349,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(forward_demodulation,[],[f4342,f208])).

fof(f4342,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(unit_resulting_resolution,[],[f92,f87,f3961,f78])).

fof(f4366,plain,
    ( spl13_120
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(avatar_split_clause,[],[f4338,f3959,f90,f85,f2550])).

fof(f4338,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(unit_resulting_resolution,[],[f92,f87,f3961,f303])).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,a_2_0_mcart_1(X2,X0))
      | v1_xboole_0(X2) ) ),
    inference(forward_demodulation,[],[f296,f208])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,a_2_0_mcart_1(X2,k1_mcart_1(k4_tarski(X0,X1))))
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(k4_tarski(X0,X1),X2)
      | v1_xboole_0(X2) ) ),
    inference(superposition,[],[f78,f234])).

fof(f4365,plain,
    ( spl13_120
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(avatar_split_clause,[],[f4364,f3959,f90,f85,f2550])).

fof(f4364,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4360,f92])).

fof(f4360,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl13_2
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4344,f87])).

fof(f4344,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl13_160 ),
    inference(resolution,[],[f3961,f303])).

fof(f4363,plain,
    ( ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(avatar_contradiction_clause,[],[f4362])).

fof(f4362,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4361,f92])).

fof(f4361,plain,
    ( v1_xboole_0(sK0)
    | ~ spl13_2
    | spl13_120
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4360,f2551])).

fof(f2551,plain,
    ( ~ r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_120 ),
    inference(avatar_component_clause,[],[f2550])).

fof(f4359,plain,
    ( ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(avatar_contradiction_clause,[],[f4358])).

fof(f4358,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4338,f2551])).

fof(f4357,plain,
    ( ~ spl13_2
    | spl13_3
    | spl13_121
    | ~ spl13_160 ),
    inference(avatar_contradiction_clause,[],[f4356])).

fof(f4356,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | spl13_121
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4355,f2562])).

fof(f2562,plain,
    ( ~ m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_121 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f4352,plain,
    ( ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(avatar_contradiction_clause,[],[f4351])).

fof(f4351,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | spl13_120
    | ~ spl13_160 ),
    inference(subsumption_resolution,[],[f4350,f2551])).

fof(f4257,plain,
    ( spl13_100
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4092,f2044,f2033])).

fof(f2033,plain,
    ( spl13_100
  <=> m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f4092,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_101 ),
    inference(resolution,[],[f2046,f50])).

fof(f4256,plain,
    ( spl13_100
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4090,f2044,f2033])).

fof(f4090,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f2046,f50])).

fof(f4255,plain,
    ( spl13_100
    | ~ spl13_101 ),
    inference(avatar_contradiction_clause,[],[f4254])).

fof(f4254,plain,
    ( $false
    | spl13_100
    | ~ spl13_101 ),
    inference(subsumption_resolution,[],[f4090,f2034])).

fof(f2034,plain,
    ( ~ m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_100 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f4253,plain,
    ( spl13_100
    | ~ spl13_101 ),
    inference(avatar_contradiction_clause,[],[f4252])).

fof(f4252,plain,
    ( $false
    | spl13_100
    | ~ spl13_101 ),
    inference(subsumption_resolution,[],[f4092,f2034])).

fof(f4251,plain,
    ( ~ spl13_101
    | spl13_100 ),
    inference(avatar_split_clause,[],[f4120,f2033,f2044])).

fof(f4120,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_100 ),
    inference(unit_resulting_resolution,[],[f2034,f50])).

fof(f4250,plain,
    ( spl13_175
    | ~ spl13_2
    | ~ spl13_109 ),
    inference(avatar_split_clause,[],[f4249,f2232,f85,f4240])).

fof(f4249,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_109 ),
    inference(subsumption_resolution,[],[f4234,f87])).

fof(f4234,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_109 ),
    inference(resolution,[],[f2234,f1358])).

fof(f1358,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f1354])).

fof(f1354,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f1345,f35])).

fof(f1345,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,X2),X0) ) ),
    inference(duplicate_literal_removal,[],[f1340])).

fof(f1340,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f65,f179])).

fof(f179,plain,(
    ! [X6,X8,X7] :
      ( sK3(X6,k1_tarski(X8),X7) = X8
      | ~ r2_hidden(X7,k9_relat_1(X6,k1_tarski(X8)))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f64,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4248,plain,
    ( ~ spl13_2
    | ~ spl13_109
    | spl13_172 ),
    inference(avatar_contradiction_clause,[],[f4247])).

fof(f4247,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_109
    | spl13_172 ),
    inference(subsumption_resolution,[],[f4246,f87])).

fof(f4246,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl13_109
    | spl13_172 ),
    inference(subsumption_resolution,[],[f4233,f4135])).

fof(f4135,plain,
    ( ~ m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | spl13_172 ),
    inference(avatar_component_clause,[],[f4133])).

fof(f4233,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl13_109 ),
    inference(resolution,[],[f2234,f1561])).

fof(f1561,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
      | m1_subset_1(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1557])).

fof(f1557,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
      | m1_subset_1(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f1541,f35])).

fof(f1541,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | m1_subset_1(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1540])).

fof(f1540,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f522,f179])).

fof(f4245,plain,
    ( ~ spl13_2
    | ~ spl13_109
    | spl13_172 ),
    inference(avatar_contradiction_clause,[],[f4244])).

fof(f4244,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_109
    | spl13_172 ),
    inference(subsumption_resolution,[],[f4227,f4135])).

fof(f4227,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_109 ),
    inference(unit_resulting_resolution,[],[f87,f2234,f1561])).

fof(f4243,plain,
    ( spl13_175
    | ~ spl13_2
    | ~ spl13_109 ),
    inference(avatar_split_clause,[],[f4228,f2232,f85,f4240])).

fof(f4228,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_109 ),
    inference(unit_resulting_resolution,[],[f87,f2234,f1358])).

fof(f4220,plain,
    ( spl13_174
    | ~ spl13_173 ),
    inference(avatar_split_clause,[],[f4205,f4179,f4210])).

fof(f4210,plain,
    ( spl13_174
  <=> m1_subset_1(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_174])])).

fof(f4179,plain,
    ( spl13_173
  <=> r2_hidden(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_173])])).

fof(f4205,plain,
    ( m1_subset_1(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_173 ),
    inference(resolution,[],[f4181,f50])).

fof(f4181,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_173 ),
    inference(avatar_component_clause,[],[f4179])).

fof(f4213,plain,
    ( spl13_174
    | ~ spl13_173 ),
    inference(avatar_split_clause,[],[f4200,f4179,f4210])).

fof(f4200,plain,
    ( m1_subset_1(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_173 ),
    inference(unit_resulting_resolution,[],[f4181,f50])).

fof(f4182,plain,
    ( spl13_173
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f4177,f119,f85,f4179])).

fof(f119,plain,
    ( spl13_6
  <=> r2_hidden(sK9(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f4177,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(forward_demodulation,[],[f4147,f150])).

fof(f4147,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),k9_relat_1(sK0,k1_tarski(k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f87,f121,f121,f87,f76,f489])).

fof(f121,plain,
    ( r2_hidden(sK9(sK0),sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f4142,plain,
    ( spl13_110
    | spl13_1
    | spl13_101 ),
    inference(avatar_split_clause,[],[f4124,f2044,f80,f2237])).

fof(f4124,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | spl13_101 ),
    inference(unit_resulting_resolution,[],[f82,f2045,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(resolution,[],[f52,f50])).

fof(f2045,plain,
    ( ~ r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_101 ),
    inference(avatar_component_clause,[],[f2044])).

fof(f4141,plain,
    ( spl13_109
    | spl13_1
    | spl13_101 ),
    inference(avatar_split_clause,[],[f4126,f2044,f80,f2232])).

fof(f4126,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | spl13_101 ),
    inference(unit_resulting_resolution,[],[f82,f2045,f52])).

fof(f4140,plain,
    ( spl13_1
    | spl13_101
    | spl13_110 ),
    inference(avatar_contradiction_clause,[],[f4139])).

fof(f4139,plain,
    ( $false
    | spl13_1
    | spl13_101
    | spl13_110 ),
    inference(subsumption_resolution,[],[f4124,f2238])).

fof(f4138,plain,
    ( spl13_1
    | spl13_101
    | spl13_109 ),
    inference(avatar_contradiction_clause,[],[f4137])).

fof(f4137,plain,
    ( $false
    | spl13_1
    | spl13_101
    | spl13_109 ),
    inference(subsumption_resolution,[],[f4126,f2233])).

fof(f4136,plain,
    ( ~ spl13_172
    | ~ spl13_2
    | spl13_3
    | spl13_101 ),
    inference(avatar_split_clause,[],[f4127,f2044,f90,f85,f4133])).

fof(f4127,plain,
    ( ~ m1_subset_1(k4_tarski(sK1,sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | spl13_3
    | spl13_101 ),
    inference(unit_resulting_resolution,[],[f92,f87,f2045,f303])).

fof(f4118,plain,
    ( spl13_101
    | spl13_58
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f4081,f2033,f1679,f2044])).

fof(f1679,plain,
    ( spl13_58
  <=> v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f4081,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58
    | ~ spl13_100 ),
    inference(unit_resulting_resolution,[],[f1681,f2035,f51])).

fof(f2035,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_100 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f1681,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_58 ),
    inference(avatar_component_clause,[],[f1679])).

fof(f4117,plain,
    ( spl13_101
    | spl13_58
    | ~ spl13_100 ),
    inference(avatar_split_clause,[],[f4116,f2033,f1679,f2044])).

fof(f4116,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58
    | ~ spl13_100 ),
    inference(subsumption_resolution,[],[f4082,f1681])).

fof(f4082,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_100 ),
    inference(resolution,[],[f2035,f51])).

fof(f4115,plain,
    ( spl13_171
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4086,f2044,f90,f85,f4112])).

fof(f4086,plain,
    ( r2_hidden(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2046,f355])).

fof(f4110,plain,
    ( spl13_170
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4087,f2044,f90,f85,f4107])).

fof(f4087,plain,
    ( sK1 = k1_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2046,f61])).

fof(f4105,plain,
    ( spl13_169
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4088,f2044,f90,f85,f4102])).

fof(f4088,plain,
    ( sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2046,f60])).

fof(f4100,plain,
    ( spl13_168
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(avatar_split_clause,[],[f4089,f2044,f90,f85,f4097])).

fof(f4089,plain,
    ( m1_subset_1(sK12(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_101 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2046,f59])).

fof(f4055,plain,
    ( ~ spl13_163
    | spl13_167
    | ~ spl13_2
    | spl13_46 ),
    inference(avatar_split_clause,[],[f4051,f718,f85,f4053,f4034])).

fof(f4034,plain,
    ( spl13_163
  <=> v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_163])])).

fof(f4053,plain,
    ( spl13_167
  <=> ! [X18,X17] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,sK12(X17,k1_tarski(k1_mcart_1(sK9(sK0))),X18)))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(k1_mcart_1(sK9(sK0))),X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_167])])).

fof(f718,plain,
    ( spl13_46
  <=> v1_xboole_0(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f4051,plain,
    ( ! [X17,X18] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,sK12(X17,k1_tarski(k1_mcart_1(sK9(sK0))),X18)))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(k1_mcart_1(sK9(sK0))),X18))
        | ~ v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0)))) )
    | ~ spl13_2
    | spl13_46 ),
    inference(subsumption_resolution,[],[f4030,f95])).

fof(f4030,plain,
    ( ! [X17,X18] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,sK12(X17,k1_tarski(k1_mcart_1(sK9(sK0))),X18)))
        | v1_xboole_0(k1_tarski(k1_mcart_1(sK9(sK0))))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(k1_mcart_1(sK9(sK0))),X18))
        | ~ v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0)))) )
    | ~ spl13_2
    | spl13_46 ),
    inference(resolution,[],[f3636,f355])).

fof(f3636,plain,
    ( ! [X44] :
        ( ~ r2_hidden(X44,k1_tarski(k1_mcart_1(sK9(sK0))))
        | ~ v1_xboole_0(k11_relat_1(sK0,X44)) )
    | ~ spl13_2
    | spl13_46 ),
    inference(superposition,[],[f720,f2796])).

fof(f2796,plain,
    ( ! [X14,X15] :
        ( k11_relat_1(sK0,X14) = k11_relat_1(sK0,X15)
        | ~ r2_hidden(X14,k1_tarski(X15)) )
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f2755,f150])).

fof(f2755,plain,
    ( ! [X14,X15] :
        ( k11_relat_1(sK0,X14) = k9_relat_1(sK0,k1_tarski(X15))
        | ~ r2_hidden(X14,k1_tarski(X15)) )
    | ~ spl13_2 ),
    inference(superposition,[],[f150,f2414])).

fof(f2414,plain,(
    ! [X6,X7] :
      ( k1_tarski(X6) = k1_tarski(X7)
      | ~ r2_hidden(X6,k1_tarski(X7)) ) ),
    inference(subsumption_resolution,[],[f2413,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK11(X0,X1) != X0
      | ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = X1 ) ),
    inference(inner_rewriting,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK11(X0,X1) != X0
      | ~ r2_hidden(sK11(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f2413,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_tarski(X7))
      | k1_tarski(X6) = k1_tarski(X7)
      | sK11(X6,k1_tarski(X7)) = X6 ) ),
    inference(subsumption_resolution,[],[f2409,f74])).

fof(f2409,plain,(
    ! [X6,X7] :
      ( X6 != X7
      | ~ r2_hidden(X6,k1_tarski(X7))
      | k1_tarski(X6) = k1_tarski(X7)
      | sK11(X6,k1_tarski(X7)) = X6 ) ),
    inference(duplicate_literal_removal,[],[f2407])).

fof(f2407,plain,(
    ! [X6,X7] :
      ( X6 != X7
      | ~ r2_hidden(X6,k1_tarski(X7))
      | k1_tarski(X6) = k1_tarski(X7)
      | k1_tarski(X6) = k1_tarski(X7)
      | sK11(X6,k1_tarski(X7)) = X6 ) ),
    inference(superposition,[],[f94,f249])).

fof(f249,plain,(
    ! [X4,X5] :
      ( sK11(X4,k1_tarski(X5)) = X5
      | k1_tarski(X5) = k1_tarski(X4)
      | sK11(X4,k1_tarski(X5)) = X4 ) ),
    inference(resolution,[],[f56,f74])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X1)
      | sK11(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f720,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_46 ),
    inference(avatar_component_clause,[],[f718])).

fof(f4048,plain,
    ( ~ spl13_163
    | spl13_166
    | ~ spl13_2
    | spl13_46 ),
    inference(avatar_split_clause,[],[f4020,f718,f85,f4046,f4034])).

fof(f4046,plain,
    ( spl13_166
  <=> ! [X4] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(X4,sK9(k11_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X4)))))
        | v1_xboole_0(k11_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_166])])).

fof(f4020,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(X4,sK9(k11_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X4)))))
        | ~ v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))))
        | v1_xboole_0(k11_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X4)) )
    | ~ spl13_2
    | spl13_46 ),
    inference(resolution,[],[f3636,f1367])).

fof(f1367,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(X17,sK9(k11_relat_1(X16,X17))),X16)
      | ~ v1_relat_1(X16)
      | v1_xboole_0(k11_relat_1(X16,X17)) ) ),
    inference(resolution,[],[f1358,f116])).

fof(f4044,plain,
    ( ~ spl13_163
    | spl13_165
    | ~ spl13_2
    | spl13_46 ),
    inference(avatar_split_clause,[],[f4019,f718,f85,f4042,f4034])).

fof(f4042,plain,
    ( spl13_165
  <=> ! [X3,X2] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(sK4(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3),sK2(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3))))
        | k9_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X2) = X3
        | r2_hidden(sK2(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_165])])).

fof(f4019,plain,
    ( ! [X2,X3] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(sK4(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3),sK2(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3))))
        | ~ v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))))
        | r2_hidden(sK2(k1_tarski(k1_mcart_1(sK9(sK0))),X2,X3),X3)
        | k9_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X2) = X3 )
    | ~ spl13_2
    | spl13_46 ),
    inference(resolution,[],[f3636,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4040,plain,
    ( ~ spl13_163
    | spl13_164
    | ~ spl13_2
    | spl13_46 ),
    inference(avatar_split_clause,[],[f4018,f718,f85,f4038,f4034])).

fof(f4038,plain,
    ( spl13_164
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(sK3(k1_tarski(k1_mcart_1(sK9(sK0))),X0,X1),X1)))
        | ~ r2_hidden(X1,k9_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_164])])).

fof(f4018,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,k4_tarski(sK3(k1_tarski(k1_mcart_1(sK9(sK0))),X0,X1),X1)))
        | ~ v1_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))))
        | ~ r2_hidden(X1,k9_relat_1(k1_tarski(k1_mcart_1(sK9(sK0))),X0)) )
    | ~ spl13_2
    | spl13_46 ),
    inference(resolution,[],[f3636,f65])).

fof(f4010,plain,
    ( ~ spl13_162
    | spl13_87 ),
    inference(avatar_split_clause,[],[f3967,f1897,f4007])).

fof(f1897,plain,
    ( spl13_87
  <=> k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_87])])).

fof(f3967,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_87 ),
    inference(unit_resulting_resolution,[],[f1898,f74])).

fof(f1898,plain,
    ( k11_relat_1(sK0,sK1) != a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | spl13_87 ),
    inference(avatar_component_clause,[],[f1897])).

fof(f4001,plain,
    ( ~ spl13_161
    | spl13_87 ),
    inference(avatar_split_clause,[],[f3980,f1897,f3998])).

fof(f3980,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_87 ),
    inference(unit_resulting_resolution,[],[f1898,f74])).

fof(f3966,plain,
    ( spl13_159
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(avatar_split_clause,[],[f3965,f1875,f85,f3954])).

fof(f3965,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(subsumption_resolution,[],[f3948,f87])).

fof(f3948,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_85 ),
    inference(resolution,[],[f1877,f1358])).

fof(f3964,plain,
    ( spl13_160
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(avatar_split_clause,[],[f3963,f1875,f85,f3959])).

fof(f3963,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(subsumption_resolution,[],[f3947,f87])).

fof(f3947,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl13_85 ),
    inference(resolution,[],[f1877,f1561])).

fof(f3962,plain,
    ( spl13_160
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(avatar_split_clause,[],[f3942,f1875,f85,f3959])).

fof(f3942,plain,
    ( m1_subset_1(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(unit_resulting_resolution,[],[f87,f1877,f1561])).

fof(f3957,plain,
    ( spl13_159
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(avatar_split_clause,[],[f3943,f1875,f85,f3954])).

fof(f3943,plain,
    ( r2_hidden(k4_tarski(sK1,sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_85 ),
    inference(unit_resulting_resolution,[],[f87,f1877,f1358])).

fof(f3935,plain,
    ( ~ spl13_85
    | spl13_84 ),
    inference(avatar_split_clause,[],[f3920,f1869,f1875])).

fof(f3920,plain,
    ( ~ r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_84 ),
    inference(unit_resulting_resolution,[],[f1870,f50])).

fof(f1870,plain,
    ( ~ m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_84 ),
    inference(avatar_component_clause,[],[f1869])).

fof(f3934,plain,
    ( spl13_1
    | spl13_85
    | spl13_121 ),
    inference(avatar_contradiction_clause,[],[f3933])).

fof(f3933,plain,
    ( $false
    | spl13_1
    | spl13_85
    | spl13_121 ),
    inference(subsumption_resolution,[],[f3924,f2562])).

fof(f3924,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | spl13_85 ),
    inference(unit_resulting_resolution,[],[f82,f1876,f157])).

fof(f3932,plain,
    ( spl13_1
    | spl13_85
    | spl13_120 ),
    inference(avatar_contradiction_clause,[],[f3931])).

fof(f3931,plain,
    ( $false
    | spl13_1
    | spl13_85
    | spl13_120 ),
    inference(subsumption_resolution,[],[f3926,f2551])).

fof(f3926,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | spl13_85 ),
    inference(unit_resulting_resolution,[],[f82,f1876,f52])).

fof(f3918,plain,
    ( ~ spl13_158
    | spl13_79 ),
    inference(avatar_split_clause,[],[f3875,f1838,f3915])).

fof(f1838,plain,
    ( spl13_79
  <=> a_2_0_mcart_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_79])])).

fof(f3875,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_79 ),
    inference(unit_resulting_resolution,[],[f1839,f74])).

fof(f1839,plain,
    ( a_2_0_mcart_1(sK0,sK1) != a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | spl13_79 ),
    inference(avatar_component_clause,[],[f1838])).

fof(f3909,plain,
    ( ~ spl13_157
    | spl13_79 ),
    inference(avatar_split_clause,[],[f3888,f1838,f3906])).

fof(f3888,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | spl13_79 ),
    inference(unit_resulting_resolution,[],[f1839,f74])).

fof(f3828,plain,
    ( ~ spl13_156
    | spl13_15
    | spl13_154 ),
    inference(avatar_split_clause,[],[f3821,f3810,f348,f3825])).

fof(f3825,plain,
    ( spl13_156
  <=> m1_subset_1(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_156])])).

fof(f3810,plain,
    ( spl13_154
  <=> r2_hidden(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f3821,plain,
    ( ~ m1_subset_1(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_15
    | spl13_154 ),
    inference(unit_resulting_resolution,[],[f350,f3812,f51])).

fof(f3812,plain,
    ( ~ r2_hidden(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_154 ),
    inference(avatar_component_clause,[],[f3810])).

fof(f3820,plain,
    ( ~ spl13_155
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_43 ),
    inference(avatar_split_clause,[],[f3779,f676,f397,f85,f3816])).

fof(f676,plain,
    ( spl13_43
  <=> r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).

fof(f3779,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_43 ),
    inference(unit_resulting_resolution,[],[f87,f678,f3334,f63])).

fof(f678,plain,
    ( r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_43 ),
    inference(avatar_component_clause,[],[f676])).

fof(f3819,plain,
    ( ~ spl13_155
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_49 ),
    inference(avatar_split_clause,[],[f3780,f1372,f397,f85,f3816])).

fof(f1372,plain,
    ( spl13_49
  <=> r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_49])])).

fof(f3780,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9(sK0)),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f87,f1374,f3334,f63])).

fof(f1374,plain,
    ( r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_49 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f3814,plain,
    ( ~ spl13_154
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_89 ),
    inference(avatar_split_clause,[],[f3781,f1930,f397,f85,f3810])).

fof(f1930,plain,
    ( spl13_89
  <=> r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).

fof(f3781,plain,
    ( ~ r2_hidden(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_89 ),
    inference(unit_resulting_resolution,[],[f87,f1932,f3334,f63])).

fof(f1932,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_89 ),
    inference(avatar_component_clause,[],[f1930])).

fof(f3813,plain,
    ( ~ spl13_154
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_133 ),
    inference(avatar_split_clause,[],[f3782,f2995,f397,f85,f3810])).

fof(f2995,plain,
    ( spl13_133
  <=> r2_hidden(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_133])])).

fof(f3782,plain,
    ( ~ r2_hidden(sK1,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_21
    | ~ spl13_133 ),
    inference(unit_resulting_resolution,[],[f87,f2997,f3334,f63])).

fof(f2997,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_133 ),
    inference(avatar_component_clause,[],[f2995])).

fof(f3753,plain,
    ( ~ spl13_149
    | spl13_153
    | ~ spl13_2
    | spl13_86 ),
    inference(avatar_split_clause,[],[f3749,f1880,f85,f3751,f3732])).

fof(f3732,plain,
    ( spl13_149
  <=> v1_relat_1(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_149])])).

fof(f3751,plain,
    ( spl13_153
  <=> ! [X18,X17] :
        ( ~ v1_relat_1(k11_relat_1(sK0,sK12(X17,k1_tarski(sK1),X18)))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(sK1),X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_153])])).

fof(f1880,plain,
    ( spl13_86
  <=> v1_relat_1(k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f3749,plain,
    ( ! [X17,X18] :
        ( ~ v1_relat_1(k11_relat_1(sK0,sK12(X17,k1_tarski(sK1),X18)))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(sK1),X18))
        | ~ v1_relat_1(k1_tarski(sK1)) )
    | ~ spl13_2
    | spl13_86 ),
    inference(subsumption_resolution,[],[f3728,f95])).

fof(f3728,plain,
    ( ! [X17,X18] :
        ( ~ v1_relat_1(k11_relat_1(sK0,sK12(X17,k1_tarski(sK1),X18)))
        | v1_xboole_0(k1_tarski(sK1))
        | ~ r2_hidden(X17,a_2_0_mcart_1(k1_tarski(sK1),X18))
        | ~ v1_relat_1(k1_tarski(sK1)) )
    | ~ spl13_2
    | spl13_86 ),
    inference(resolution,[],[f3617,f355])).

fof(f3617,plain,
    ( ! [X25] :
        ( ~ r2_hidden(X25,k1_tarski(sK1))
        | ~ v1_relat_1(k11_relat_1(sK0,X25)) )
    | ~ spl13_2
    | spl13_86 ),
    inference(superposition,[],[f1882,f2796])).

fof(f1882,plain,
    ( ~ v1_relat_1(k11_relat_1(sK0,sK1))
    | spl13_86 ),
    inference(avatar_component_clause,[],[f1880])).

fof(f3746,plain,
    ( ~ spl13_149
    | spl13_152
    | ~ spl13_2
    | spl13_86 ),
    inference(avatar_split_clause,[],[f3718,f1880,f85,f3744,f3732])).

fof(f3744,plain,
    ( spl13_152
  <=> ! [X4] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(X4,sK9(k11_relat_1(k1_tarski(sK1),X4)))))
        | v1_xboole_0(k11_relat_1(k1_tarski(sK1),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f3718,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(X4,sK9(k11_relat_1(k1_tarski(sK1),X4)))))
        | ~ v1_relat_1(k1_tarski(sK1))
        | v1_xboole_0(k11_relat_1(k1_tarski(sK1),X4)) )
    | ~ spl13_2
    | spl13_86 ),
    inference(resolution,[],[f3617,f1367])).

fof(f3742,plain,
    ( ~ spl13_149
    | spl13_151
    | ~ spl13_2
    | spl13_86 ),
    inference(avatar_split_clause,[],[f3717,f1880,f85,f3740,f3732])).

fof(f3740,plain,
    ( spl13_151
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(sK4(k1_tarski(sK1),X2,X3),sK2(k1_tarski(sK1),X2,X3))))
        | k9_relat_1(k1_tarski(sK1),X2) = X3
        | r2_hidden(sK2(k1_tarski(sK1),X2,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_151])])).

fof(f3717,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(sK4(k1_tarski(sK1),X2,X3),sK2(k1_tarski(sK1),X2,X3))))
        | ~ v1_relat_1(k1_tarski(sK1))
        | r2_hidden(sK2(k1_tarski(sK1),X2,X3),X3)
        | k9_relat_1(k1_tarski(sK1),X2) = X3 )
    | ~ spl13_2
    | spl13_86 ),
    inference(resolution,[],[f3617,f37])).

fof(f3738,plain,
    ( ~ spl13_149
    | spl13_150
    | ~ spl13_2
    | spl13_86 ),
    inference(avatar_split_clause,[],[f3716,f1880,f85,f3736,f3732])).

fof(f3736,plain,
    ( spl13_150
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(sK3(k1_tarski(sK1),X0,X1),X1)))
        | ~ r2_hidden(X1,k9_relat_1(k1_tarski(sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f3716,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k11_relat_1(sK0,k4_tarski(sK3(k1_tarski(sK1),X0,X1),X1)))
        | ~ v1_relat_1(k1_tarski(sK1))
        | ~ r2_hidden(X1,k9_relat_1(k1_tarski(sK1),X0)) )
    | ~ spl13_2
    | spl13_86 ),
    inference(resolution,[],[f3617,f65])).

fof(f3498,plain,
    ( ~ spl13_148
    | spl13_130 ),
    inference(avatar_split_clause,[],[f3490,f2948,f3495])).

fof(f3495,plain,
    ( spl13_148
  <=> m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1)),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f2948,plain,
    ( spl13_130
  <=> r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1)),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f3490,plain,
    ( ~ m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1)),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_130 ),
    inference(unit_resulting_resolution,[],[f95,f2950,f51])).

fof(f2950,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1)),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_130 ),
    inference(avatar_component_clause,[],[f2948])).

fof(f3488,plain,
    ( ~ spl13_147
    | spl13_129 ),
    inference(avatar_split_clause,[],[f3480,f2939,f3485])).

fof(f3485,plain,
    ( spl13_147
  <=> m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_147])])).

fof(f2939,plain,
    ( spl13_129
  <=> r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_129])])).

fof(f3480,plain,
    ( ~ m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_129 ),
    inference(unit_resulting_resolution,[],[f95,f2941,f51])).

fof(f2941,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_129 ),
    inference(avatar_component_clause,[],[f2939])).

fof(f3478,plain,
    ( spl13_146
    | spl13_122 ),
    inference(avatar_split_clause,[],[f3463,f2598,f3474])).

fof(f3477,plain,
    ( spl13_146
    | spl13_122 ),
    inference(avatar_split_clause,[],[f3464,f2598,f3474])).

fof(f3459,plain,
    ( ~ spl13_145
    | spl13_128 ),
    inference(avatar_split_clause,[],[f3451,f2905,f3456])).

fof(f3456,plain,
    ( spl13_145
  <=> m1_subset_1(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_145])])).

fof(f2905,plain,
    ( spl13_128
  <=> r2_hidden(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f3451,plain,
    ( ~ m1_subset_1(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_128 ),
    inference(unit_resulting_resolution,[],[f95,f2907,f51])).

fof(f2907,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_128 ),
    inference(avatar_component_clause,[],[f2905])).

fof(f3449,plain,
    ( ~ spl13_144
    | spl13_127 ),
    inference(avatar_split_clause,[],[f3441,f2896,f3446])).

fof(f3446,plain,
    ( spl13_144
  <=> m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f2896,plain,
    ( spl13_127
  <=> r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_127])])).

fof(f3441,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_127 ),
    inference(unit_resulting_resolution,[],[f95,f2898,f51])).

fof(f2898,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_127 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f3432,plain,
    ( ~ spl13_143
    | ~ spl13_21
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f3425,f2157,f397,f3428])).

fof(f3428,plain,
    ( spl13_143
  <=> v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_143])])).

fof(f3425,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_21
    | ~ spl13_108 ),
    inference(resolution,[],[f2158,f399])).

fof(f2158,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_108 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f3431,plain,
    ( ~ spl13_143
    | ~ spl13_21
    | ~ spl13_108 ),
    inference(avatar_split_clause,[],[f3421,f2157,f397,f3428])).

fof(f3421,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_21
    | ~ spl13_108 ),
    inference(unit_resulting_resolution,[],[f399,f2158])).

fof(f3356,plain,
    ( spl13_141
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f3340,f397,f85,f3352])).

fof(f3352,plain,
    ( spl13_141
  <=> k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_141])])).

fof(f3340,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(unit_resulting_resolution,[],[f399,f87,f399,f183])).

fof(f3355,plain,
    ( spl13_141
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f3341,f397,f85,f3352])).

fof(f3341,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(unit_resulting_resolution,[],[f399,f87,f399,f183])).

fof(f3350,plain,
    ( spl13_140
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(avatar_split_clause,[],[f3342,f397,f85,f3347])).

fof(f3347,plain,
    ( spl13_140
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f3342,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))))
    | ~ spl13_2
    | ~ spl13_21 ),
    inference(unit_resulting_resolution,[],[f87,f87,f399,f275])).

fof(f3329,plain,
    ( spl13_139
    | ~ spl13_2
    | ~ spl13_117
    | ~ spl13_118
    | ~ spl13_119 ),
    inference(avatar_split_clause,[],[f3324,f2439,f2434,f2429,f85,f3326])).

fof(f3326,plain,
    ( spl13_139
  <=> k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))) = sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_139])])).

fof(f2429,plain,
    ( spl13_117
  <=> sK9(k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_117])])).

fof(f2434,plain,
    ( spl13_118
  <=> sK1 = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f2439,plain,
    ( spl13_119
  <=> r2_hidden(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_119])])).

fof(f3324,plain,
    ( k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))) = sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)
    | ~ spl13_2
    | ~ spl13_117
    | ~ spl13_118
    | ~ spl13_119 ),
    inference(forward_demodulation,[],[f3323,f2436])).

fof(f2436,plain,
    ( sK1 = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_118 ),
    inference(avatar_component_clause,[],[f2434])).

fof(f3323,plain,
    ( sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)),sK9(k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_117
    | ~ spl13_119 ),
    inference(forward_demodulation,[],[f3318,f2431])).

fof(f2431,plain,
    ( sK9(k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_117 ),
    inference(avatar_component_clause,[],[f2429])).

fof(f3318,plain,
    ( sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)),k2_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_119 ),
    inference(unit_resulting_resolution,[],[f87,f2441,f49])).

fof(f2441,plain,
    ( r2_hidden(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_119 ),
    inference(avatar_component_clause,[],[f2439])).

fof(f3267,plain,
    ( spl13_138
    | ~ spl13_137 ),
    inference(avatar_split_clause,[],[f3260,f3247,f3263])).

fof(f3263,plain,
    ( spl13_138
  <=> m1_subset_1(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f3247,plain,
    ( spl13_137
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_137])])).

fof(f3260,plain,
    ( m1_subset_1(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_137 ),
    inference(resolution,[],[f3249,f50])).

fof(f3249,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_137 ),
    inference(avatar_component_clause,[],[f3247])).

fof(f3266,plain,
    ( spl13_138
    | ~ spl13_137 ),
    inference(avatar_split_clause,[],[f3255,f3247,f3263])).

fof(f3255,plain,
    ( m1_subset_1(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_137 ),
    inference(unit_resulting_resolution,[],[f3249,f50])).

fof(f3250,plain,
    ( spl13_137
    | ~ spl13_2
    | ~ spl13_133 ),
    inference(avatar_split_clause,[],[f3245,f2995,f85,f3247])).

fof(f3245,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_133 ),
    inference(forward_demodulation,[],[f3237,f150])).

fof(f3237,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl13_2
    | ~ spl13_133 ),
    inference(unit_resulting_resolution,[],[f87,f76,f2997,f63])).

fof(f3181,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2132,f1754,f1679])).

fof(f1754,plain,
    ( spl13_73
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_73])])).

fof(f2132,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f1756,f58])).

fof(f1756,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_73 ),
    inference(avatar_component_clause,[],[f1754])).

fof(f3180,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2134,f1754,f1679])).

fof(f2134,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_73 ),
    inference(resolution,[],[f1756,f58])).

fof(f3175,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2307,f1754,f1679])).

fof(f2307,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f1756,f58])).

fof(f3174,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2309,f1754,f1679])).

fof(f2309,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_73 ),
    inference(resolution,[],[f1756,f58])).

fof(f3166,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_80 ),
    inference(avatar_split_clause,[],[f2334,f1843,f85,f1679])).

fof(f1843,plain,
    ( spl13_80
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f2334,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_80 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1844,f275])).

fof(f1844,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_80 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f3165,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_80 ),
    inference(avatar_split_clause,[],[f3164,f1843,f85,f1679])).

fof(f3164,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_80 ),
    inference(subsumption_resolution,[],[f3093,f87])).

fof(f3093,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_80 ),
    inference(duplicate_literal_removal,[],[f2339])).

fof(f2339,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_80 ),
    inference(resolution,[],[f1844,f275])).

fof(f3163,plain,
    ( ~ spl13_58
    | spl13_136
    | ~ spl13_2
    | spl13_80 ),
    inference(avatar_split_clause,[],[f3159,f1843,f85,f3161,f1679])).

fof(f3159,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_80 ),
    inference(subsumption_resolution,[],[f2342,f87])).

fof(f2342,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_80 ),
    inference(superposition,[],[f1844,f183])).

fof(f3158,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_80 ),
    inference(avatar_split_clause,[],[f3157,f1843,f85,f1679])).

fof(f3157,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_80 ),
    inference(subsumption_resolution,[],[f2345,f87])).

fof(f2345,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_80 ),
    inference(duplicate_literal_removal,[],[f2339])).

fof(f3156,plain,
    ( spl13_135
    | ~ spl13_58
    | ~ spl13_2
    | spl13_81 ),
    inference(avatar_split_clause,[],[f3155,f1848,f85,f1679,f3137])).

fof(f3155,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_81 ),
    inference(subsumption_resolution,[],[f3154,f162])).

fof(f3154,plain,
    ( ! [X0] :
        ( a_2_0_mcart_1(sK0,sK1) != X0
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_81 ),
    inference(subsumption_resolution,[],[f2892,f87])).

fof(f2892,plain,
    ( ! [X0] :
        ( a_2_0_mcart_1(sK0,sK1) != X0
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_81 ),
    inference(superposition,[],[f1849,f183])).

fof(f3153,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f2072,f1856,f85,f1679])).

fof(f2072,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_82 ),
    inference(unit_resulting_resolution,[],[f87,f1857,f181])).

fof(f1857,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_82 ),
    inference(avatar_component_clause,[],[f1856])).

fof(f3152,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3151,f1856,f85,f1679])).

fof(f3151,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f2075,f87])).

fof(f2075,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | spl13_82 ),
    inference(resolution,[],[f1857,f181])).

fof(f3150,plain,
    ( ~ spl13_58
    | spl13_135
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3149,f1856,f85,f3137,f1679])).

fof(f3149,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) )
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f3095,f87])).

fof(f3095,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0) )
    | spl13_82 ),
    inference(duplicate_literal_removal,[],[f2076])).

fof(f2076,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_82 ),
    inference(superposition,[],[f1857,f183])).

fof(f3148,plain,
    ( ~ spl13_58
    | spl13_135
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3147,f1856,f85,f3137,f1679])).

fof(f3147,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) )
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f2077,f87])).

fof(f2077,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0) )
    | spl13_82 ),
    inference(duplicate_literal_removal,[],[f2076])).

fof(f3146,plain,
    ( ~ spl13_58
    | spl13_135
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3145,f1856,f85,f3137,f1679])).

fof(f3145,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) )
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f2267,f87])).

fof(f2267,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0) )
    | spl13_82 ),
    inference(duplicate_literal_removal,[],[f2076])).

fof(f3144,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f2269,f1856,f85,f1679])).

fof(f2269,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_82 ),
    inference(unit_resulting_resolution,[],[f87,f1857,f181])).

fof(f3143,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3142,f1856,f85,f1679])).

fof(f3142,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f2273,f87])).

fof(f2273,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | spl13_82 ),
    inference(resolution,[],[f1857,f181])).

fof(f3141,plain,
    ( ~ spl13_58
    | spl13_135
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3140,f1856,f85,f3137,f1679])).

fof(f3140,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) )
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f3096,f87])).

fof(f3096,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0) )
    | spl13_82 ),
    inference(duplicate_literal_removal,[],[f2274])).

fof(f2274,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_82 ),
    inference(superposition,[],[f1857,f183])).

fof(f3139,plain,
    ( ~ spl13_58
    | spl13_135
    | ~ spl13_2
    | spl13_82 ),
    inference(avatar_split_clause,[],[f3135,f1856,f85,f3137,f1679])).

fof(f3135,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1)) )
    | ~ spl13_2
    | spl13_82 ),
    inference(subsumption_resolution,[],[f2275,f87])).

fof(f2275,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0) )
    | spl13_82 ),
    inference(duplicate_literal_removal,[],[f2274])).

fof(f3132,plain,
    ( spl13_73
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(avatar_split_clause,[],[f3131,f2981,f2136,f90,f85,f1754])).

fof(f2136,plain,
    ( spl13_104
  <=> m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f2981,plain,
    ( spl13_131
  <=> sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_131])])).

fof(f3131,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f3130,f234])).

fof(f3130,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f3129,f208])).

fof(f3129,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f2965,f2983])).

fof(f2983,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_131 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f2965,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104 ),
    inference(unit_resulting_resolution,[],[f92,f87,f2138,f78])).

fof(f2138,plain,
    ( m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_104 ),
    inference(avatar_component_clause,[],[f2136])).

fof(f3128,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(avatar_split_clause,[],[f3127,f2981,f2136,f90,f85,f1679])).

fof(f3127,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f3126,f208])).

fof(f3126,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f2964,f2983])).

fof(f2964,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104 ),
    inference(unit_resulting_resolution,[],[f87,f92,f2138,f295])).

fof(f295,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(a_2_0_mcart_1(X2,k1_mcart_1(X3)))
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f78,f58])).

fof(f3120,plain,
    ( spl13_73
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106
    | ~ spl13_131 ),
    inference(avatar_split_clause,[],[f3119,f2981,f2146,f2136,f90,f85,f1754])).

fof(f2146,plain,
    ( spl13_106
  <=> sK1 = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f3119,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f3118,f234])).

fof(f3118,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106
    | ~ spl13_131 ),
    inference(forward_demodulation,[],[f2968,f2983])).

fof(f2968,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106 ),
    inference(forward_demodulation,[],[f2965,f2148])).

fof(f2148,plain,
    ( sK1 = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_106 ),
    inference(avatar_component_clause,[],[f2146])).

fof(f3117,plain,
    ( spl13_73
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_105
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f2969,f2146,f2141,f2136,f90,f85,f1754])).

fof(f2141,plain,
    ( spl13_105
  <=> sK9(a_2_0_mcart_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_105])])).

fof(f2969,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_105
    | ~ spl13_106 ),
    inference(forward_demodulation,[],[f2968,f2143])).

fof(f2143,plain,
    ( sK9(a_2_0_mcart_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_105 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f3116,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106 ),
    inference(avatar_split_clause,[],[f2970,f2146,f2136,f90,f85,f1679])).

fof(f2970,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_104
    | ~ spl13_106 ),
    inference(forward_demodulation,[],[f2964,f2148])).

fof(f3105,plain,
    ( ~ spl13_82
    | spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f3104,f2262,f2257,f1856])).

fof(f3102,plain,
    ( ~ spl13_82
    | ~ spl13_112
    | spl13_113 ),
    inference(avatar_split_clause,[],[f3101,f2322,f2262,f1856])).

fof(f3098,plain,
    ( spl13_102
    | ~ spl13_112
    | ~ spl13_115 ),
    inference(avatar_split_clause,[],[f3097,f2347,f2262,f2079])).

fof(f3079,plain,
    ( spl13_58
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(avatar_split_clause,[],[f3078,f1848,f1843,f1679])).

fof(f3078,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3077,f1850])).

fof(f1850,plain,
    ( a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_81 ),
    inference(avatar_component_clause,[],[f1848])).

fof(f3077,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f1845,f1850])).

fof(f1845,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f1843])).

fof(f3076,plain,
    ( spl13_58
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(avatar_split_clause,[],[f2169,f1848,f1843,f1679])).

fof(f2169,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f2168,f1850])).

fof(f2168,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f1845,f1850])).

fof(f3075,plain,
    ( spl13_58
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(avatar_split_clause,[],[f3074,f1848,f1843,f85,f1679])).

fof(f3074,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3073,f1850])).

fof(f3073,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3072,f1850])).

fof(f3072,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3071,f1850])).

fof(f3071,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f2318,f1850])).

fof(f2318,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1845,f275])).

fof(f3066,plain,
    ( spl13_58
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(avatar_split_clause,[],[f3065,f1848,f1843,f85,f1679])).

fof(f3065,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3064,f1850])).

fof(f3064,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f3063,f1850])).

fof(f3063,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(forward_demodulation,[],[f2315,f1850])).

fof(f2315,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(unit_resulting_resolution,[],[f87,f1845,f181])).

fof(f3053,plain,
    ( ~ spl13_81
    | spl13_128 ),
    inference(avatar_contradiction_clause,[],[f3052])).

fof(f3052,plain,
    ( $false
    | ~ spl13_81
    | spl13_128 ),
    inference(subsumption_resolution,[],[f3047,f76])).

fof(f3047,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_81
    | spl13_128 ),
    inference(backward_demodulation,[],[f2907,f1850])).

fof(f3051,plain,
    ( ~ spl13_81
    | spl13_127 ),
    inference(avatar_contradiction_clause,[],[f3050])).

fof(f3050,plain,
    ( $false
    | ~ spl13_81
    | spl13_127 ),
    inference(subsumption_resolution,[],[f3046,f76])).

fof(f3046,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_81
    | spl13_127 ),
    inference(backward_demodulation,[],[f2898,f1850])).

fof(f3049,plain,
    ( ~ spl13_73
    | ~ spl13_81
    | spl13_102 ),
    inference(avatar_split_clause,[],[f3043,f2079,f1848,f1754])).

fof(f3043,plain,
    ( ~ r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_81
    | spl13_102 ),
    inference(backward_demodulation,[],[f2080,f1850])).

fof(f2080,plain,
    ( ~ r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_102 ),
    inference(avatar_component_clause,[],[f2079])).

fof(f3048,plain,
    ( spl13_58
    | ~ spl13_81
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f3042,f1856,f1848,f1679])).

fof(f3042,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_81
    | ~ spl13_82 ),
    inference(backward_demodulation,[],[f1858,f1850])).

fof(f3039,plain,
    ( spl13_58
    | ~ spl13_81
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f2163,f1856,f1848,f1679])).

fof(f2163,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_81
    | ~ spl13_82 ),
    inference(backward_demodulation,[],[f1858,f1850])).

fof(f3038,plain,
    ( ~ spl13_73
    | ~ spl13_81
    | spl13_102 ),
    inference(avatar_split_clause,[],[f2164,f2079,f1848,f1754])).

fof(f2164,plain,
    ( ~ r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_81
    | spl13_102 ),
    inference(backward_demodulation,[],[f2080,f1850])).

fof(f3031,plain,
    ( spl13_82
    | ~ spl13_111
    | ~ spl13_112 ),
    inference(avatar_split_clause,[],[f3030,f2262,f2257,f1856])).

fof(f3028,plain,
    ( ~ spl13_102
    | ~ spl13_112
    | spl13_115 ),
    inference(avatar_split_clause,[],[f3027,f2347,f2262,f2079])).

fof(f3024,plain,
    ( spl13_80
    | ~ spl13_113
    | ~ spl13_114 ),
    inference(avatar_split_clause,[],[f3023,f2327,f2322,f1843])).

fof(f3021,plain,
    ( ~ spl13_82
    | spl13_108
    | ~ spl13_2
    | spl13_75 ),
    inference(avatar_split_clause,[],[f3020,f1818,f85,f2157,f1856])).

fof(f1818,plain,
    ( spl13_75
  <=> v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_75])])).

fof(f3020,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_75 ),
    inference(subsumption_resolution,[],[f2353,f87])).

fof(f2353,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_75 ),
    inference(superposition,[],[f1820,f183])).

fof(f1820,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_75 ),
    inference(avatar_component_clause,[],[f1818])).

fof(f3019,plain,
    ( ~ spl13_58
    | spl13_108
    | ~ spl13_2
    | spl13_76 ),
    inference(avatar_split_clause,[],[f3018,f1823,f85,f2157,f1679])).

fof(f1823,plain,
    ( spl13_76
  <=> v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f3018,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_76 ),
    inference(subsumption_resolution,[],[f2276,f87])).

fof(f2276,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_76 ),
    inference(superposition,[],[f1825,f183])).

fof(f1825,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_76 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f3017,plain,
    ( ~ spl13_58
    | spl13_134
    | ~ spl13_2
    | spl13_75 ),
    inference(avatar_split_clause,[],[f3013,f1818,f85,f3015,f1679])).

fof(f3015,plain,
    ( spl13_134
  <=> ! [X0] :
        ( ~ v1_relat_1(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f3013,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_75 ),
    inference(subsumption_resolution,[],[f2352,f87])).

fof(f2352,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k9_relat_1(sK0,X0))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_75 ),
    inference(superposition,[],[f1820,f183])).

fof(f3012,plain,
    ( ~ spl13_58
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2422,f1945,f1679])).

fof(f1945,plain,
    ( spl13_92
  <=> r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f2422,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(resolution,[],[f1947,f58])).

fof(f1947,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f1945])).

fof(f3011,plain,
    ( ~ spl13_58
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2420,f1945,f1679])).

fof(f2420,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f1947,f58])).

fof(f3010,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2385,f1935,f90,f85,f1679])).

fof(f1935,plain,
    ( spl13_90
  <=> m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f2385,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2375,f208])).

fof(f2375,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1937,f295])).

fof(f1937,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f1935])).

fof(f3009,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3008,f1935,f90,f85,f1679])).

fof(f3008,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f3007,f87])).

fof(f3007,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f2379,f92])).

fof(f2379,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl13_90 ),
    inference(resolution,[],[f1937,f336])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_tarski(X0,X1),X2)
      | ~ v1_xboole_0(a_2_0_mcart_1(X2,X0))
      | v1_xboole_0(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f295,f208])).

fof(f3006,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2373,f1935,f90,f85,f1679])).

fof(f2373,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1937,f336])).

fof(f3005,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2657,f1935,f90,f85,f1679])).

fof(f2657,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2649,f208])).

fof(f2649,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1937,f295])).

fof(f3004,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2647,f1935,f90,f85,f1679])).

fof(f2647,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1937,f336])).

fof(f3003,plain,
    ( ~ spl13_58
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f3002,f1935,f90,f85,f1679])).

fof(f3002,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f3001,f87])).

fof(f3001,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f2653,f92])).

fof(f2653,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl13_90 ),
    inference(resolution,[],[f1937,f336])).

fof(f3000,plain,
    ( ~ spl13_58
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2667,f1945,f1679])).

fof(f2667,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f1947,f58])).

fof(f2999,plain,
    ( ~ spl13_58
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2669,f1945,f1679])).

fof(f2669,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(resolution,[],[f1947,f58])).

fof(f2998,plain,
    ( spl13_133
    | ~ spl13_107
    | ~ spl13_131 ),
    inference(avatar_split_clause,[],[f2988,f2981,f2151,f2995])).

fof(f2151,plain,
    ( spl13_107
  <=> r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_107])])).

fof(f2988,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_107
    | ~ spl13_131 ),
    inference(backward_demodulation,[],[f2153,f2983])).

fof(f2153,plain,
    ( r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_107 ),
    inference(avatar_component_clause,[],[f2151])).

fof(f2993,plain,
    ( spl13_132
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(avatar_split_clause,[],[f2985,f2981,f2136,f2990])).

fof(f2990,plain,
    ( spl13_132
  <=> m1_subset_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f2985,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1))),sK0)
    | ~ spl13_104
    | ~ spl13_131 ),
    inference(backward_demodulation,[],[f2138,f2983])).

fof(f2984,plain,
    ( spl13_131
    | ~ spl13_2
    | ~ spl13_105
    | ~ spl13_106
    | ~ spl13_107 ),
    inference(avatar_split_clause,[],[f2979,f2151,f2146,f2141,f85,f2981])).

fof(f2979,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1) = k4_tarski(sK1,sK9(a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_105
    | ~ spl13_106
    | ~ spl13_107 ),
    inference(forward_demodulation,[],[f2978,f2148])).

fof(f2978,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)),sK9(a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_105
    | ~ spl13_107 ),
    inference(forward_demodulation,[],[f2973,f2143])).

fof(f2973,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)),k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_107 ),
    inference(unit_resulting_resolution,[],[f87,f2153,f49])).

fof(f2951,plain,
    ( ~ spl13_130
    | spl13_98 ),
    inference(avatar_split_clause,[],[f2909,f2011,f2948])).

fof(f2909,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1)),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_98 ),
    inference(unit_resulting_resolution,[],[f2012,f74])).

fof(f2942,plain,
    ( ~ spl13_129
    | spl13_98 ),
    inference(avatar_split_clause,[],[f2922,f2011,f2939])).

fof(f2922,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_98 ),
    inference(unit_resulting_resolution,[],[f2012,f74])).

fof(f2908,plain,
    ( ~ spl13_128
    | spl13_81 ),
    inference(avatar_split_clause,[],[f2866,f1848,f2905])).

fof(f2866,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_81 ),
    inference(unit_resulting_resolution,[],[f1849,f74])).

fof(f2899,plain,
    ( ~ spl13_127
    | spl13_81 ),
    inference(avatar_split_clause,[],[f2879,f1848,f2896])).

fof(f2879,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_81 ),
    inference(unit_resulting_resolution,[],[f1849,f74])).

fof(f2713,plain,
    ( spl13_126
    | spl13_97 ),
    inference(avatar_split_clause,[],[f2699,f2006,f2709])).

fof(f2699,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_97 ),
    inference(unit_resulting_resolution,[],[f48,f2007,f51])).

fof(f2007,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_97 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2712,plain,
    ( spl13_126
    | spl13_97 ),
    inference(avatar_split_clause,[],[f2700,f2006,f2709])).

fof(f2700,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | spl13_97 ),
    inference(unit_resulting_resolution,[],[f2007,f116])).

fof(f2695,plain,
    ( ~ spl13_2
    | ~ spl13_97
    | spl13_122 ),
    inference(avatar_contradiction_clause,[],[f2694])).

fof(f2694,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_97
    | spl13_122 ),
    inference(subsumption_resolution,[],[f2677,f2599])).

fof(f2677,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f87,f2008,f181])).

fof(f2008,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_97 ),
    inference(avatar_component_clause,[],[f2006])).

fof(f2693,plain,
    ( spl13_125
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(avatar_split_clause,[],[f2678,f2006,f85,f2689])).

fof(f2678,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f2008,f87,f2008,f183])).

fof(f2692,plain,
    ( spl13_125
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(avatar_split_clause,[],[f2679,f2006,f85,f2689])).

fof(f2679,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f2008,f87,f2008,f183])).

fof(f2687,plain,
    ( spl13_124
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(avatar_split_clause,[],[f2680,f2006,f85,f2684])).

fof(f2680,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | ~ spl13_97 ),
    inference(unit_resulting_resolution,[],[f87,f87,f2008,f275])).

fof(f2607,plain,
    ( spl13_123
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f2593,f2019,f85,f2603])).

fof(f2593,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f2021,f87,f2021,f183])).

fof(f2606,plain,
    ( spl13_123
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f2594,f2019,f85,f2603])).

fof(f2594,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f2021,f87,f2021,f183])).

fof(f2601,plain,
    ( spl13_122
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f2595,f2019,f85,f2598])).

fof(f2595,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_99 ),
    inference(unit_resulting_resolution,[],[f87,f87,f2021,f275])).

fof(f2579,plain,
    ( ~ spl13_83
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2357,f1924,f1861])).

fof(f1924,plain,
    ( spl13_88
  <=> r2_hidden(sK9(k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f2357,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_88 ),
    inference(unit_resulting_resolution,[],[f1926,f58])).

fof(f1926,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_88 ),
    inference(avatar_component_clause,[],[f1924])).

fof(f2578,plain,
    ( ~ spl13_83
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2361,f1924,f1861])).

fof(f2361,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_88 ),
    inference(resolution,[],[f1926,f58])).

fof(f2577,plain,
    ( spl13_88
    | ~ spl13_2
    | ~ spl13_89 ),
    inference(avatar_split_clause,[],[f2370,f1930,f85,f1924])).

fof(f2370,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_89 ),
    inference(forward_demodulation,[],[f2362,f150])).

fof(f2362,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl13_2
    | ~ spl13_89 ),
    inference(unit_resulting_resolution,[],[f87,f76,f1932,f63])).

fof(f2575,plain,
    ( spl13_89
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2377,f1935,f90,f1930])).

fof(f2377,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f92,f1937,f51])).

fof(f2574,plain,
    ( spl13_89
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2573,f1935,f90,f1930])).

fof(f2573,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f2380,f92])).

fof(f2380,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_90 ),
    inference(resolution,[],[f1937,f51])).

fof(f2572,plain,
    ( spl13_91
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2419,f1945,f1940])).

fof(f1940,plain,
    ( spl13_91
  <=> m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_91])])).

fof(f2419,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f1947,f50])).

fof(f2571,plain,
    ( spl13_91
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2421,f1945,f1940])).

fof(f2421,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_92 ),
    inference(resolution,[],[f1947,f50])).

fof(f2567,plain,
    ( spl13_121
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2524,f1861,f80,f2561])).

fof(f2524,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f82,f1949,f157])).

fof(f1949,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK0,sK1))
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f1862,f58])).

fof(f1862,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_83 ),
    inference(avatar_component_clause,[],[f1861])).

fof(f2566,plain,
    ( spl13_121
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2565,f1861,f80,f2561])).

fof(f2565,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f2525,f780])).

fof(f780,plain,
    ( ! [X0] : a_2_0_mcart_1(sK0,sK1) = sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f82,f771])).

fof(f771,plain,(
    ! [X30,X28,X29] :
      ( sK5(k4_tarski(X28,X29),X30) = X28
      | X28 = X30 ) ),
    inference(forward_demodulation,[],[f763,f208])).

fof(f763,plain,(
    ! [X30,X28,X29] :
      ( sK5(k4_tarski(X28,X29),X30) = k1_mcart_1(k4_tarski(X28,X29))
      | X28 = X30 ) ),
    inference(superposition,[],[f208,f210])).

fof(f210,plain,(
    ! [X2,X3,X1] :
      ( k4_tarski(X1,X2) = k4_tarski(sK5(k4_tarski(X1,X2),X3),sK6(k4_tarski(X1,X2),X3))
      | X1 = X3 ) ),
    inference(backward_demodulation,[],[f67,f208])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( k4_tarski(X1,X2) = k4_tarski(sK5(k4_tarski(X1,X2),X3),sK6(k4_tarski(X1,X2),X3))
      | k1_mcart_1(k4_tarski(X1,X2)) = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(sK5(X0,X3),sK6(X0,X3)) = X0
      | k1_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2525,plain,
    ( ! [X0] : m1_subset_1(sK10(k11_relat_1(sK0,sK1),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1))),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f214,f1949,f157])).

fof(f214,plain,
    ( ! [X0] : k11_relat_1(sK0,sK1) != sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f82,f211])).

fof(f211,plain,(
    ! [X2,X3,X1] :
      ( sK5(k4_tarski(X1,X2),X3) != X3
      | X1 = X3 ) ),
    inference(backward_demodulation,[],[f66,f208])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( sK5(k4_tarski(X1,X2),X3) != X3
      | k1_mcart_1(k4_tarski(X1,X2)) = X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | sK5(X0,X3) != X3
      | k1_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2564,plain,
    ( spl13_121
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2559,f1861,f80,f2561])).

fof(f2559,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f2526,f945])).

fof(f945,plain,
    ( ! [X1] : a_2_0_mcart_1(sK0,sK1) = sK8(k4_tarski(X1,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1 ),
    inference(forward_demodulation,[],[f925,f780])).

fof(f925,plain,
    ( ! [X0,X1] : sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)) = sK8(k4_tarski(X1,sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f896])).

fof(f896,plain,(
    ! [X43,X44,X42] :
      ( sK8(k4_tarski(X42,X43),X44) = X43
      | X43 = X44 ) ),
    inference(forward_demodulation,[],[f885,f234])).

fof(f885,plain,(
    ! [X43,X44,X42] :
      ( sK8(k4_tarski(X42,X43),X44) = k2_mcart_1(k4_tarski(X42,X43))
      | X43 = X44 ) ),
    inference(superposition,[],[f234,f236])).

fof(f236,plain,(
    ! [X2,X3,X1] :
      ( k4_tarski(X1,X2) = k4_tarski(sK7(k4_tarski(X1,X2),X3),sK8(k4_tarski(X1,X2),X3))
      | X2 = X3 ) ),
    inference(backward_demodulation,[],[f71,f234])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( k4_tarski(X1,X2) = k4_tarski(sK7(k4_tarski(X1,X2),X3),sK8(k4_tarski(X1,X2),X3))
      | k2_mcart_1(k4_tarski(X1,X2)) = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(sK7(X0,X3),sK8(X0,X3)) = X0
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2526,plain,
    ( ! [X0] : m1_subset_1(sK10(k11_relat_1(sK0,sK1),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f242,f1949,f157])).

fof(f242,plain,
    ( ! [X0] : k11_relat_1(sK0,sK1) != sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f82,f237])).

fof(f237,plain,(
    ! [X2,X3,X1] :
      ( sK8(k4_tarski(X1,X2),X3) != X3
      | X2 = X3 ) ),
    inference(backward_demodulation,[],[f70,f234])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( sK8(k4_tarski(X1,X2),X3) != X3
      | k2_mcart_1(k4_tarski(X1,X2)) = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | sK8(X0,X3) != X3
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2556,plain,
    ( spl13_120
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2531,f1861,f80,f2550])).

fof(f2531,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f82,f1949,f52])).

fof(f2555,plain,
    ( spl13_120
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2554,f1861,f80,f2550])).

fof(f2554,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f2532,f780])).

fof(f2532,plain,
    ( ! [X0] : r2_hidden(sK10(k11_relat_1(sK0,sK1),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1))),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f214,f1949,f52])).

fof(f2553,plain,
    ( spl13_120
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2548,f1861,f80,f2550])).

fof(f2548,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f2533,f945])).

fof(f2533,plain,
    ( ! [X0] : r2_hidden(sK10(k11_relat_1(sK0,sK1),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f242,f1949,f52])).

fof(f2464,plain,
    ( spl13_83
    | ~ spl13_97
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2463,f2011,f2006,f1861])).

fof(f2463,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_97
    | ~ spl13_98 ),
    inference(forward_demodulation,[],[f2462,f2013])).

fof(f2013,plain,
    ( k11_relat_1(sK0,sK1) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f2011])).

fof(f2462,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_97
    | ~ spl13_98 ),
    inference(forward_demodulation,[],[f2008,f2013])).

fof(f2461,plain,
    ( spl13_83
    | ~ spl13_98
    | ~ spl13_99 ),
    inference(avatar_split_clause,[],[f2458,f2019,f2011,f1861])).

fof(f2458,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_98
    | ~ spl13_99 ),
    inference(backward_demodulation,[],[f2021,f2013])).

fof(f2454,plain,
    ( spl13_92
    | spl13_58
    | ~ spl13_91 ),
    inference(avatar_split_clause,[],[f2401,f1940,f1679,f1945])).

fof(f2401,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58
    | ~ spl13_91 ),
    inference(unit_resulting_resolution,[],[f1681,f1942,f51])).

fof(f1942,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_91 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f2453,plain,
    ( spl13_92
    | spl13_58
    | ~ spl13_91 ),
    inference(avatar_split_clause,[],[f2452,f1940,f1679,f1945])).

fof(f2452,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58
    | ~ spl13_91 ),
    inference(subsumption_resolution,[],[f2402,f1681])).

fof(f2402,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_91 ),
    inference(resolution,[],[f1942,f51])).

fof(f2451,plain,
    ( spl13_90
    | ~ spl13_2
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2354,f1924,f85,f1935])).

fof(f2354,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_88 ),
    inference(unit_resulting_resolution,[],[f87,f1926,f1561])).

fof(f2450,plain,
    ( spl13_90
    | ~ spl13_2
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2449,f1924,f85,f1935])).

fof(f2449,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | ~ spl13_88 ),
    inference(subsumption_resolution,[],[f2358,f87])).

fof(f2358,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl13_88 ),
    inference(resolution,[],[f1926,f1561])).

fof(f2448,plain,
    ( spl13_90
    | ~ spl13_89 ),
    inference(avatar_split_clause,[],[f2364,f1930,f1935])).

fof(f2364,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_89 ),
    inference(unit_resulting_resolution,[],[f1932,f50])).

fof(f2447,plain,
    ( spl13_90
    | ~ spl13_89 ),
    inference(avatar_split_clause,[],[f2367,f1930,f1935])).

fof(f2367,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_89 ),
    inference(resolution,[],[f1932,f50])).

fof(f2446,plain,
    ( ~ spl13_83
    | spl13_108
    | ~ spl13_2
    | spl13_95 ),
    inference(avatar_split_clause,[],[f2445,f1994,f85,f2157,f1861])).

fof(f1994,plain,
    ( spl13_95
  <=> v1_relat_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_95])])).

fof(f2445,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k11_relat_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_95 ),
    inference(subsumption_resolution,[],[f2085,f87])).

fof(f2085,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(k11_relat_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_95 ),
    inference(superposition,[],[f1996,f183])).

fof(f1996,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_95 ),
    inference(avatar_component_clause,[],[f1994])).

fof(f2444,plain,
    ( ~ spl13_83
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2357,f1924,f1861])).

fof(f2443,plain,
    ( ~ spl13_83
    | ~ spl13_88 ),
    inference(avatar_split_clause,[],[f2361,f1924,f1861])).

fof(f2442,plain,
    ( spl13_119
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2415,f1945,f90,f85,f2439])).

fof(f2415,plain,
    ( r2_hidden(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1947,f355])).

fof(f2437,plain,
    ( spl13_118
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2416,f1945,f90,f85,f2434])).

fof(f2416,plain,
    ( sK1 = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1947,f61])).

fof(f2432,plain,
    ( spl13_117
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2417,f1945,f90,f85,f2429])).

fof(f2417,plain,
    ( sK9(k11_relat_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1947,f60])).

fof(f2427,plain,
    ( spl13_116
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(avatar_split_clause,[],[f2418,f1945,f90,f85,f2424])).

fof(f2424,plain,
    ( spl13_116
  <=> m1_subset_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f2418,plain,
    ( m1_subset_1(sK12(sK9(k11_relat_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_92 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1947,f59])).

fof(f2400,plain,
    ( spl13_92
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2382,f1935,f90,f85,f1945])).

fof(f2382,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2381,f234])).

fof(f2381,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2376,f208])).

fof(f2376,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f92,f87,f1937,f78])).

fof(f2399,plain,
    ( spl13_92
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2372,f1935,f90,f85,f1945])).

fof(f2372,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f92,f87,f1937,f303])).

fof(f2398,plain,
    ( spl13_92
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2397,f1935,f90,f85,f1945])).

fof(f2397,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f2392,f92])).

fof(f2392,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl13_2
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f2378,f87])).

fof(f2378,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl13_90 ),
    inference(resolution,[],[f1937,f303])).

fof(f2396,plain,
    ( spl13_91
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(avatar_split_clause,[],[f2387,f1935,f90,f85,f1940])).

fof(f2387,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2386,f234])).

fof(f2386,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(forward_demodulation,[],[f2374,f208])).

fof(f2374,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1)))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1937,f294])).

fof(f2395,plain,
    ( ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(avatar_contradiction_clause,[],[f2394])).

fof(f2394,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(subsumption_resolution,[],[f2393,f92])).

fof(f2393,plain,
    ( v1_xboole_0(sK0)
    | ~ spl13_2
    | ~ spl13_90
    | spl13_92 ),
    inference(subsumption_resolution,[],[f2392,f1946])).

fof(f1946,plain,
    ( ~ r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_92 ),
    inference(avatar_component_clause,[],[f1945])).

fof(f2391,plain,
    ( ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(avatar_contradiction_clause,[],[f2390])).

fof(f2390,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(subsumption_resolution,[],[f2372,f1946])).

fof(f2389,plain,
    ( ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_91 ),
    inference(avatar_contradiction_clause,[],[f2388])).

fof(f2388,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_91 ),
    inference(subsumption_resolution,[],[f2387,f1941])).

fof(f1941,plain,
    ( ~ m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_91 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f2384,plain,
    ( ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(avatar_contradiction_clause,[],[f2383])).

fof(f2383,plain,
    ( $false
    | ~ spl13_2
    | spl13_3
    | ~ spl13_90
    | spl13_92 ),
    inference(subsumption_resolution,[],[f2382,f1946])).

fof(f2351,plain,
    ( spl13_115
    | spl13_80 ),
    inference(avatar_split_clause,[],[f2337,f1843,f2347])).

fof(f2337,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_80 ),
    inference(unit_resulting_resolution,[],[f48,f1844,f51])).

fof(f2350,plain,
    ( spl13_115
    | spl13_80 ),
    inference(avatar_split_clause,[],[f2338,f1843,f2347])).

fof(f2338,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))),k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | spl13_80 ),
    inference(unit_resulting_resolution,[],[f1844,f116])).

fof(f2333,plain,
    ( ~ spl13_2
    | ~ spl13_80
    | spl13_111 ),
    inference(avatar_contradiction_clause,[],[f2332])).

fof(f2332,plain,
    ( $false
    | ~ spl13_2
    | ~ spl13_80
    | spl13_111 ),
    inference(subsumption_resolution,[],[f2315,f2258])).

fof(f2331,plain,
    ( spl13_114
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f2316,f1843,f85,f2327])).

fof(f2316,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(unit_resulting_resolution,[],[f1845,f87,f1845,f183])).

fof(f2330,plain,
    ( spl13_114
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f2317,f1843,f85,f2327])).

fof(f2317,plain,
    ( k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))) = k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(unit_resulting_resolution,[],[f1845,f87,f1845,f183])).

fof(f2325,plain,
    ( spl13_113
    | ~ spl13_2
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f2318,f1843,f85,f2322])).

fof(f2266,plain,
    ( spl13_112
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f2252,f1856,f85,f2262])).

fof(f2252,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f1858,f87,f1858,f183])).

fof(f2265,plain,
    ( spl13_112
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f2253,f1856,f85,f2262])).

fof(f2253,plain,
    ( k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) = k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f1858,f87,f1858,f183])).

fof(f2260,plain,
    ( spl13_111
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f2254,f1856,f85,f2257])).

fof(f2254,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))))
    | ~ spl13_2
    | ~ spl13_82 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1858,f275])).

fof(f2243,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2132,f1754,f1679])).

fof(f2242,plain,
    ( ~ spl13_58
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2134,f1754,f1679])).

fof(f2240,plain,
    ( spl13_110
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f2213,f1679,f80,f2237])).

fof(f2213,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1773,f157])).

fof(f1773,plain,
    ( ! [X0] : ~ r2_hidden(X0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f58])).

fof(f1680,plain,
    ( v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f1679])).

fof(f2235,plain,
    ( spl13_109
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f2216,f1679,f80,f2232])).

fof(f2216,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1773,f52])).

fof(f2170,plain,
    ( spl13_58
    | ~ spl13_80
    | ~ spl13_81 ),
    inference(avatar_split_clause,[],[f2169,f1848,f1843,f1679])).

fof(f2167,plain,
    ( ~ spl13_73
    | ~ spl13_81
    | spl13_102 ),
    inference(avatar_split_clause,[],[f2164,f2079,f1848,f1754])).

fof(f2166,plain,
    ( spl13_58
    | ~ spl13_81
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f2163,f1856,f1848,f1679])).

fof(f2159,plain,
    ( ~ spl13_58
    | spl13_108
    | ~ spl13_2
    | spl13_76 ),
    inference(avatar_split_clause,[],[f2155,f1823,f85,f2157,f1679])).

fof(f2155,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_76 ),
    inference(subsumption_resolution,[],[f2084,f87])).

fof(f2084,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_76 ),
    inference(superposition,[],[f1825,f183])).

fof(f2154,plain,
    ( spl13_107
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2127,f1754,f90,f85,f2151])).

fof(f2127,plain,
    ( r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1756,f355])).

fof(f2149,plain,
    ( spl13_106
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2128,f1754,f90,f85,f2146])).

fof(f2128,plain,
    ( sK1 = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1756,f61])).

fof(f2144,plain,
    ( spl13_105
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2129,f1754,f90,f85,f2141])).

fof(f2129,plain,
    ( sK9(a_2_0_mcart_1(sK0,sK1)) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1756,f60])).

fof(f2139,plain,
    ( spl13_104
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(avatar_split_clause,[],[f2130,f1754,f90,f85,f2136])).

fof(f2130,plain,
    ( m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,sK1)),sK0,sK1),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_73 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1756,f59])).

fof(f2097,plain,
    ( spl13_103
    | spl13_99 ),
    inference(avatar_split_clause,[],[f2087,f2019,f2093])).

fof(f2087,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_99 ),
    inference(unit_resulting_resolution,[],[f48,f2020,f51])).

fof(f2020,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_99 ),
    inference(avatar_component_clause,[],[f2019])).

fof(f2096,plain,
    ( spl13_103
    | spl13_99 ),
    inference(avatar_split_clause,[],[f2088,f2019,f2093])).

fof(f2088,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,k11_relat_1(sK0,sK1))),k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | spl13_99 ),
    inference(unit_resulting_resolution,[],[f2020,f116])).

fof(f2083,plain,
    ( spl13_102
    | spl13_82 ),
    inference(avatar_split_clause,[],[f2073,f1856,f2079])).

fof(f2073,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_82 ),
    inference(unit_resulting_resolution,[],[f48,f1857,f51])).

fof(f2082,plain,
    ( spl13_102
    | spl13_82 ),
    inference(avatar_split_clause,[],[f2074,f1856,f2079])).

fof(f2074,plain,
    ( r2_hidden(sK9(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))),k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | spl13_82 ),
    inference(unit_resulting_resolution,[],[f1857,f116])).

fof(f2050,plain,
    ( spl13_101
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1950,f1861,f80,f2044])).

fof(f1950,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f82,f1862,f158])).

fof(f2049,plain,
    ( spl13_101
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2048,f1861,f80,f2044])).

fof(f2048,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f1951,f780])).

fof(f1951,plain,
    ( ! [X0] : r2_hidden(sK10(sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f214,f1862,f158])).

fof(f2047,plain,
    ( spl13_101
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2042,f1861,f80,f2044])).

fof(f2042,plain,
    ( r2_hidden(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f1952,f945])).

fof(f1952,plain,
    ( ! [X0] : r2_hidden(sK10(sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f242,f1862,f158])).

fof(f2041,plain,
    ( ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(avatar_contradiction_clause,[],[f2040])).

fof(f2040,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(subsumption_resolution,[],[f1953,f1898])).

fof(f1953,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f375,f1862,f158])).

fof(f375,plain,
    ( ! [X0] : ~ r2_hidden(X0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_15 ),
    inference(unit_resulting_resolution,[],[f349,f58])).

fof(f349,plain,
    ( v1_xboole_0(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f348])).

fof(f2039,plain,
    ( spl13_100
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1954,f1861,f80,f2033])).

fof(f1954,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f82,f1862,f161])).

fof(f2038,plain,
    ( spl13_100
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2037,f1861,f80,f2033])).

fof(f2037,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f1955,f780])).

fof(f1955,plain,
    ( ! [X0] : m1_subset_1(sK10(sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f214,f1862,f161])).

fof(f2036,plain,
    ( spl13_100
    | spl13_1
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f2031,f1861,f80,f2033])).

fof(f2031,plain,
    ( m1_subset_1(sK10(a_2_0_mcart_1(sK0,sK1),k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_83 ),
    inference(forward_demodulation,[],[f1956,f945])).

fof(f1956,plain,
    ( ! [X0] : m1_subset_1(sK10(sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1)),sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f242,f1862,f161])).

fof(f2030,plain,
    ( ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(avatar_contradiction_clause,[],[f2029])).

fof(f2029,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(subsumption_resolution,[],[f1957,f1898])).

fof(f1957,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f349,f1862,f162])).

fof(f2026,plain,
    ( ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(avatar_contradiction_clause,[],[f2025])).

fof(f2025,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(subsumption_resolution,[],[f1962,f1898])).

fof(f1962,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f349,f1862,f162])).

fof(f2022,plain,
    ( spl13_99
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1969,f1861,f85,f2019])).

fof(f1969,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1862,f181])).

fof(f2017,plain,
    ( spl13_93
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1970,f1861,f348,f85,f1984])).

fof(f1984,plain,
    ( spl13_93
  <=> a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_93])])).

fof(f1970,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f349,f87,f1862,f183])).

fof(f2016,plain,
    ( spl13_98
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1971,f1861,f85,f2011])).

fof(f1971,plain,
    ( k11_relat_1(sK0,sK1) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f1862,f87,f1862,f183])).

fof(f2015,plain,
    ( spl13_96
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1972,f1861,f348,f85,f1999])).

fof(f1999,plain,
    ( spl13_96
  <=> k11_relat_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f1972,plain,
    ( k11_relat_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f349,f87,f1862,f183])).

fof(f2014,plain,
    ( spl13_98
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1973,f1861,f85,f2011])).

fof(f1973,plain,
    ( k11_relat_1(sK0,sK1) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f1862,f87,f1862,f183])).

fof(f2009,plain,
    ( spl13_97
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1974,f1861,f85,f2006])).

fof(f1974,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1862,f275])).

fof(f2004,plain,
    ( ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(avatar_contradiction_clause,[],[f2003])).

fof(f2003,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_83
    | spl13_87 ),
    inference(subsumption_resolution,[],[f1975,f1898])).

fof(f1975,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f1862,f418])).

fof(f418,plain,
    ( ! [X3] :
        ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = X3
        | ~ v1_xboole_0(X3) )
    | ~ spl13_15 ),
    inference(resolution,[],[f375,f158])).

fof(f2002,plain,
    ( spl13_96
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1976,f1861,f348,f85,f1999])).

fof(f1976,plain,
    ( k11_relat_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1862,f505])).

fof(f505,plain,
    ( ! [X6,X7] :
        ( k9_relat_1(X6,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) = X7
        | ~ v1_relat_1(X6)
        | ~ v1_xboole_0(X7) )
    | ~ spl13_15 ),
    inference(resolution,[],[f415,f158])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(X0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
        | ~ v1_relat_1(X0) )
    | ~ spl13_15 ),
    inference(resolution,[],[f375,f64])).

fof(f1997,plain,
    ( ~ spl13_95
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1978,f1861,f534,f348,f85,f1994])).

fof(f534,plain,
    ( spl13_32
  <=> v1_relat_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f1978,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1862,f541])).

fof(f541,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k9_relat_1(X0,X1))
        | ~ v1_xboole_0(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f538,f181])).

fof(f538,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f536,f418])).

fof(f536,plain,
    ( ~ v1_relat_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_32 ),
    inference(avatar_component_clause,[],[f534])).

fof(f1992,plain,
    ( ~ spl13_94
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1979,f1861,f534,f348,f85,f1989])).

fof(f1979,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1862,f542])).

fof(f542,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(k9_relat_1(X2,k9_relat_1(X3,X4)))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ v1_xboole_0(X4) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f538,f275])).

fof(f1987,plain,
    ( spl13_93
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(avatar_split_clause,[],[f1980,f1861,f348,f85,f1984])).

fof(f1980,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f375,f1862,f992])).

fof(f1948,plain,
    ( spl13_92
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1914,f1861,f534,f348,f85,f1945])).

fof(f1914,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1863,f1522])).

fof(f1522,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK9(k11_relat_1(X0,X1)),a_2_0_mcart_1(X0,X1))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(k11_relat_1(X0,X1)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1521,f538])).

fof(f1521,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k11_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(sK9(k11_relat_1(X0,X1)),a_2_0_mcart_1(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1515])).

fof(f1515,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k11_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK9(k11_relat_1(X0,X1)),a_2_0_mcart_1(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f1503,f303])).

fof(f1503,plain,(
    ! [X4,X3] :
      ( m1_subset_1(k4_tarski(X4,sK9(k11_relat_1(X3,X4))),X3)
      | v1_xboole_0(k11_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f1367,f50])).

fof(f1943,plain,
    ( spl13_91
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1915,f1861,f534,f348,f85,f1940])).

fof(f1915,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1863,f1520])).

fof(f1520,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK9(k11_relat_1(X2,X3)),a_2_0_mcart_1(X2,X3))
        | ~ v1_relat_1(X2)
        | v1_xboole_0(k11_relat_1(X2,X3)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(duplicate_literal_removal,[],[f1516])).

fof(f1516,plain,
    ( ! [X2,X3] :
        ( v1_xboole_0(k11_relat_1(X2,X3))
        | ~ v1_relat_1(X2)
        | m1_subset_1(sK9(k11_relat_1(X2,X3)),a_2_0_mcart_1(X2,X3))
        | ~ v1_relat_1(X2) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f1503,f1034])).

fof(f1034,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k4_tarski(X0,X1),X2)
        | m1_subset_1(X1,a_2_0_mcart_1(X2,X0))
        | ~ v1_relat_1(X2) )
    | ~ spl13_15
    | spl13_32 ),
    inference(forward_demodulation,[],[f1033,f208])).

fof(f1033,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X1,a_2_0_mcart_1(X2,k1_mcart_1(k4_tarski(X0,X1))))
        | ~ m1_subset_1(k4_tarski(X0,X1),X2)
        | ~ v1_relat_1(X2) )
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1026,f538])).

fof(f1026,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X1,a_2_0_mcart_1(X2,k1_mcart_1(k4_tarski(X0,X1))))
      | ~ m1_subset_1(k4_tarski(X0,X1),X2)
      | v1_xboole_0(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f294,f234])).

fof(f1938,plain,
    ( spl13_90
    | ~ spl13_2
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1917,f1861,f85,f1935])).

fof(f1917,plain,
    ( m1_subset_1(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1863,f1503])).

fof(f1933,plain,
    ( spl13_89
    | ~ spl13_2
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1918,f1861,f85,f1930])).

fof(f1918,plain,
    ( r2_hidden(k4_tarski(sK1,sK9(k11_relat_1(sK0,sK1))),sK0)
    | ~ spl13_2
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f87,f1863,f1367])).

fof(f1928,plain,
    ( spl13_88
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1919,f1861,f1924])).

fof(f1919,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f48,f1863,f51])).

fof(f1927,plain,
    ( spl13_88
    | spl13_83 ),
    inference(avatar_split_clause,[],[f1920,f1861,f1924])).

fof(f1920,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_83 ),
    inference(unit_resulting_resolution,[],[f1863,f116])).

fof(f1911,plain,
    ( ~ spl13_77
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1803,f1679,f534,f348,f1828])).

fof(f1828,plain,
    ( spl13_77
  <=> v1_relat_1(a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f1803,plain,
    ( ~ v1_relat_1(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(resolution,[],[f1680,f538])).

fof(f1910,plain,
    ( spl13_83
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1909,f1679,f534,f348,f85,f1861])).

fof(f1909,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1802,f87])).

fof(f1802,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(resolution,[],[f1680,f1523])).

fof(f1523,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(a_2_0_mcart_1(X4,X5))
        | ~ v1_relat_1(X4)
        | v1_xboole_0(k11_relat_1(X4,X5)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1519,f538])).

fof(f1519,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k11_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_xboole_0(a_2_0_mcart_1(X4,X5))
      | v1_xboole_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f1517])).

fof(f1517,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k11_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_xboole_0(a_2_0_mcart_1(X4,X5))
      | v1_xboole_0(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f1503,f336])).

fof(f1908,plain,
    ( ~ spl13_86
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1907,f1679,f534,f348,f85,f1880])).

fof(f1907,plain,
    ( ~ v1_relat_1(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1801,f87])).

fof(f1801,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k11_relat_1(sK0,sK1))
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(resolution,[],[f1680,f1619])).

fof(f1619,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(a_2_0_mcart_1(X0,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k11_relat_1(X0,X1)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(duplicate_literal_removal,[],[f1615])).

fof(f1615,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k11_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f1595,f35])).

fof(f1595,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k9_relat_1(X0,k1_tarski(X1)))
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(X0,X1)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f1585,f538])).

fof(f1585,plain,
    ( ! [X19,X20] :
        ( v1_xboole_0(k9_relat_1(X19,k1_tarski(X20)))
        | ~ v1_xboole_0(a_2_0_mcart_1(X19,X20))
        | ~ v1_relat_1(X19) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f1579,f116])).

fof(f1579,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(X0,X1)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(duplicate_literal_removal,[],[f1578])).

fof(f1578,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(a_2_0_mcart_1(X0,X1))
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
        | ~ r2_hidden(X2,k9_relat_1(X0,k1_tarski(X1)))
        | ~ v1_relat_1(X0) )
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f1546,f179])).

fof(f1546,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_xboole_0(a_2_0_mcart_1(X7,sK3(X7,X8,X6)))
        | ~ v1_relat_1(X7)
        | ~ r2_hidden(X6,k9_relat_1(X7,X8)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1542,f538])).

fof(f1542,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k9_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_xboole_0(a_2_0_mcart_1(X7,sK3(X7,X8,X6)))
      | v1_xboole_0(X7) ) ),
    inference(duplicate_literal_removal,[],[f1538])).

fof(f1538,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k9_relat_1(X7,X8))
      | ~ v1_relat_1(X7)
      | ~ v1_xboole_0(a_2_0_mcart_1(X7,sK3(X7,X8,X6)))
      | v1_xboole_0(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f522,f336])).

fof(f1906,plain,
    ( spl13_83
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1760,f1679,f534,f348,f85,f1861])).

fof(f1760,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f1523])).

fof(f1904,plain,
    ( spl13_83
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1903,f1679,f534,f348,f85,f1861])).

fof(f1903,plain,
    ( v1_xboole_0(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1762,f150])).

fof(f1762,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f1585])).

fof(f1902,plain,
    ( ~ spl13_86
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1901,f1679,f534,f348,f85,f1880])).

fof(f1901,plain,
    ( ~ v1_relat_1(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1764,f150])).

fof(f1764,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f1595])).

fof(f1900,plain,
    ( spl13_87
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1765,f1679,f534,f348,f85,f1897])).

fof(f1765,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f349,f87,f1680,f1612])).

fof(f1612,plain,
    ( ! [X26,X24,X25] :
        ( k11_relat_1(X24,X25) = X26
        | ~ v1_xboole_0(a_2_0_mcart_1(X24,X25))
        | ~ v1_relat_1(X24)
        | ~ v1_xboole_0(X26) )
    | ~ spl13_15
    | spl13_32 ),
    inference(resolution,[],[f1594,f158])).

fof(f1594,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(X0,X1)) )
    | ~ spl13_15
    | spl13_32 ),
    inference(duplicate_literal_removal,[],[f1590])).

fof(f1590,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k11_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | ~ v1_xboole_0(a_2_0_mcart_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f1579,f35])).

fof(f1895,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1894])).

fof(f1894,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1766,f82])).

fof(f1766,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(sK0,sK1)
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f87,f1680,f1612])).

fof(f1893,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1892])).

fof(f1892,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1767,f1680])).

fof(f1767,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f82,f1680,f1612])).

fof(f1891,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1890])).

fof(f1890,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1768,f87])).

fof(f1768,plain,
    ( ~ v1_relat_1(sK0)
    | spl13_1
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f82,f1680,f1612])).

fof(f1889,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1888])).

fof(f1888,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1887,f1680])).

fof(f1887,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1770,f780])).

fof(f1770,plain,
    ( ! [X0] : ~ v1_xboole_0(sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f214,f1680,f1612])).

fof(f1886,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1885])).

fof(f1885,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1884,f1680])).

fof(f1884,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(forward_demodulation,[],[f1771,f945])).

fof(f1771,plain,
    ( ! [X0] : ~ v1_xboole_0(sK8(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f242,f1680,f1612])).

fof(f1883,plain,
    ( ~ spl13_86
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1772,f1679,f534,f348,f85,f1880])).

fof(f1772,plain,
    ( ~ v1_relat_1(k11_relat_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f1619])).

fof(f1878,plain,
    ( spl13_85
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1774,f1679,f80,f1875])).

fof(f1774,plain,
    ( r2_hidden(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1680,f158])).

fof(f1873,plain,
    ( spl13_79
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1775,f1679,f348,f1838])).

fof(f1775,plain,
    ( a_2_0_mcart_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f375,f1680,f158])).

fof(f1872,plain,
    ( spl13_84
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1776,f1679,f80,f1869])).

fof(f1776,plain,
    ( m1_subset_1(sK10(k11_relat_1(sK0,sK1),a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1680,f161])).

fof(f1867,plain,
    ( spl13_79
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1777,f1679,f348,f1838])).

fof(f1777,plain,
    ( a_2_0_mcart_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f349,f1680,f162])).

fof(f1866,plain,
    ( ~ spl13_83
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1779,f1679,f80,f1861])).

fof(f1779,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1680,f162])).

fof(f1865,plain,
    ( spl13_79
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1780,f1679,f348,f1838])).

fof(f1780,plain,
    ( a_2_0_mcart_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f349,f1680,f162])).

fof(f1864,plain,
    ( ~ spl13_83
    | spl13_1
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1782,f1679,f80,f1861])).

fof(f1782,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1))
    | spl13_1
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f82,f1680,f162])).

fof(f1859,plain,
    ( spl13_82
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1785,f1679,f85,f1856])).

fof(f1785,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f181])).

fof(f1854,plain,
    ( spl13_74
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1786,f1679,f348,f85,f1813])).

fof(f1813,plain,
    ( spl13_74
  <=> a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f1786,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f349,f87,f1680,f183])).

fof(f1853,plain,
    ( spl13_81
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1787,f1679,f85,f1848])).

fof(f1787,plain,
    ( a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f87,f1680,f183])).

fof(f1852,plain,
    ( spl13_78
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1788,f1679,f348,f85,f1833])).

fof(f1833,plain,
    ( spl13_78
  <=> a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f1788,plain,
    ( a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f349,f87,f1680,f183])).

fof(f1851,plain,
    ( spl13_81
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1789,f1679,f85,f1848])).

fof(f1789,plain,
    ( a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f87,f1680,f183])).

fof(f1846,plain,
    ( spl13_80
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1790,f1679,f85,f1843])).

fof(f1790,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1680,f275])).

fof(f1841,plain,
    ( spl13_79
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1791,f1679,f348,f1838])).

fof(f1791,plain,
    ( a_2_0_mcart_1(sK0,sK1) = a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f418])).

fof(f1836,plain,
    ( spl13_78
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1792,f1679,f348,f85,f1833])).

fof(f1792,plain,
    ( a_2_0_mcart_1(sK0,sK1) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f505])).

fof(f1831,plain,
    ( ~ spl13_77
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1793,f1679,f534,f348,f1828])).

fof(f1793,plain,
    ( ~ v1_relat_1(a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f538])).

fof(f1826,plain,
    ( ~ spl13_76
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1794,f1679,f534,f348,f85,f1823])).

fof(f1794,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1)))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f541])).

fof(f1821,plain,
    ( ~ spl13_75
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1795,f1679,f534,f348,f85,f1818])).

fof(f1795,plain,
    ( ~ v1_relat_1(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f87,f1680,f542])).

fof(f1816,plain,
    ( spl13_74
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(avatar_split_clause,[],[f1796,f1679,f348,f85,f1813])).

fof(f1796,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(sK0,sK1))
    | ~ spl13_2
    | ~ spl13_15
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f375,f1680,f992])).

fof(f1811,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1810])).

fof(f1810,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1797,f82])).

fof(f1797,plain,
    ( k11_relat_1(sK0,sK1) = a_2_0_mcart_1(sK0,sK1)
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f1680,f1612])).

fof(f1809,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1808])).

fof(f1808,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1798,f1680])).

fof(f1798,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f82,f1680,f1612])).

fof(f1807,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1806])).

fof(f1806,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(subsumption_resolution,[],[f1799,f87])).

fof(f1799,plain,
    ( ~ v1_relat_1(sK0)
    | spl13_1
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f1680,f82,f1680,f1612])).

fof(f1805,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1800])).

fof(f1800,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f82,f1680,f1612])).

fof(f1804,plain,
    ( spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(avatar_contradiction_clause,[],[f1769])).

fof(f1769,plain,
    ( $false
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_58 ),
    inference(unit_resulting_resolution,[],[f87,f1680,f82,f1680,f1612])).

fof(f1758,plain,
    ( spl13_73
    | spl13_58 ),
    inference(avatar_split_clause,[],[f1751,f1679,f1754])).

fof(f1751,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58 ),
    inference(unit_resulting_resolution,[],[f48,f1681,f51])).

fof(f1757,plain,
    ( spl13_73
    | spl13_58 ),
    inference(avatar_split_clause,[],[f1752,f1679,f1754])).

fof(f1752,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_58 ),
    inference(unit_resulting_resolution,[],[f1681,f116])).

fof(f1750,plain,
    ( ~ spl13_58
    | spl13_72
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1746,f534,f348,f85,f80,f1748,f1679])).

fof(f1748,plain,
    ( spl13_72
  <=> ! [X22,X23] :
        ( sK8(k4_tarski(X23,X22),a_2_0_mcart_1(sK0,sK1)) = X22
        | ~ v1_xboole_0(X22) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f1746,plain,
    ( ! [X23,X22] :
        ( sK8(k4_tarski(X23,X22),a_2_0_mcart_1(sK0,sK1)) = X22
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X22) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1652,f87])).

fof(f1652,plain,
    ( ! [X23,X22] :
        ( sK8(k4_tarski(X23,X22),a_2_0_mcart_1(sK0,sK1)) = X22
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X22) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f962,f1612])).

fof(f962,plain,
    ( ! [X0] : k11_relat_1(sK0,sK1) = sK8(k4_tarski(X0,k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1))
    | spl13_1 ),
    inference(forward_demodulation,[],[f922,f945])).

fof(f922,plain,
    ( ! [X0,X1] : k11_relat_1(sK0,sK1) = sK8(k4_tarski(X0,k11_relat_1(sK0,sK1)),sK8(k4_tarski(X1,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f242,f896])).

fof(f1745,plain,
    ( ~ spl13_58
    | spl13_71
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1741,f534,f348,f85,f80,f1743,f1679])).

fof(f1743,plain,
    ( spl13_71
  <=> ! [X20,X21] :
        ( a_2_0_mcart_1(sK0,sK1) = sK8(k4_tarski(X21,a_2_0_mcart_1(sK0,sK1)),X20)
        | ~ v1_xboole_0(X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f1741,plain,
    ( ! [X21,X20] :
        ( a_2_0_mcart_1(sK0,sK1) = sK8(k4_tarski(X21,a_2_0_mcart_1(sK0,sK1)),X20)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X20) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1651,f87])).

fof(f1651,plain,
    ( ! [X21,X20] :
        ( a_2_0_mcart_1(sK0,sK1) = sK8(k4_tarski(X21,a_2_0_mcart_1(sK0,sK1)),X20)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X20) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f945,f1612])).

fof(f1740,plain,
    ( ~ spl13_58
    | spl13_70
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1736,f534,f348,f85,f80,f1738,f1679])).

fof(f1738,plain,
    ( spl13_70
  <=> ! [X18,X19] :
        ( sK7(k4_tarski(X19,X18),a_2_0_mcart_1(sK0,sK1)) = X19
        | ~ v1_xboole_0(X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f1736,plain,
    ( ! [X19,X18] :
        ( sK7(k4_tarski(X19,X18),a_2_0_mcart_1(sK0,sK1)) = X19
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X18) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1650,f87])).

fof(f1650,plain,
    ( ! [X19,X18] :
        ( sK7(k4_tarski(X19,X18),a_2_0_mcart_1(sK0,sK1)) = X19
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X18) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f918,f1612])).

fof(f918,plain,
    ( ! [X0] : sK7(k4_tarski(X0,k11_relat_1(sK0,sK1)),a_2_0_mcart_1(sK0,sK1)) = X0
    | spl13_1 ),
    inference(forward_demodulation,[],[f899,f780])).

fof(f899,plain,
    ( ! [X0,X1] : sK7(k4_tarski(X0,k11_relat_1(sK0,sK1)),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X1),k11_relat_1(sK0,sK1))) = X0
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f894])).

fof(f894,plain,(
    ! [X30,X28,X29] :
      ( sK7(k4_tarski(X28,X29),X30) = X28
      | X29 = X30 ) ),
    inference(forward_demodulation,[],[f881,f208])).

fof(f881,plain,(
    ! [X30,X28,X29] :
      ( k1_mcart_1(k4_tarski(X28,X29)) = sK7(k4_tarski(X28,X29),X30)
      | X29 = X30 ) ),
    inference(superposition,[],[f208,f236])).

fof(f1735,plain,
    ( ~ spl13_58
    | spl13_69
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1731,f534,f348,f85,f80,f1733,f1679])).

fof(f1733,plain,
    ( spl13_69
  <=> ! [X16,X17] :
        ( sK7(k4_tarski(X17,a_2_0_mcart_1(sK0,sK1)),X16) = X17
        | ~ v1_xboole_0(X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_69])])).

fof(f1731,plain,
    ( ! [X17,X16] :
        ( sK7(k4_tarski(X17,a_2_0_mcart_1(sK0,sK1)),X16) = X17
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X16) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1649,f87])).

fof(f1649,plain,
    ( ! [X17,X16] :
        ( sK7(k4_tarski(X17,a_2_0_mcart_1(sK0,sK1)),X16) = X17
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X16) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f914,f1612])).

fof(f914,plain,
    ( ! [X0] : sK7(k4_tarski(X0,a_2_0_mcart_1(sK0,sK1)),k11_relat_1(sK0,sK1)) = X0
    | spl13_1 ),
    inference(forward_demodulation,[],[f903,f780])).

fof(f903,plain,
    ( ! [X0,X1] : sK7(k4_tarski(X0,sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X1),k11_relat_1(sK0,sK1))),k11_relat_1(sK0,sK1)) = X0
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f894])).

fof(f1730,plain,
    ( ~ spl13_58
    | spl13_68
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1726,f534,f348,f85,f80,f1728,f1679])).

fof(f1728,plain,
    ( spl13_68
  <=> ! [X15,X14] :
        ( sK6(k4_tarski(X14,X15),a_2_0_mcart_1(sK0,sK1)) = X15
        | ~ v1_xboole_0(X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f1726,plain,
    ( ! [X14,X15] :
        ( sK6(k4_tarski(X14,X15),a_2_0_mcart_1(sK0,sK1)) = X15
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X14) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1648,f87])).

fof(f1648,plain,
    ( ! [X14,X15] :
        ( sK6(k4_tarski(X14,X15),a_2_0_mcart_1(sK0,sK1)) = X15
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X14) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f853,f1612])).

fof(f853,plain,
    ( ! [X0] : sK6(k4_tarski(k11_relat_1(sK0,sK1),X0),a_2_0_mcart_1(sK0,sK1)) = X0
    | spl13_1 ),
    inference(forward_demodulation,[],[f840,f780])).

fof(f840,plain,
    ( ! [X0,X1] : sK6(k4_tarski(k11_relat_1(sK0,sK1),X0),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X1),k11_relat_1(sK0,sK1))) = X0
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f773])).

fof(f773,plain,(
    ! [X39,X38,X40] :
      ( sK6(k4_tarski(X38,X39),X40) = X39
      | X38 = X40 ) ),
    inference(forward_demodulation,[],[f766,f234])).

fof(f766,plain,(
    ! [X39,X38,X40] :
      ( sK6(k4_tarski(X38,X39),X40) = k2_mcart_1(k4_tarski(X38,X39))
      | X38 = X40 ) ),
    inference(superposition,[],[f234,f210])).

fof(f1725,plain,
    ( ~ spl13_58
    | spl13_67
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1721,f534,f348,f85,f80,f1723,f1679])).

fof(f1723,plain,
    ( spl13_67
  <=> ! [X13,X12] :
        ( sK6(k4_tarski(a_2_0_mcart_1(sK0,sK1),X13),X12) = X13
        | ~ v1_xboole_0(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).

fof(f1721,plain,
    ( ! [X12,X13] :
        ( sK6(k4_tarski(a_2_0_mcart_1(sK0,sK1),X13),X12) = X13
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X12) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1647,f87])).

fof(f1647,plain,
    ( ! [X12,X13] :
        ( sK6(k4_tarski(a_2_0_mcart_1(sK0,sK1),X13),X12) = X13
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X12) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f852,f1612])).

fof(f852,plain,
    ( ! [X1] : sK6(k4_tarski(a_2_0_mcart_1(sK0,sK1),X1),k11_relat_1(sK0,sK1)) = X1
    | spl13_1 ),
    inference(forward_demodulation,[],[f844,f780])).

fof(f844,plain,
    ( ! [X0,X1] : sK6(k4_tarski(sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X0),k11_relat_1(sK0,sK1)),X1),k11_relat_1(sK0,sK1)) = X1
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f773])).

fof(f1720,plain,
    ( ~ spl13_58
    | spl13_66
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1716,f534,f348,f85,f80,f1718,f1679])).

fof(f1718,plain,
    ( spl13_66
  <=> ! [X11,X10] :
        ( sK5(k4_tarski(X10,X11),a_2_0_mcart_1(sK0,sK1)) = X10
        | ~ v1_xboole_0(X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f1716,plain,
    ( ! [X10,X11] :
        ( sK5(k4_tarski(X10,X11),a_2_0_mcart_1(sK0,sK1)) = X10
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X10) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1646,f87])).

fof(f1646,plain,
    ( ! [X10,X11] :
        ( sK5(k4_tarski(X10,X11),a_2_0_mcart_1(sK0,sK1)) = X10
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X10) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f824,f1612])).

fof(f824,plain,
    ( ! [X0] : k11_relat_1(sK0,sK1) = sK5(k4_tarski(k11_relat_1(sK0,sK1),X0),a_2_0_mcart_1(sK0,sK1))
    | spl13_1 ),
    inference(forward_demodulation,[],[f776,f780])).

fof(f776,plain,
    ( ! [X0,X1] : k11_relat_1(sK0,sK1) = sK5(k4_tarski(k11_relat_1(sK0,sK1),X0),sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X1),k11_relat_1(sK0,sK1)))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f214,f771])).

fof(f1715,plain,
    ( ~ spl13_58
    | spl13_65
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1711,f534,f348,f85,f80,f1713,f1679])).

fof(f1713,plain,
    ( spl13_65
  <=> ! [X9,X8] :
        ( a_2_0_mcart_1(sK0,sK1) = sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X9),X8)
        | ~ v1_xboole_0(X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f1711,plain,
    ( ! [X8,X9] :
        ( a_2_0_mcart_1(sK0,sK1) = sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X9),X8)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X8) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1645,f87])).

fof(f1645,plain,
    ( ! [X8,X9] :
        ( a_2_0_mcart_1(sK0,sK1) = sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X9),X8)
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X8) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f780,f1612])).

fof(f1710,plain,
    ( ~ spl13_58
    | spl13_64
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1706,f534,f348,f85,f80,f1708,f1679])).

fof(f1708,plain,
    ( spl13_64
  <=> ! [X7,X6] :
        ( sK8(k4_tarski(X7,a_2_0_mcart_1(sK0,sK1)),X6) != X6
        | ~ v1_xboole_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f1706,plain,
    ( ! [X6,X7] :
        ( sK8(k4_tarski(X7,a_2_0_mcart_1(sK0,sK1)),X6) != X6
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X6) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1644,f87])).

fof(f1644,plain,
    ( ! [X6,X7] :
        ( sK8(k4_tarski(X7,a_2_0_mcart_1(sK0,sK1)),X6) != X6
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X6) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f242,f1612])).

fof(f1705,plain,
    ( ~ spl13_58
    | spl13_63
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1701,f534,f348,f85,f80,f1703,f1679])).

fof(f1703,plain,
    ( spl13_63
  <=> ! [X5,X4] :
        ( sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X5),X4) != X4
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f1701,plain,
    ( ! [X4,X5] :
        ( sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X5),X4) != X4
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X4) )
    | spl13_1
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1643,f87])).

fof(f1643,plain,
    ( ! [X4,X5] :
        ( sK5(k4_tarski(a_2_0_mcart_1(sK0,sK1),X5),X4) != X4
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X4) )
    | spl13_1
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f214,f1612])).

fof(f1700,plain,
    ( ~ spl13_58
    | spl13_62
    | ~ spl13_2
    | spl13_8
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1696,f534,f348,f144,f85,f1698,f1679])).

fof(f1698,plain,
    ( spl13_62
  <=> ! [X3] :
        ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(X3))
        | ~ v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_62])])).

fof(f144,plain,
    ( spl13_8
  <=> m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f1696,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(X3))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X3) )
    | ~ spl13_2
    | spl13_8
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1642,f87])).

fof(f1642,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(X3))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X3) )
    | spl13_8
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f146,f1612])).

fof(f146,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1695,plain,
    ( ~ spl13_58
    | spl13_61
    | ~ spl13_2
    | spl13_7
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1691,f534,f348,f138,f85,f1693,f1679])).

fof(f1693,plain,
    ( spl13_61
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_61])])).

fof(f138,plain,
    ( spl13_7
  <=> m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f1691,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X2) )
    | ~ spl13_2
    | spl13_7
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1641,f87])).

fof(f1641,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X2) )
    | spl13_7
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f140,f1612])).

fof(f140,plain,
    ( ~ m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1690,plain,
    ( ~ spl13_58
    | spl13_60
    | ~ spl13_2
    | spl13_5
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1686,f534,f348,f109,f85,f1688,f1679])).

fof(f1688,plain,
    ( spl13_60
  <=> ! [X1] :
        ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(X1))
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f109,plain,
    ( spl13_5
  <=> r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f1686,plain,
    ( ! [X1] :
        ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(X1))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X1) )
    | ~ spl13_2
    | spl13_5
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1640,f87])).

fof(f1640,plain,
    ( ! [X1] :
        ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(X1))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X1) )
    | spl13_5
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f111,f1612])).

fof(f111,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1685,plain,
    ( ~ spl13_58
    | spl13_59
    | ~ spl13_2
    | spl13_4
    | ~ spl13_15
    | spl13_32 ),
    inference(avatar_split_clause,[],[f1677,f534,f348,f104,f85,f1683,f1679])).

fof(f1683,plain,
    ( spl13_59
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_59])])).

fof(f104,plain,
    ( spl13_4
  <=> r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1677,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_xboole_0(X0) )
    | ~ spl13_2
    | spl13_4
    | ~ spl13_15
    | spl13_32 ),
    inference(subsumption_resolution,[],[f1639,f87])).

fof(f1639,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(a_2_0_mcart_1(sK0,sK1)))
        | ~ v1_xboole_0(a_2_0_mcart_1(sK0,sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_xboole_0(X0) )
    | spl13_4
    | ~ spl13_15
    | spl13_32 ),
    inference(superposition,[],[f106,f1612])).

fof(f106,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1496,plain,
    ( spl13_57
    | ~ spl13_2
    | ~ spl13_54
    | ~ spl13_55
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f1491,f1464,f1445,f1440,f85,f1493])).

fof(f1493,plain,
    ( spl13_57
  <=> k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))) = sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).

fof(f1440,plain,
    ( spl13_54
  <=> sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_54])])).

fof(f1445,plain,
    ( spl13_55
  <=> k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f1464,plain,
    ( spl13_56
  <=> r2_hidden(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f1491,plain,
    ( k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))) = sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))
    | ~ spl13_2
    | ~ spl13_54
    | ~ spl13_55
    | ~ spl13_56 ),
    inference(forward_demodulation,[],[f1490,f1447])).

fof(f1447,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_55 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1490,plain,
    ( sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_54
    | ~ spl13_56 ),
    inference(forward_demodulation,[],[f1485,f1442])).

fof(f1442,plain,
    ( sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_54 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f1485,plain,
    ( sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_56 ),
    inference(unit_resulting_resolution,[],[f87,f1466,f49])).

fof(f1466,plain,
    ( r2_hidden(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f1467,plain,
    ( spl13_56
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(avatar_split_clause,[],[f1451,f1408,f90,f85,f1464])).

fof(f1408,plain,
    ( spl13_51
  <=> r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_51])])).

fof(f1451,plain,
    ( r2_hidden(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1410,f355])).

fof(f1410,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_51 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1448,plain,
    ( spl13_55
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(avatar_split_clause,[],[f1427,f1408,f90,f85,f1445])).

fof(f1427,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1410,f61])).

fof(f1443,plain,
    ( spl13_54
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(avatar_split_clause,[],[f1428,f1408,f90,f85,f1440])).

fof(f1428,plain,
    ( sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1410,f60])).

fof(f1438,plain,
    ( spl13_53
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(avatar_split_clause,[],[f1429,f1408,f90,f85,f1435])).

fof(f1435,plain,
    ( spl13_53
  <=> m1_subset_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_53])])).

fof(f1429,plain,
    ( m1_subset_1(sK12(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_51 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1410,f59])).

fof(f1426,plain,
    ( spl13_52
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1425,f1386,f534,f348,f85,f1416])).

fof(f1416,plain,
    ( spl13_52
  <=> m1_subset_1(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f1386,plain,
    ( spl13_50
  <=> m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f1425,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f1402,f87])).

fof(f1402,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ v1_relat_1(sK0)
    | ~ spl13_15
    | spl13_32
    | ~ spl13_50 ),
    inference(resolution,[],[f1388,f1034])).

fof(f1388,plain,
    ( m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f1424,plain,
    ( spl13_51
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1423,f1386,f90,f85,f1408])).

fof(f1423,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f1422,f92])).

fof(f1422,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl13_2
    | ~ spl13_50 ),
    inference(subsumption_resolution,[],[f1401,f87])).

fof(f1401,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl13_50 ),
    inference(resolution,[],[f1388,f303])).

fof(f1421,plain,
    ( spl13_51
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1394,f1386,f90,f85,f1408])).

fof(f1394,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f92,f87,f1388,f303])).

fof(f1420,plain,
    ( spl13_52
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1395,f1386,f534,f348,f85,f1416])).

fof(f1395,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15
    | spl13_32
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f87,f1388,f1034])).

fof(f1419,plain,
    ( spl13_52
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1414,f1386,f90,f85,f1416])).

fof(f1414,plain,
    ( m1_subset_1(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f1413,f234])).

fof(f1413,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f1397,f208])).

fof(f1397,plain,
    ( m1_subset_1(k2_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f87,f92,f1388,f294])).

fof(f1411,plain,
    ( spl13_51
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1406,f1386,f90,f85,f1408])).

fof(f1406,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f1405,f234])).

fof(f1405,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(forward_demodulation,[],[f1399,f208])).

fof(f1399,plain,
    ( r2_hidden(k2_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_50 ),
    inference(unit_resulting_resolution,[],[f92,f87,f1388,f78])).

fof(f1393,plain,
    ( spl13_50
    | ~ spl13_49 ),
    inference(avatar_split_clause,[],[f1383,f1372,f1386])).

fof(f1383,plain,
    ( m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_49 ),
    inference(resolution,[],[f1374,f50])).

fof(f1389,plain,
    ( spl13_50
    | ~ spl13_49 ),
    inference(avatar_split_clause,[],[f1380,f1372,f1386])).

fof(f1380,plain,
    ( m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_49 ),
    inference(unit_resulting_resolution,[],[f1374,f50])).

fof(f1377,plain,
    ( spl13_49
    | ~ spl13_2
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f1376,f732,f85,f1372])).

fof(f732,plain,
    ( spl13_48
  <=> r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f1376,plain,
    ( r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_2
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f1366,f87])).

fof(f1366,plain,
    ( ~ v1_relat_1(sK0)
    | r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_48 ),
    inference(resolution,[],[f1358,f734])).

fof(f734,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f732])).

fof(f1375,plain,
    ( spl13_49
    | ~ spl13_2
    | ~ spl13_48 ),
    inference(avatar_split_clause,[],[f1360,f732,f85,f1372])).

fof(f1360,plain,
    ( r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_2
    | ~ spl13_48 ),
    inference(unit_resulting_resolution,[],[f87,f734,f1358])).

fof(f736,plain,
    ( spl13_48
    | spl13_46 ),
    inference(avatar_split_clause,[],[f729,f718,f732])).

fof(f729,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_46 ),
    inference(unit_resulting_resolution,[],[f48,f720,f51])).

fof(f735,plain,
    ( spl13_48
    | spl13_46 ),
    inference(avatar_split_clause,[],[f730,f718,f732])).

fof(f730,plain,
    ( r2_hidden(sK9(k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_46 ),
    inference(unit_resulting_resolution,[],[f720,f116])).

fof(f728,plain,
    ( ~ spl13_46
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f716,f708,f718])).

fof(f708,plain,
    ( spl13_45
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f716,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_45 ),
    inference(resolution,[],[f710,f58])).

fof(f710,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_45 ),
    inference(avatar_component_clause,[],[f708])).

fof(f727,plain,
    ( spl13_47
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f715,f708,f723])).

fof(f723,plain,
    ( spl13_47
  <=> m1_subset_1(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_47])])).

fof(f715,plain,
    ( m1_subset_1(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_45 ),
    inference(resolution,[],[f710,f50])).

fof(f726,plain,
    ( spl13_47
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f713,f708,f723])).

fof(f713,plain,
    ( m1_subset_1(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_45 ),
    inference(unit_resulting_resolution,[],[f710,f50])).

fof(f721,plain,
    ( ~ spl13_46
    | ~ spl13_45 ),
    inference(avatar_split_clause,[],[f714,f708,f718])).

fof(f714,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_45 ),
    inference(unit_resulting_resolution,[],[f710,f58])).

fof(f711,plain,
    ( spl13_45
    | ~ spl13_2
    | ~ spl13_43 ),
    inference(avatar_split_clause,[],[f706,f676,f85,f708])).

fof(f706,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k11_relat_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_43 ),
    inference(forward_demodulation,[],[f698,f150])).

fof(f698,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),k9_relat_1(sK0,k1_tarski(k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_43 ),
    inference(unit_resulting_resolution,[],[f87,f76,f678,f63])).

fof(f684,plain,
    ( spl13_44
    | ~ spl13_17
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f674,f667,f362,f681])).

fof(f681,plain,
    ( spl13_44
  <=> m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f362,plain,
    ( spl13_17
  <=> m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f667,plain,
    ( spl13_42
  <=> sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f674,plain,
    ( m1_subset_1(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_17
    | ~ spl13_42 ),
    inference(backward_demodulation,[],[f364,f669])).

fof(f669,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f667])).

fof(f364,plain,
    ( m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f362])).

fof(f679,plain,
    ( spl13_43
    | ~ spl13_27
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f673,f667,f472,f676])).

fof(f472,plain,
    ( spl13_27
  <=> r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f673,plain,
    ( r2_hidden(k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))),sK0)
    | ~ spl13_27
    | ~ spl13_42 ),
    inference(backward_demodulation,[],[f474,f669])).

fof(f474,plain,
    ( r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f472])).

fof(f670,plain,
    ( spl13_42
    | ~ spl13_37
    | ~ spl13_39 ),
    inference(avatar_split_clause,[],[f663,f638,f612,f667])).

fof(f612,plain,
    ( spl13_37
  <=> sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).

fof(f638,plain,
    ( spl13_39
  <=> k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f663,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK9(sK0)),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_37
    | ~ spl13_39 ),
    inference(backward_demodulation,[],[f614,f640])).

fof(f640,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_39 ),
    inference(avatar_component_clause,[],[f638])).

fof(f614,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_37 ),
    inference(avatar_component_clause,[],[f612])).

fof(f662,plain,
    ( spl13_41
    | ~ spl13_9
    | ~ spl13_35
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f657,f643,f600,f153,f659])).

fof(f659,plain,
    ( spl13_41
  <=> sK9(sK0) = sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f153,plain,
    ( spl13_9
  <=> sK9(sK0) = k4_tarski(k1_mcart_1(sK9(sK0)),k2_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f600,plain,
    ( spl13_35
  <=> sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f643,plain,
    ( spl13_40
  <=> k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f657,plain,
    ( sK9(sK0) = sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))
    | ~ spl13_9
    | ~ spl13_35
    | ~ spl13_40 ),
    inference(forward_demodulation,[],[f653,f155])).

fof(f155,plain,
    ( sK9(sK0) = k4_tarski(k1_mcart_1(sK9(sK0)),k2_mcart_1(sK9(sK0)))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f653,plain,
    ( k4_tarski(k1_mcart_1(sK9(sK0)),k2_mcart_1(sK9(sK0))) = sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))
    | ~ spl13_35
    | ~ spl13_40 ),
    inference(backward_demodulation,[],[f602,f645])).

fof(f645,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f643])).

fof(f602,plain,
    ( sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK9(sK0)))
    | ~ spl13_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f646,plain,
    ( spl13_40
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f631,f299,f90,f85,f643])).

fof(f299,plain,
    ( spl13_10
  <=> r2_hidden(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f631,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f87,f92,f301,f61])).

fof(f301,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f299])).

fof(f641,plain,
    ( spl13_39
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f632,f324,f90,f85,f638])).

fof(f324,plain,
    ( spl13_13
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f632,plain,
    ( k1_mcart_1(sK9(sK0)) = k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(unit_resulting_resolution,[],[f87,f92,f326,f61])).

fof(f326,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f324])).

fof(f620,plain,
    ( spl13_38
    | ~ spl13_28
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f610,f585,f477,f617])).

fof(f617,plain,
    ( spl13_38
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f477,plain,
    ( spl13_28
  <=> r2_hidden(k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f585,plain,
    ( spl13_33
  <=> sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f610,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_28
    | ~ spl13_33 ),
    inference(backward_demodulation,[],[f479,f587])).

fof(f587,plain,
    ( sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f585])).

fof(f479,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f477])).

fof(f615,plain,
    ( spl13_37
    | ~ spl13_30
    | ~ spl13_33 ),
    inference(avatar_split_clause,[],[f609,f585,f497,f612])).

fof(f497,plain,
    ( spl13_30
  <=> sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f609,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_30
    | ~ spl13_33 ),
    inference(backward_demodulation,[],[f499,f587])).

fof(f499,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f497])).

fof(f608,plain,
    ( spl13_36
    | ~ spl13_23
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f598,f590,f431,f605])).

fof(f605,plain,
    ( spl13_36
  <=> r2_hidden(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f431,plain,
    ( spl13_23
  <=> r2_hidden(k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f590,plain,
    ( spl13_34
  <=> k2_mcart_1(sK9(sK0)) = k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f598,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_23
    | ~ spl13_34 ),
    inference(backward_demodulation,[],[f433,f592])).

fof(f592,plain,
    ( k2_mcart_1(sK9(sK0)) = k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f590])).

fof(f433,plain,
    ( r2_hidden(k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f431])).

fof(f603,plain,
    ( spl13_35
    | ~ spl13_25
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f597,f590,f448,f600])).

fof(f448,plain,
    ( spl13_25
  <=> sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f597,plain,
    ( sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK9(sK0)))
    | ~ spl13_25
    | ~ spl13_34 ),
    inference(backward_demodulation,[],[f450,f592])).

fof(f450,plain,
    ( sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f448])).

fof(f593,plain,
    ( spl13_34
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f580,f299,f90,f85,f590])).

fof(f580,plain,
    ( k2_mcart_1(sK9(sK0)) = k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f87,f92,f301,f60])).

fof(f588,plain,
    ( spl13_33
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f581,f324,f90,f85,f585])).

fof(f581,plain,
    ( sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) = k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(unit_resulting_resolution,[],[f87,f92,f326,f60])).

fof(f537,plain,
    ( spl13_31
    | ~ spl13_32
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f528,f348,f534,f531])).

fof(f531,plain,
    ( spl13_31
  <=> ! [X25,X26] : ~ r2_hidden(X25,k9_relat_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),X26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).

fof(f528,plain,
    ( ! [X26,X25] :
        ( ~ v1_relat_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
        | ~ r2_hidden(X25,k9_relat_1(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))),X26)) )
    | ~ spl13_15 ),
    inference(resolution,[],[f65,f375])).

fof(f500,plain,
    ( spl13_30
    | ~ spl13_2
    | ~ spl13_27 ),
    inference(avatar_split_clause,[],[f491,f472,f85,f497])).

fof(f491,plain,
    ( sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_27 ),
    inference(unit_resulting_resolution,[],[f87,f474,f49])).

fof(f487,plain,
    ( spl13_27
    | spl13_3
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f486,f362,f90,f472])).

fof(f486,plain,
    ( r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | spl13_3
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f470,f92])).

fof(f470,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_17 ),
    inference(resolution,[],[f364,f51])).

fof(f485,plain,
    ( ~ spl13_29
    | ~ spl13_2
    | spl13_3
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f467,f362,f90,f85,f482])).

fof(f482,plain,
    ( spl13_29
  <=> v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f467,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_17 ),
    inference(unit_resulting_resolution,[],[f87,f92,f364,f295])).

fof(f480,plain,
    ( spl13_28
    | ~ spl13_2
    | spl13_3
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f468,f362,f90,f85,f477])).

fof(f468,plain,
    ( r2_hidden(k2_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_17 ),
    inference(unit_resulting_resolution,[],[f92,f87,f364,f78])).

fof(f475,plain,
    ( spl13_27
    | spl13_3
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f469,f362,f90,f472])).

fof(f469,plain,
    ( r2_hidden(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | spl13_3
    | ~ spl13_17 ),
    inference(unit_resulting_resolution,[],[f92,f364,f51])).

fof(f466,plain,
    ( spl13_26
    | spl13_24 ),
    inference(avatar_split_clause,[],[f459,f436,f462])).

fof(f462,plain,
    ( spl13_26
  <=> r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f436,plain,
    ( spl13_24
  <=> v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f459,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | spl13_24 ),
    inference(unit_resulting_resolution,[],[f438,f116])).

fof(f438,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | spl13_24 ),
    inference(avatar_component_clause,[],[f436])).

fof(f465,plain,
    ( spl13_26
    | spl13_24 ),
    inference(avatar_split_clause,[],[f460,f436,f462])).

fof(f460,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | spl13_24 ),
    inference(unit_resulting_resolution,[],[f48,f438,f51])).

fof(f451,plain,
    ( spl13_25
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f442,f426,f85,f448])).

fof(f426,plain,
    ( spl13_22
  <=> r2_hidden(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f442,plain,
    ( sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))) = k4_tarski(k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(unit_resulting_resolution,[],[f87,f428,f49])).

fof(f428,plain,
    ( r2_hidden(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f426])).

fof(f441,plain,
    ( spl13_22
    | spl13_3
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f440,f357,f90,f426])).

fof(f357,plain,
    ( spl13_16
  <=> m1_subset_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f440,plain,
    ( r2_hidden(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | spl13_3
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f424,f92])).

fof(f424,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_16 ),
    inference(resolution,[],[f359,f51])).

fof(f359,plain,
    ( m1_subset_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f357])).

fof(f439,plain,
    ( ~ spl13_24
    | ~ spl13_2
    | spl13_3
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f421,f357,f90,f85,f436])).

fof(f421,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f87,f92,f359,f295])).

fof(f434,plain,
    ( spl13_23
    | ~ spl13_2
    | spl13_3
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f422,f357,f90,f85,f431])).

fof(f422,plain,
    ( r2_hidden(k2_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))))))
    | ~ spl13_2
    | spl13_3
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f92,f87,f359,f78])).

fof(f429,plain,
    ( spl13_22
    | spl13_3
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f423,f357,f90,f426])).

fof(f423,plain,
    ( r2_hidden(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | spl13_3
    | ~ spl13_16 ),
    inference(unit_resulting_resolution,[],[f92,f359,f51])).

fof(f400,plain,
    ( spl13_21
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f380,f348,f85,f397])).

fof(f380,plain,
    ( v1_xboole_0(k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(unit_resulting_resolution,[],[f87,f349,f181])).

fof(f395,plain,
    ( spl13_20
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f381,f348,f85,f391])).

fof(f391,plain,
    ( spl13_20
  <=> a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f381,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(unit_resulting_resolution,[],[f349,f87,f349,f183])).

fof(f394,plain,
    ( spl13_20
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f382,f348,f85,f391])).

fof(f382,plain,
    ( a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))) = k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(unit_resulting_resolution,[],[f349,f87,f349,f183])).

fof(f389,plain,
    ( spl13_19
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(avatar_split_clause,[],[f383,f348,f85,f386])).

fof(f386,plain,
    ( spl13_19
  <=> v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f383,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))))
    | ~ spl13_2
    | ~ spl13_15 ),
    inference(unit_resulting_resolution,[],[f87,f87,f349,f275])).

fof(f373,plain,
    ( spl13_18
    | spl13_15 ),
    inference(avatar_split_clause,[],[f366,f348,f369])).

fof(f369,plain,
    ( spl13_18
  <=> r2_hidden(sK9(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f366,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_15 ),
    inference(unit_resulting_resolution,[],[f350,f116])).

fof(f372,plain,
    ( spl13_18
    | spl13_15 ),
    inference(avatar_split_clause,[],[f367,f348,f369])).

fof(f367,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | spl13_15 ),
    inference(unit_resulting_resolution,[],[f48,f350,f51])).

fof(f365,plain,
    ( spl13_17
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(avatar_split_clause,[],[f352,f324,f90,f85,f362])).

fof(f352,plain,
    ( m1_subset_1(sK12(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_13 ),
    inference(unit_resulting_resolution,[],[f87,f92,f326,f59])).

fof(f360,plain,
    ( spl13_16
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f353,f299,f90,f85,f357])).

fof(f353,plain,
    ( m1_subset_1(sK12(k2_mcart_1(sK9(sK0)),sK0,k1_mcart_1(sK9(sK0))),sK0)
    | ~ spl13_2
    | spl13_3
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f87,f92,f301,f59])).

fof(f351,plain,
    ( ~ spl13_14
    | ~ spl13_15
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f342,f153,f348,f344])).

fof(f344,plain,
    ( spl13_14
  <=> v1_relat_1(k1_tarski(sK9(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f342,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(k1_tarski(sK9(sK0)),k1_mcart_1(sK9(sK0))))
    | ~ v1_relat_1(k1_tarski(sK9(sK0)))
    | ~ spl13_9 ),
    inference(superposition,[],[f340,f155])).

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(a_2_0_mcart_1(k1_tarski(k4_tarski(X0,X1)),X0))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f337,f95])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(a_2_0_mcart_1(k1_tarski(k4_tarski(X0,X1)),X0))
      | v1_xboole_0(k1_tarski(k4_tarski(X0,X1)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(resolution,[],[f336,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(X0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f76,f50])).

fof(f328,plain,
    ( spl13_13
    | spl13_11 ),
    inference(avatar_split_clause,[],[f321,f310,f324])).

fof(f310,plain,
    ( spl13_11
  <=> v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f321,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_11 ),
    inference(unit_resulting_resolution,[],[f312,f116])).

fof(f312,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_11 ),
    inference(avatar_component_clause,[],[f310])).

fof(f327,plain,
    ( spl13_13
    | spl13_11 ),
    inference(avatar_split_clause,[],[f322,f310,f324])).

fof(f322,plain,
    ( r2_hidden(sK9(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | spl13_11 ),
    inference(unit_resulting_resolution,[],[f48,f312,f51])).

fof(f320,plain,
    ( ~ spl13_11
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f308,f299,f310])).

fof(f308,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_10 ),
    inference(resolution,[],[f301,f58])).

fof(f319,plain,
    ( spl13_12
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f307,f299,f315])).

fof(f315,plain,
    ( spl13_12
  <=> m1_subset_1(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f307,plain,
    ( m1_subset_1(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_10 ),
    inference(resolution,[],[f301,f50])).

fof(f318,plain,
    ( spl13_12
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f305,f299,f315])).

fof(f305,plain,
    ( m1_subset_1(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f301,f50])).

fof(f313,plain,
    ( ~ spl13_11
    | ~ spl13_10 ),
    inference(avatar_split_clause,[],[f306,f299,f310])).

fof(f306,plain,
    ( ~ v1_xboole_0(a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_10 ),
    inference(unit_resulting_resolution,[],[f301,f58])).

fof(f302,plain,
    ( spl13_10
    | ~ spl13_2
    | spl13_3 ),
    inference(avatar_split_clause,[],[f293,f90,f85,f299])).

fof(f293,plain,
    ( r2_hidden(k2_mcart_1(sK9(sK0)),a_2_0_mcart_1(sK0,k1_mcart_1(sK9(sK0))))
    | ~ spl13_2
    | spl13_3 ),
    inference(unit_resulting_resolution,[],[f92,f48,f87,f78])).

fof(f156,plain,
    ( spl13_9
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f151,f119,f85,f153])).

fof(f151,plain,
    ( sK9(sK0) = k4_tarski(k1_mcart_1(sK9(sK0)),k2_mcart_1(sK9(sK0)))
    | ~ spl13_2
    | ~ spl13_6 ),
    inference(unit_resulting_resolution,[],[f87,f121,f49])).

fof(f147,plain,
    ( ~ spl13_8
    | spl13_5 ),
    inference(avatar_split_clause,[],[f142,f109,f144])).

fof(f142,plain,
    ( ~ m1_subset_1(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_5 ),
    inference(unit_resulting_resolution,[],[f95,f111,f51])).

fof(f141,plain,
    ( ~ spl13_7
    | spl13_4 ),
    inference(avatar_split_clause,[],[f136,f104,f138])).

fof(f136,plain,
    ( ~ m1_subset_1(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_4 ),
    inference(unit_resulting_resolution,[],[f95,f106,f51])).

fof(f122,plain,
    ( spl13_6
    | spl13_3 ),
    inference(avatar_split_clause,[],[f113,f90,f119])).

fof(f113,plain,
    ( r2_hidden(sK9(sK0),sK0)
    | spl13_3 ),
    inference(unit_resulting_resolution,[],[f92,f48,f51])).

fof(f112,plain,
    ( ~ spl13_5
    | spl13_1 ),
    inference(avatar_split_clause,[],[f101,f80,f109])).

fof(f101,plain,
    ( ~ r2_hidden(a_2_0_mcart_1(sK0,sK1),k1_tarski(k11_relat_1(sK0,sK1)))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f82,f74])).

fof(f107,plain,
    ( ~ spl13_4
    | spl13_1 ),
    inference(avatar_split_clause,[],[f102,f80,f104])).

fof(f102,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1),k1_tarski(a_2_0_mcart_1(sK0,sK1)))
    | spl13_1 ),
    inference(unit_resulting_resolution,[],[f82,f74])).

fof(f93,plain,(
    ~ spl13_3 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] : k11_relat_1(X0,X1) != a_2_0_mcart_1(X0,X1)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] : k11_relat_1(X0,X1) != a_2_0_mcart_1(X0,X1)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_relat_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_mcart_1)).

fof(f88,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    k11_relat_1(sK0,sK1) != a_2_0_mcart_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------

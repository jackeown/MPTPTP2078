%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t53_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:44 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  818 (3054 expanded)
%              Number of leaves         :  210 (1171 expanded)
%              Depth                    :   15
%              Number of atoms          : 2081 (7758 expanded)
%              Number of equality atoms :  110 ( 655 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3013,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f111,f118,f127,f134,f141,f154,f166,f173,f180,f207,f215,f240,f247,f256,f269,f281,f291,f303,f310,f335,f346,f389,f396,f419,f431,f458,f465,f494,f504,f516,f544,f551,f565,f572,f579,f586,f642,f658,f667,f681,f714,f721,f731,f739,f753,f768,f780,f812,f819,f826,f835,f841,f844,f860,f883,f1008,f1017,f1024,f1035,f1044,f1051,f1060,f1078,f1086,f1103,f1114,f1136,f1144,f1185,f1203,f1210,f1221,f1228,f1252,f1259,f1266,f1289,f1300,f1318,f1329,f1350,f1357,f1366,f1380,f1387,f1411,f1418,f1425,f1432,f1439,f1446,f1453,f1470,f1495,f1522,f1544,f1564,f1571,f1585,f1607,f1618,f1627,f1671,f1678,f1706,f1717,f1726,f1733,f1742,f1749,f1784,f1792,f1803,f1812,f1820,f1822,f1825,f1832,f1834,f1841,f1843,f1857,f1922,f1955,f1964,f1976,f1983,f1994,f2025,f2036,f2055,f2068,f2083,f2090,f2097,f2106,f2121,f2145,f2155,f2162,f2172,f2179,f2196,f2203,f2210,f2222,f2229,f2314,f2318,f2322,f2345,f2354,f2424,f2452,f2487,f2501,f2508,f2529,f2560,f2568,f2598,f2621,f2628,f2641,f2648,f2676,f2683,f2732,f2734,f2876,f2883,f2909,f2916,f2924,f2948,f2957,f2964,f2971,f2985,f2993,f2996,f3002,f3012])).

fof(f3012,plain,
    ( ~ spl5_0
    | ~ spl5_18
    | spl5_31
    | ~ spl5_254 ),
    inference(avatar_contradiction_clause,[],[f3011])).

fof(f3011,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_31
    | ~ spl5_254 ),
    inference(subsumption_resolution,[],[f3010,f103])).

fof(f103,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f3010,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_18
    | ~ spl5_31
    | ~ spl5_254 ),
    inference(subsumption_resolution,[],[f3009,f225])).

fof(f225,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f220,f193])).

fof(f193,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f172,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_k7_subset_1)).

fof(f172,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_18
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f220,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0)
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f172,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',redefinition_k7_subset_1)).

fof(f3009,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_31
    | ~ spl5_254 ),
    inference(subsumption_resolution,[],[f3000,f252])).

fof(f252,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_31
  <=> k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) != k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f3000,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_254 ),
    inference(resolution,[],[f2105,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t52_pre_topc)).

fof(f2105,plain,
    ( v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_254 ),
    inference(avatar_component_clause,[],[f2104])).

fof(f2104,plain,
    ( spl5_254
  <=> v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).

fof(f3002,plain,
    ( ~ spl5_0
    | ~ spl5_18
    | spl5_31
    | ~ spl5_254 ),
    inference(avatar_contradiction_clause,[],[f3001])).

fof(f3001,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_31
    | ~ spl5_254 ),
    inference(subsumption_resolution,[],[f2998,f252])).

fof(f2998,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_254 ),
    inference(unit_resulting_resolution,[],[f103,f225,f2105,f80])).

fof(f2996,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | spl5_255
    | ~ spl5_310 ),
    inference(avatar_contradiction_clause,[],[f2995])).

fof(f2995,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_255
    | ~ spl5_310 ),
    inference(subsumption_resolution,[],[f2994,f147])).

fof(f147,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_12
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2994,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_255
    | ~ spl5_310 ),
    inference(forward_demodulation,[],[f2988,f2982])).

fof(f2982,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_18
    | ~ spl5_310 ),
    inference(subsumption_resolution,[],[f2978,f172])).

fof(f2978,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_310 ),
    inference(superposition,[],[f2875,f93])).

fof(f2875,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_310 ),
    inference(avatar_component_clause,[],[f2874])).

fof(f2874,plain,
    ( spl5_310
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_310])])).

fof(f2988,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_255 ),
    inference(unit_resulting_resolution,[],[f103,f172,f225,f2102,f558])).

fof(f558,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(superposition,[],[f83,f93])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',d6_pre_topc)).

fof(f2102,plain,
    ( ~ v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_255 ),
    inference(avatar_component_clause,[],[f2101])).

fof(f2101,plain,
    ( spl5_255
  <=> ~ v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_255])])).

fof(f2993,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | spl5_255
    | ~ spl5_310 ),
    inference(avatar_contradiction_clause,[],[f2992])).

fof(f2992,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_255
    | ~ spl5_310 ),
    inference(subsumption_resolution,[],[f2991,f147])).

fof(f2991,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_255
    | ~ spl5_310 ),
    inference(forward_demodulation,[],[f2990,f2982])).

fof(f2990,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_255 ),
    inference(forward_demodulation,[],[f2989,f220])).

fof(f2989,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_255 ),
    inference(unit_resulting_resolution,[],[f103,f225,f2102,f83])).

fof(f2985,plain,
    ( ~ spl5_0
    | spl5_13
    | ~ spl5_18
    | ~ spl5_254
    | ~ spl5_310 ),
    inference(avatar_contradiction_clause,[],[f2984])).

fof(f2984,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_13
    | ~ spl5_18
    | ~ spl5_254
    | ~ spl5_310 ),
    inference(subsumption_resolution,[],[f2983,f144])).

fof(f144,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_13
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2983,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_254
    | ~ spl5_310 ),
    inference(backward_demodulation,[],[f2982,f2111])).

fof(f2111,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_254 ),
    inference(forward_demodulation,[],[f2107,f220])).

fof(f2107,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_254 ),
    inference(unit_resulting_resolution,[],[f103,f225,f2105,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2971,plain,
    ( ~ spl5_327
    | spl5_319 ),
    inference(avatar_split_clause,[],[f2935,f2922,f2969])).

fof(f2969,plain,
    ( spl5_327
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_327])])).

fof(f2922,plain,
    ( spl5_319
  <=> ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_319])])).

fof(f2935,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_319 ),
    inference(unit_resulting_resolution,[],[f2923,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t1_subset)).

fof(f2923,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_319 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2964,plain,
    ( ~ spl5_325
    | ~ spl5_308 ),
    inference(avatar_split_clause,[],[f2889,f2681,f2962])).

fof(f2962,plain,
    ( spl5_325
  <=> ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(sK2(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_325])])).

fof(f2681,plain,
    ( spl5_308
  <=> r2_hidden(sK2(sK2(sK1)),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_308])])).

fof(f2889,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(sK2(sK2(sK1))))
    | ~ spl5_308 ),
    inference(unit_resulting_resolution,[],[f2682,f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f188,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t5_subset)).

fof(f188,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f187,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t4_subset)).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f159,f87])).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t2_subset)).

fof(f159,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f87,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',antisymmetry_r2_hidden)).

fof(f2682,plain,
    ( r2_hidden(sK2(sK2(sK1)),sK2(sK1))
    | ~ spl5_308 ),
    inference(avatar_component_clause,[],[f2681])).

fof(f2957,plain,
    ( ~ spl5_323
    | spl5_73 ),
    inference(avatar_split_clause,[],[f2027,f570,f2955])).

fof(f2955,plain,
    ( spl5_323
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_323])])).

fof(f570,plain,
    ( spl5_73
  <=> ~ m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2027,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(sK2(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl5_73 ),
    inference(unit_resulting_resolution,[],[f84,f571,f94])).

fof(f571,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f570])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',existence_m1_subset_1)).

fof(f2948,plain,
    ( ~ spl5_321
    | ~ spl5_222 ),
    inference(avatar_split_clause,[],[f1756,f1747,f2946])).

fof(f2946,plain,
    ( spl5_321
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_321])])).

fof(f1747,plain,
    ( spl5_222
  <=> r2_hidden(sK2(k2_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f1756,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0))))
    | ~ spl5_222 ),
    inference(unit_resulting_resolution,[],[f1748,f189])).

fof(f1748,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_222 ),
    inference(avatar_component_clause,[],[f1747])).

fof(f2924,plain,
    ( ~ spl5_319
    | spl5_65 ),
    inference(avatar_split_clause,[],[f1930,f511,f2922])).

fof(f511,plain,
    ( spl5_65
  <=> ~ v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f1930,plain,
    ( ~ m1_subset_1(sK2(k1_zfmisc_1(k1_xboole_0)),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_65 ),
    inference(unit_resulting_resolution,[],[f512,f187])).

fof(f512,plain,
    ( ~ v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f511])).

fof(f2916,plain,
    ( ~ spl5_317
    | spl5_227 ),
    inference(avatar_split_clause,[],[f1795,f1790,f2914])).

fof(f2914,plain,
    ( spl5_317
  <=> ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_317])])).

fof(f1790,plain,
    ( spl5_227
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_227])])).

fof(f1795,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0))))
    | ~ spl5_227 ),
    inference(unit_resulting_resolution,[],[f1791,f86])).

fof(f1791,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0))))
    | ~ spl5_227 ),
    inference(avatar_component_clause,[],[f1790])).

fof(f2909,plain,
    ( ~ spl5_315
    | spl5_67 ),
    inference(avatar_split_clause,[],[f552,f542,f2907])).

fof(f2907,plain,
    ( spl5_315
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(sK2(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_315])])).

fof(f542,plain,
    ( spl5_67
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f552,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(sK2(sK1)))))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f84,f543,f94])).

fof(f543,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f542])).

fof(f2883,plain,
    ( ~ spl5_313
    | spl5_295 ),
    inference(avatar_split_clause,[],[f2612,f2590,f2881])).

fof(f2881,plain,
    ( spl5_313
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(sK2(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_313])])).

fof(f2590,plain,
    ( spl5_295
  <=> ~ m1_subset_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_295])])).

fof(f2612,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(sK2(sK1))))
    | ~ spl5_295 ),
    inference(unit_resulting_resolution,[],[f84,f2591,f94])).

fof(f2591,plain,
    ( ~ m1_subset_1(sK1,sK2(sK1))
    | ~ spl5_295 ),
    inference(avatar_component_clause,[],[f2590])).

fof(f2876,plain,
    ( spl5_310
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f1870,f171,f139,f102,f2874])).

fof(f139,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f1870,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f1862,f220])).

fof(f1862,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f103,f140,f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f78,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_l1_pre_topc)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t22_pre_topc)).

fof(f140,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f2734,plain,
    ( ~ spl5_58
    | ~ spl5_296
    | spl5_309 ),
    inference(avatar_contradiction_clause,[],[f2733])).

fof(f2733,plain,
    ( $false
    | ~ spl5_58
    | ~ spl5_296
    | ~ spl5_309 ),
    inference(subsumption_resolution,[],[f2730,f464])).

fof(f464,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl5_58
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2730,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_296
    | ~ spl5_309 ),
    inference(backward_demodulation,[],[f2697,f2679])).

fof(f2679,plain,
    ( ~ r2_hidden(sK2(sK2(sK1)),sK2(sK1))
    | ~ spl5_309 ),
    inference(avatar_component_clause,[],[f2678])).

fof(f2678,plain,
    ( spl5_309
  <=> ~ r2_hidden(sK2(sK2(sK1)),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_309])])).

fof(f2697,plain,
    ( k1_xboole_0 = sK2(sK1)
    | ~ spl5_296 ),
    inference(unit_resulting_resolution,[],[f2597,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t6_boole)).

fof(f2597,plain,
    ( v1_xboole_0(sK2(sK1))
    | ~ spl5_296 ),
    inference(avatar_component_clause,[],[f2596])).

fof(f2596,plain,
    ( spl5_296
  <=> v1_xboole_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_296])])).

fof(f2732,plain,
    ( spl5_51
    | ~ spl5_296 ),
    inference(avatar_contradiction_clause,[],[f2731])).

fof(f2731,plain,
    ( $false
    | ~ spl5_51
    | ~ spl5_296 ),
    inference(subsumption_resolution,[],[f2719,f392])).

fof(f392,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl5_51
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f2719,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_296 ),
    inference(backward_demodulation,[],[f2697,f2597])).

fof(f2683,plain,
    ( spl5_308
    | spl5_297 ),
    inference(avatar_split_clause,[],[f2607,f2593,f2681])).

fof(f2593,plain,
    ( spl5_297
  <=> ~ v1_xboole_0(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_297])])).

fof(f2607,plain,
    ( r2_hidden(sK2(sK2(sK1)),sK2(sK1))
    | ~ spl5_297 ),
    inference(unit_resulting_resolution,[],[f84,f2594,f87])).

fof(f2594,plain,
    ( ~ v1_xboole_0(sK2(sK1))
    | ~ spl5_297 ),
    inference(avatar_component_clause,[],[f2593])).

fof(f2676,plain,
    ( ~ spl5_307
    | spl5_297 ),
    inference(avatar_split_clause,[],[f2606,f2593,f2674])).

fof(f2674,plain,
    ( spl5_307
  <=> ~ r2_hidden(sK2(sK1),sK2(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_307])])).

fof(f2606,plain,
    ( ~ r2_hidden(sK2(sK1),sK2(sK2(sK1)))
    | ~ spl5_297 ),
    inference(unit_resulting_resolution,[],[f84,f2594,f159])).

fof(f2648,plain,
    ( ~ spl5_305
    | spl5_299 ),
    inference(avatar_split_clause,[],[f2633,f2619,f2646])).

fof(f2646,plain,
    ( spl5_305
  <=> ~ r2_hidden(sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_305])])).

fof(f2619,plain,
    ( spl5_299
  <=> ~ m1_subset_1(sK2(sK1),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_299])])).

fof(f2633,plain,
    ( ~ r2_hidden(sK2(sK1),sK2(sK1))
    | ~ spl5_299 ),
    inference(unit_resulting_resolution,[],[f2620,f86])).

fof(f2620,plain,
    ( ~ m1_subset_1(sK2(sK1),sK2(sK1))
    | ~ spl5_299 ),
    inference(avatar_component_clause,[],[f2619])).

fof(f2641,plain,
    ( ~ spl5_303
    | spl5_75
    | spl5_297 ),
    inference(avatar_split_clause,[],[f2608,f2593,f577,f2639])).

fof(f2639,plain,
    ( spl5_303
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_303])])).

fof(f577,plain,
    ( spl5_75
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f2608,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK1))
    | ~ spl5_75
    | ~ spl5_297 ),
    inference(unit_resulting_resolution,[],[f578,f2594,f87])).

fof(f578,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK1))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f577])).

fof(f2628,plain,
    ( ~ spl5_301
    | spl5_107 ),
    inference(avatar_split_clause,[],[f2058,f830,f2626])).

fof(f2626,plain,
    ( spl5_301
  <=> ~ r2_hidden(k2_pre_topc(sK0,k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_301])])).

fof(f830,plain,
    ( spl5_107
  <=> ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f2058,plain,
    ( ~ r2_hidden(k2_pre_topc(sK0,k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_107 ),
    inference(unit_resulting_resolution,[],[f84,f831,f94])).

fof(f831,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f830])).

fof(f2621,plain,
    ( ~ spl5_299
    | spl5_297 ),
    inference(avatar_split_clause,[],[f2599,f2593,f2619])).

fof(f2599,plain,
    ( ~ m1_subset_1(sK2(sK1),sK2(sK1))
    | ~ spl5_297 ),
    inference(unit_resulting_resolution,[],[f2594,f187])).

fof(f2598,plain,
    ( ~ spl5_295
    | spl5_296
    | spl5_41 ),
    inference(avatar_split_clause,[],[f311,f301,f2596,f2590])).

fof(f301,plain,
    ( spl5_41
  <=> ~ r2_hidden(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f311,plain,
    ( v1_xboole_0(sK2(sK1))
    | ~ m1_subset_1(sK1,sK2(sK1))
    | ~ spl5_41 ),
    inference(resolution,[],[f302,f87])).

fof(f302,plain,
    ( ~ r2_hidden(sK1,sK2(sK1))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f301])).

fof(f2568,plain,
    ( ~ spl5_293
    | ~ spl5_18
    | spl5_219 ),
    inference(avatar_split_clause,[],[f2480,f1728,f171,f2566])).

fof(f2566,plain,
    ( spl5_293
  <=> k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_293])])).

fof(f1728,plain,
    ( spl5_219
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_219])])).

fof(f2480,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0
    | ~ spl5_18
    | ~ spl5_219 ),
    inference(subsumption_resolution,[],[f2478,f172])).

fof(f2478,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_219 ),
    inference(superposition,[],[f1729,f93])).

fof(f1729,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0
    | ~ spl5_219 ),
    inference(avatar_component_clause,[],[f1728])).

fof(f2560,plain,
    ( ~ spl5_291
    | spl5_237 ),
    inference(avatar_split_clause,[],[f1985,f1981,f2558])).

fof(f2558,plain,
    ( spl5_291
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_291])])).

fof(f1981,plain,
    ( spl5_237
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f1985,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(sK1))))
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f84,f1982,f94])).

fof(f1982,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_237 ),
    inference(avatar_component_clause,[],[f1981])).

fof(f2529,plain,
    ( ~ spl5_289
    | spl5_65
    | spl5_109 ),
    inference(avatar_split_clause,[],[f2387,f855,f511,f2527])).

fof(f2527,plain,
    ( spl5_289
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_289])])).

fof(f855,plain,
    ( spl5_109
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f2387,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_65
    | ~ spl5_109 ),
    inference(unit_resulting_resolution,[],[f856,f84,f512,f181])).

fof(f856,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_109 ),
    inference(avatar_component_clause,[],[f855])).

fof(f2508,plain,
    ( ~ spl5_287
    | spl5_269 ),
    inference(avatar_split_clause,[],[f2213,f2194,f2506])).

fof(f2506,plain,
    ( spl5_287
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_287])])).

fof(f2194,plain,
    ( spl5_269
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_269])])).

fof(f2213,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_269 ),
    inference(unit_resulting_resolution,[],[f2195,f86])).

fof(f2195,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_269 ),
    inference(avatar_component_clause,[],[f2194])).

fof(f2501,plain,
    ( ~ spl5_285
    | spl5_233 ),
    inference(avatar_split_clause,[],[f1967,f1962,f2499])).

fof(f2499,plain,
    ( spl5_285
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_285])])).

fof(f1962,plain,
    ( spl5_233
  <=> ~ m1_subset_1(sK2(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_233])])).

fof(f1967,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl5_233 ),
    inference(unit_resulting_resolution,[],[f84,f1963,f94])).

fof(f1963,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),sK1)
    | ~ spl5_233 ),
    inference(avatar_component_clause,[],[f1962])).

fof(f2487,plain,
    ( ~ spl5_283
    | ~ spl5_18
    | spl5_219 ),
    inference(avatar_split_clause,[],[f2479,f1728,f171,f2485])).

fof(f2485,plain,
    ( spl5_283
  <=> ~ v1_xboole_0(k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_283])])).

fof(f2479,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl5_18
    | ~ spl5_219 ),
    inference(forward_demodulation,[],[f2477,f220])).

fof(f2477,plain,
    ( ~ v1_xboole_0(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl5_219 ),
    inference(unit_resulting_resolution,[],[f1729,f76])).

fof(f2452,plain,
    ( ~ spl5_281
    | spl5_107 ),
    inference(avatar_split_clause,[],[f2059,f830,f2450])).

fof(f2450,plain,
    ( spl5_281
  <=> ~ r2_hidden(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_281])])).

fof(f2059,plain,
    ( ~ r2_hidden(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_107 ),
    inference(unit_resulting_resolution,[],[f831,f86])).

fof(f2424,plain,
    ( spl5_278
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_242
    | ~ spl5_272 ),
    inference(avatar_split_clause,[],[f2415,f2208,f2034,f152,f102,f2422])).

fof(f2422,plain,
    ( spl5_278
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_278])])).

fof(f152,plain,
    ( spl5_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2034,plain,
    ( spl5_242
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).

fof(f2208,plain,
    ( spl5_272
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_272])])).

fof(f2415,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_242
    | ~ spl5_272 ),
    inference(unit_resulting_resolution,[],[f2035,f2209,f507])).

fof(f507,plain,
    ( ! [X0] :
        ( v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f506,f103])).

fof(f506,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) != X0
        | v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f81,f153])).

fof(f153,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2209,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl5_272 ),
    inference(avatar_component_clause,[],[f2208])).

fof(f2035,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_242 ),
    inference(avatar_component_clause,[],[f2034])).

fof(f2354,plain,
    ( ~ spl5_108
    | ~ spl5_150 ),
    inference(avatar_contradiction_clause,[],[f2353])).

fof(f2353,plain,
    ( $false
    | ~ spl5_108
    | ~ spl5_150 ),
    inference(subsumption_resolution,[],[f2352,f84])).

fof(f2352,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_108
    | ~ spl5_150 ),
    inference(forward_demodulation,[],[f2351,f2242])).

fof(f2242,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f859,f76])).

fof(f859,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_108 ),
    inference(avatar_component_clause,[],[f858])).

fof(f858,plain,
    ( spl5_108
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f2351,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_108
    | ~ spl5_150 ),
    inference(forward_demodulation,[],[f2236,f2242])).

fof(f2236,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_108
    | ~ spl5_150 ),
    inference(unit_resulting_resolution,[],[f1258,f859,f95])).

fof(f1258,plain,
    ( r2_hidden(sK2(sK2(k1_xboole_0)),sK2(k1_xboole_0))
    | ~ spl5_150 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f1257,plain,
    ( spl5_150
  <=> r2_hidden(sK2(sK2(k1_xboole_0)),sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f2345,plain,
    ( ~ spl5_58
    | ~ spl5_108
    | spl5_277 ),
    inference(avatar_contradiction_clause,[],[f2344])).

fof(f2344,plain,
    ( $false
    | ~ spl5_58
    | ~ spl5_108
    | ~ spl5_277 ),
    inference(subsumption_resolution,[],[f2312,f464])).

fof(f2312,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_108
    | ~ spl5_277 ),
    inference(backward_demodulation,[],[f2242,f2225])).

fof(f2225,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_277 ),
    inference(avatar_component_clause,[],[f2224])).

fof(f2224,plain,
    ( spl5_277
  <=> ~ r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_277])])).

fof(f2322,plain,
    ( ~ spl5_58
    | ~ spl5_108
    | spl5_157 ),
    inference(avatar_contradiction_clause,[],[f2321])).

fof(f2321,plain,
    ( $false
    | ~ spl5_58
    | ~ spl5_108
    | ~ spl5_157 ),
    inference(subsumption_resolution,[],[f2266,f464])).

fof(f2266,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_108
    | ~ spl5_157 ),
    inference(backward_demodulation,[],[f2242,f1299])).

fof(f1299,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f1298])).

fof(f1298,plain,
    ( spl5_157
  <=> ~ r2_hidden(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f2318,plain,
    ( ~ spl5_108
    | spl5_155 ),
    inference(avatar_contradiction_clause,[],[f2317])).

fof(f2317,plain,
    ( $false
    | ~ spl5_108
    | ~ spl5_155 ),
    inference(subsumption_resolution,[],[f2263,f84])).

fof(f2263,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_108
    | ~ spl5_155 ),
    inference(backward_demodulation,[],[f2242,f1288])).

fof(f1288,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_155 ),
    inference(avatar_component_clause,[],[f1287])).

fof(f1287,plain,
    ( spl5_155
  <=> ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_155])])).

fof(f2314,plain,
    ( spl5_51
    | ~ spl5_108 ),
    inference(avatar_contradiction_clause,[],[f2313])).

fof(f2313,plain,
    ( $false
    | ~ spl5_51
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f2255,f392])).

fof(f2255,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_108 ),
    inference(backward_demodulation,[],[f2242,f859])).

fof(f2229,plain,
    ( spl5_276
    | spl5_109 ),
    inference(avatar_split_clause,[],[f913,f855,f2227])).

fof(f2227,plain,
    ( spl5_276
  <=> r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_276])])).

fof(f913,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_109 ),
    inference(unit_resulting_resolution,[],[f84,f856,f87])).

fof(f2222,plain,
    ( ~ spl5_275
    | spl5_109 ),
    inference(avatar_split_clause,[],[f912,f855,f2220])).

fof(f2220,plain,
    ( spl5_275
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_275])])).

fof(f912,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_109 ),
    inference(unit_resulting_resolution,[],[f84,f856,f159])).

fof(f2210,plain,
    ( spl5_272
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f483,f139,f102,f2208])).

fof(f483,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f103,f140,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',projectivity_k2_pre_topc)).

fof(f2203,plain,
    ( ~ spl5_271
    | spl5_71
    | ~ spl5_242 ),
    inference(avatar_split_clause,[],[f2131,f2034,f563,f2201])).

fof(f2201,plain,
    ( spl5_271
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_271])])).

fof(f563,plain,
    ( spl5_71
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f2131,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | ~ spl5_71
    | ~ spl5_242 ),
    inference(unit_resulting_resolution,[],[f564,f2035,f94])).

fof(f564,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f563])).

fof(f2196,plain,
    ( ~ spl5_269
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f2042,f584,f2194])).

fof(f584,plain,
    ( spl5_76
  <=> r2_hidden(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f2042,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_76 ),
    inference(unit_resulting_resolution,[],[f585,f189])).

fof(f585,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f584])).

fof(f2179,plain,
    ( ~ spl5_267
    | spl5_65
    | spl5_259 ),
    inference(avatar_split_clause,[],[f2147,f2143,f511,f2177])).

fof(f2177,plain,
    ( spl5_267
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_267])])).

fof(f2143,plain,
    ( spl5_259
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).

fof(f2147,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_65
    | ~ spl5_259 ),
    inference(unit_resulting_resolution,[],[f512,f2144,f87])).

fof(f2144,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_259 ),
    inference(avatar_component_clause,[],[f2143])).

fof(f2172,plain,
    ( ~ spl5_265
    | spl5_93
    | ~ spl5_242 ),
    inference(avatar_split_clause,[],[f2132,f2034,f737,f2170])).

fof(f2170,plain,
    ( spl5_265
  <=> ~ r2_hidden(sK2(k1_xboole_0),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_265])])).

fof(f737,plain,
    ( spl5_93
  <=> ~ m1_subset_1(sK2(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f2132,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k2_pre_topc(sK0,sK1))
    | ~ spl5_93
    | ~ spl5_242 ),
    inference(unit_resulting_resolution,[],[f738,f2035,f94])).

fof(f738,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f737])).

fof(f2162,plain,
    ( ~ spl5_263
    | spl5_87 ),
    inference(avatar_split_clause,[],[f1938,f712,f2160])).

fof(f2160,plain,
    ( spl5_263
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_263])])).

fof(f712,plain,
    ( spl5_87
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f1938,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f84,f713,f94])).

fof(f713,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f712])).

fof(f2155,plain,
    ( ~ spl5_261
    | spl5_61 ),
    inference(avatar_split_clause,[],[f1927,f492,f2153])).

fof(f2153,plain,
    ( spl5_261
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_261])])).

fof(f492,plain,
    ( spl5_61
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f1927,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f84,f493,f94])).

fof(f493,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f492])).

fof(f2145,plain,
    ( ~ spl5_259
    | spl5_85 ),
    inference(avatar_split_clause,[],[f682,f679,f2143])).

fof(f679,plain,
    ( spl5_85
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f682,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f84,f680,f94])).

fof(f680,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f679])).

fof(f2121,plain,
    ( ~ spl5_257
    | spl5_33 ),
    inference(avatar_split_clause,[],[f294,f261,f2119])).

fof(f2119,plain,
    ( spl5_257
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_257])])).

fof(f261,plain,
    ( spl5_33
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f294,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f84,f262,f94])).

fof(f262,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f261])).

fof(f2106,plain,
    ( spl5_254
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f1944,f254,f171,f152,f102,f2104])).

fof(f254,plain,
    ( spl5_30
  <=> k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1944,plain,
    ( v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(unit_resulting_resolution,[],[f225,f255,f507])).

fof(f255,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f2097,plain,
    ( ~ spl5_253
    | spl5_79 ),
    inference(avatar_split_clause,[],[f1888,f637,f2095])).

fof(f2095,plain,
    ( spl5_253
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_253])])).

fof(f637,plain,
    ( spl5_79
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f1888,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_79 ),
    inference(unit_resulting_resolution,[],[f84,f638,f94])).

fof(f638,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f637])).

fof(f2090,plain,
    ( ~ spl5_251
    | spl5_247 ),
    inference(avatar_split_clause,[],[f2075,f2066,f2088])).

fof(f2088,plain,
    ( spl5_251
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_251])])).

fof(f2066,plain,
    ( spl5_247
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_247])])).

fof(f2075,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_247 ),
    inference(unit_resulting_resolution,[],[f2067,f86])).

fof(f2067,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_247 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f2083,plain,
    ( ~ spl5_249
    | spl5_245 ),
    inference(avatar_split_clause,[],[f2071,f2053,f2081])).

fof(f2081,plain,
    ( spl5_249
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_249])])).

fof(f2053,plain,
    ( spl5_245
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_245])])).

fof(f2071,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_245 ),
    inference(unit_resulting_resolution,[],[f2054,f86])).

fof(f2054,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_245 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f2068,plain,
    ( ~ spl5_247
    | ~ spl5_58
    | spl5_207 ),
    inference(avatar_split_clause,[],[f1914,f1625,f463,f2066])).

fof(f1625,plain,
    ( spl5_207
  <=> ~ m1_subset_1(sK2(k1_xboole_0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f1914,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_58
    | ~ spl5_207 ),
    inference(unit_resulting_resolution,[],[f1626,f464,f94])).

fof(f1626,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k2_struct_0(sK0))
    | ~ spl5_207 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f2055,plain,
    ( ~ spl5_245
    | ~ spl5_58
    | spl5_155 ),
    inference(avatar_split_clause,[],[f1912,f1287,f463,f2053])).

fof(f1912,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_58
    | ~ spl5_155 ),
    inference(unit_resulting_resolution,[],[f1288,f464,f94])).

fof(f2036,plain,
    ( spl5_242
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f314,f139,f102,f2034])).

fof(f314,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f103,f140,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_k2_pre_topc)).

fof(f2025,plain,
    ( ~ spl5_241
    | spl5_67 ),
    inference(avatar_split_clause,[],[f553,f542,f2023])).

fof(f2023,plain,
    ( spl5_241
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_241])])).

fof(f553,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_67 ),
    inference(unit_resulting_resolution,[],[f543,f86])).

fof(f1994,plain,
    ( ~ spl5_239
    | spl5_237 ),
    inference(avatar_split_clause,[],[f1986,f1981,f1992])).

fof(f1992,plain,
    ( spl5_239
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_239])])).

fof(f1986,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_237 ),
    inference(unit_resulting_resolution,[],[f1982,f86])).

fof(f1983,plain,
    ( ~ spl5_237
    | ~ spl5_58
    | spl5_233 ),
    inference(avatar_split_clause,[],[f1965,f1962,f463,f1981])).

fof(f1965,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl5_58
    | ~ spl5_233 ),
    inference(unit_resulting_resolution,[],[f464,f1963,f94])).

fof(f1976,plain,
    ( ~ spl5_235
    | spl5_79 ),
    inference(avatar_split_clause,[],[f1889,f637,f1974])).

fof(f1974,plain,
    ( spl5_235
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).

fof(f1889,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_79 ),
    inference(unit_resulting_resolution,[],[f638,f86])).

fof(f1964,plain,
    ( ~ spl5_233
    | spl5_35
    | spl5_231 ),
    inference(avatar_split_clause,[],[f1956,f1953,f264,f1962])).

fof(f264,plain,
    ( spl5_35
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1953,plain,
    ( spl5_231
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).

fof(f1956,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),sK1)
    | ~ spl5_35
    | ~ spl5_231 ),
    inference(unit_resulting_resolution,[],[f265,f1954,f87])).

fof(f1954,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK1)
    | ~ spl5_231 ),
    inference(avatar_component_clause,[],[f1953])).

fof(f265,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f264])).

fof(f1955,plain,
    ( ~ spl5_231
    | ~ spl5_10
    | spl5_93 ),
    inference(avatar_split_clause,[],[f1868,f737,f139,f1953])).

fof(f1868,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK1)
    | ~ spl5_10
    | ~ spl5_93 ),
    inference(unit_resulting_resolution,[],[f738,f140,f94])).

fof(f1922,plain,
    ( ~ spl5_83
    | spl5_85 ),
    inference(avatar_split_clause,[],[f683,f679,f665])).

fof(f665,plain,
    ( spl5_83
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f683,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f680,f86])).

fof(f1857,plain,
    ( ~ spl5_13
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f1845,f254,f171,f143])).

fof(f1845,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(trivial_inequality_removal,[],[f1844])).

fof(f1844,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(backward_demodulation,[],[f255,f228])).

fof(f228,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f220,f73])).

fof(f73,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ( ~ v3_pre_topc(sK1,sK0)
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v2_pre_topc(sK0) )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v3_pre_topc(sK1,sK0) ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f57,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v3_pre_topc(X1,X0)
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v3_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,sK0)
              & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v2_pre_topc(sK0) )
            | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v3_pre_topc(X1,sK0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v3_pre_topc(sK1,X0)
            & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1))
            & v2_pre_topc(X0) )
          | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1))
            & v3_pre_topc(sK1,X0) ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t53_pre_topc)).

fof(f1843,plain,
    ( spl5_87
    | ~ spl5_90 ),
    inference(avatar_contradiction_clause,[],[f1842])).

fof(f1842,plain,
    ( $false
    | ~ spl5_87
    | ~ spl5_90 ),
    inference(subsumption_resolution,[],[f713,f937])).

fof(f937,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_90 ),
    inference(resolution,[],[f727,f86])).

fof(f727,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl5_90
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f1841,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | spl5_95
    | ~ spl5_218 ),
    inference(avatar_contradiction_clause,[],[f1840])).

fof(f1840,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_95
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f749,f1839])).

fof(f1839,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1838,f103])).

fof(f1838,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1837,f172])).

fof(f1837,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_80
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1805,f1823])).

fof(f1823,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_12
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f147,f657])).

fof(f657,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl5_80
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1805,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_218 ),
    inference(superposition,[],[f83,f1732])).

fof(f1732,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_218 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f1731,plain,
    ( spl5_218
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_218])])).

fof(f749,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f748])).

fof(f748,plain,
    ( spl5_95
  <=> ~ v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f1834,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(avatar_contradiction_clause,[],[f1833])).

fof(f1833,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f755,f1828])).

fof(f1828,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f1827,f1823])).

fof(f1827,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f1814,f657])).

fof(f1814,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f1813,f74])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',t3_boole)).

fof(f1813,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)) != k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18
    | ~ spl5_80 ),
    inference(forward_demodulation,[],[f228,f657])).

fof(f755,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f103,f172,f752,f80])).

fof(f752,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl5_94
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f1832,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(avatar_contradiction_clause,[],[f1831])).

fof(f1831,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f1830,f103])).

fof(f1830,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f1829,f172])).

fof(f1829,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f757,f1828])).

fof(f757,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_94 ),
    inference(resolution,[],[f752,f80])).

fof(f1825,plain,
    ( ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(avatar_contradiction_clause,[],[f1824])).

fof(f1824,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f1823,f1816])).

fof(f1816,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f1815,f657])).

fof(f1815,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f1814,f720])).

fof(f720,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl5_88
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f1822,plain,
    ( ~ spl5_18
    | ~ spl5_48
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(avatar_contradiction_clause,[],[f1821])).

fof(f1821,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_48
    | ~ spl5_80
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f385,f1816])).

fof(f385,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl5_48
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1820,plain,
    ( ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88
    | ~ spl5_134
    | ~ spl5_218 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_80
    | ~ spl5_88
    | ~ spl5_134
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1809,f1816])).

fof(f1809,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_18
    | ~ spl5_134
    | ~ spl5_218 ),
    inference(backward_demodulation,[],[f1808,f1143])).

fof(f1143,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ spl5_134 ),
    inference(avatar_component_clause,[],[f1142])).

fof(f1142,plain,
    ( spl5_134
  <=> v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f1808,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_18
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1804,f172])).

fof(f1804,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_218 ),
    inference(superposition,[],[f1732,f93])).

fof(f1812,plain,
    ( ~ spl5_18
    | spl5_49
    | ~ spl5_134
    | ~ spl5_218 ),
    inference(avatar_contradiction_clause,[],[f1811])).

fof(f1811,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_49
    | ~ spl5_134
    | ~ spl5_218 ),
    inference(subsumption_resolution,[],[f1809,f388])).

fof(f388,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl5_49
  <=> ~ v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1803,plain,
    ( ~ spl5_229
    | spl5_213 ),
    inference(avatar_split_clause,[],[f1708,f1704,f1801])).

fof(f1801,plain,
    ( spl5_229
  <=> ~ r2_hidden(k2_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_229])])).

fof(f1704,plain,
    ( spl5_213
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f1708,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f84,f1705,f94])).

fof(f1705,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_213 ),
    inference(avatar_component_clause,[],[f1704])).

fof(f1792,plain,
    ( ~ spl5_227
    | ~ spl5_210 ),
    inference(avatar_split_clause,[],[f1687,f1676,f1790])).

fof(f1676,plain,
    ( spl5_210
  <=> r2_hidden(sK2(k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f1687,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(sK2(k2_struct_0(sK0))))
    | ~ spl5_210 ),
    inference(unit_resulting_resolution,[],[f1677,f189])).

fof(f1677,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ spl5_210 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f1784,plain,
    ( ~ spl5_225
    | spl5_199 ),
    inference(avatar_split_clause,[],[f1593,f1577,f1782])).

fof(f1782,plain,
    ( spl5_225
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).

fof(f1577,plain,
    ( spl5_199
  <=> ~ m1_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_199])])).

fof(f1593,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k2_struct_0(sK0))))
    | ~ spl5_199 ),
    inference(unit_resulting_resolution,[],[f84,f1578,f94])).

fof(f1578,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_199 ),
    inference(avatar_component_clause,[],[f1577])).

fof(f1749,plain,
    ( spl5_222
    | spl5_45
    | ~ spl5_216 ),
    inference(avatar_split_clause,[],[f1735,f1724,f333,f1747])).

fof(f333,plain,
    ( spl5_45
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1724,plain,
    ( spl5_216
  <=> m1_subset_1(sK2(k2_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_216])])).

fof(f1735,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_45
    | ~ spl5_216 ),
    inference(unit_resulting_resolution,[],[f334,f1725,f87])).

fof(f1725,plain,
    ( m1_subset_1(sK2(k2_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_216 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f334,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f333])).

fof(f1742,plain,
    ( ~ spl5_221
    | spl5_45
    | ~ spl5_216 ),
    inference(avatar_split_clause,[],[f1734,f1724,f333,f1740])).

fof(f1740,plain,
    ( spl5_221
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_221])])).

fof(f1734,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k2_struct_0(sK0)))
    | ~ spl5_45
    | ~ spl5_216 ),
    inference(unit_resulting_resolution,[],[f334,f1725,f159])).

fof(f1733,plain,
    ( spl5_218
    | ~ spl5_6
    | ~ spl5_18
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f793,f640,f171,f125,f1731])).

fof(f125,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f640,plain,
    ( spl5_78
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f793,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0
    | ~ spl5_6
    | ~ spl5_18
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f792,f74])).

fof(f792,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0
    | ~ spl5_6
    | ~ spl5_18
    | ~ spl5_78 ),
    inference(forward_demodulation,[],[f787,f220])).

fof(f787,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0
    | ~ spl5_6
    | ~ spl5_78 ),
    inference(unit_resulting_resolution,[],[f126,f641,f78])).

fof(f641,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f640])).

fof(f126,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1726,plain,
    ( spl5_216
    | ~ spl5_18
    | ~ spl5_210 ),
    inference(avatar_split_clause,[],[f1684,f1676,f171,f1724])).

fof(f1684,plain,
    ( m1_subset_1(sK2(k2_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_18
    | ~ spl5_210 ),
    inference(unit_resulting_resolution,[],[f172,f1677,f94])).

fof(f1717,plain,
    ( ~ spl5_215
    | spl5_213 ),
    inference(avatar_split_clause,[],[f1709,f1704,f1715])).

fof(f1715,plain,
    ( spl5_215
  <=> ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f1709,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f1705,f86])).

fof(f1706,plain,
    ( ~ spl5_213
    | ~ spl5_34
    | ~ spl5_210 ),
    inference(avatar_split_clause,[],[f1688,f1676,f267,f1704])).

fof(f267,plain,
    ( spl5_34
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1688,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_210 ),
    inference(unit_resulting_resolution,[],[f1677,f633])).

fof(f633,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f592,f591])).

fof(f591,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f268,f76])).

fof(f268,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f267])).

fof(f592,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_34 ),
    inference(resolution,[],[f268,f95])).

fof(f1678,plain,
    ( spl5_210
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1588,f1580,f1676])).

fof(f1580,plain,
    ( spl5_201
  <=> ~ v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f1588,plain,
    ( r2_hidden(sK2(k2_struct_0(sK0)),k2_struct_0(sK0))
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f84,f1581,f87])).

fof(f1581,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl5_201 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1671,plain,
    ( ~ spl5_209
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1587,f1580,f1669])).

fof(f1669,plain,
    ( spl5_209
  <=> ~ r2_hidden(k2_struct_0(sK0),sK2(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_209])])).

fof(f1587,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),sK2(k2_struct_0(sK0)))
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f84,f1581,f159])).

fof(f1627,plain,
    ( ~ spl5_207
    | spl5_105
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1590,f1580,f824,f1625])).

fof(f824,plain,
    ( spl5_105
  <=> ~ r2_hidden(sK2(k1_xboole_0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f1590,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k2_struct_0(sK0))
    | ~ spl5_105
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f825,f1581,f87])).

fof(f825,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k2_struct_0(sK0))
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f824])).

fof(f1618,plain,
    ( ~ spl5_205
    | spl5_203 ),
    inference(avatar_split_clause,[],[f1610,f1605,f1616])).

fof(f1616,plain,
    ( spl5_205
  <=> ~ r2_hidden(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f1605,plain,
    ( spl5_203
  <=> ~ m1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f1610,plain,
    ( ~ r2_hidden(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_203 ),
    inference(unit_resulting_resolution,[],[f1606,f86])).

fof(f1606,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_203 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f1607,plain,
    ( ~ spl5_203
    | spl5_201 ),
    inference(avatar_split_clause,[],[f1586,f1580,f1605])).

fof(f1586,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_201 ),
    inference(unit_resulting_resolution,[],[f1581,f187])).

fof(f1585,plain,
    ( ~ spl5_199
    | spl5_200
    | spl5_25 ),
    inference(avatar_split_clause,[],[f216,f213,f1583,f1577])).

fof(f1583,plain,
    ( spl5_200
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f213,plain,
    ( spl5_25
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f216,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_25 ),
    inference(resolution,[],[f214,f87])).

fof(f214,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f1571,plain,
    ( ~ spl5_197
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1551,f1542,f1569])).

fof(f1569,plain,
    ( spl5_197
  <=> ~ r2_hidden(u1_struct_0(sK4),k2_pre_topc(sK4,k2_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f1542,plain,
    ( spl5_192
  <=> m1_subset_1(k2_pre_topc(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f1551,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),k2_pre_topc(sK4,k2_struct_0(sK4)))
    | ~ spl5_192 ),
    inference(unit_resulting_resolution,[],[f1543,f189])).

fof(f1543,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_192 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f1564,plain,
    ( spl5_194
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f799,f164,f109,f1562])).

fof(f1562,plain,
    ( spl5_194
  <=> k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),k4_xboole_0(k2_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3))))) = sK2(k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f109,plain,
    ( spl5_2
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f164,plain,
    ( spl5_16
  <=> m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f799,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),k4_xboole_0(k2_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3))))) = sK2(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_2
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f781,f219])).

fof(f219,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),X0) = k4_xboole_0(k2_struct_0(sK3),X0)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f165,f93])).

fof(f165,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f781,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),k7_subset_1(u1_struct_0(sK3),k2_struct_0(sK3),sK2(k1_zfmisc_1(u1_struct_0(sK3))))) = sK2(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f110,f84,f78])).

fof(f110,plain,
    ( l1_struct_0(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1544,plain,
    ( spl5_192
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f316,f178,f116,f1542])).

fof(f116,plain,
    ( spl5_4
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f178,plain,
    ( spl5_20
  <=> m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f316,plain,
    ( m1_subset_1(k2_pre_topc(sK4,k2_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f117,f179,f88])).

fof(f179,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f117,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f1522,plain,
    ( spl5_190
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_106
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1065,f1058,f833,f171,f102,f1520])).

fof(f1520,plain,
    ( spl5_190
  <=> v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f833,plain,
    ( spl5_106
  <=> m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1058,plain,
    ( spl5_122
  <=> v4_pre_topc(k2_pre_topc(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1065,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_106
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f1061,f220])).

fof(f1061,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)),sK0)
    | ~ spl5_0
    | ~ spl5_106
    | ~ spl5_122 ),
    inference(unit_resulting_resolution,[],[f103,f834,f1059,f82])).

fof(f1059,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_xboole_0),sK0)
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f834,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f833])).

fof(f1495,plain,
    ( spl5_188
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f480,f116,f1493])).

fof(f1493,plain,
    ( spl5_188
  <=> k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4)))) = k2_pre_topc(sK4,k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f480,plain,
    ( k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4)))) = k2_pre_topc(sK4,k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4)))))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f117,f84,f89])).

fof(f1470,plain,
    ( spl5_186
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_126
    | ~ spl5_182 ),
    inference(avatar_split_clause,[],[f1459,f1444,f1084,f152,f102,f1468])).

fof(f1468,plain,
    ( spl5_186
  <=> v4_pre_topc(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f1084,plain,
    ( spl5_126
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f1444,plain,
    ( spl5_182
  <=> k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f1459,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_126
    | ~ spl5_182 ),
    inference(unit_resulting_resolution,[],[f1085,f1445,f507])).

fof(f1445,plain,
    ( k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_182 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1085,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_126 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1453,plain,
    ( ~ spl5_185
    | spl5_171 ),
    inference(avatar_split_clause,[],[f1398,f1385,f1451])).

fof(f1451,plain,
    ( spl5_185
  <=> ~ r2_hidden(sK2(k1_xboole_0),k1_zfmisc_1(sK2(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_185])])).

fof(f1385,plain,
    ( spl5_171
  <=> ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(sK2(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f1398,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_zfmisc_1(sK2(sK2(k1_xboole_0))))
    | ~ spl5_171 ),
    inference(unit_resulting_resolution,[],[f1386,f86])).

fof(f1386,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(sK2(sK2(k1_xboole_0))))
    | ~ spl5_171 ),
    inference(avatar_component_clause,[],[f1385])).

fof(f1446,plain,
    ( spl5_182
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f479,f102,f1444])).

fof(f479,plain,
    ( k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f103,f84,f89])).

fof(f1439,plain,
    ( ~ spl5_181
    | spl5_169 ),
    inference(avatar_split_clause,[],[f1394,f1378,f1437])).

fof(f1437,plain,
    ( spl5_181
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1378,plain,
    ( spl5_169
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1394,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(sK2(u1_struct_0(sK0))))
    | ~ spl5_169 ),
    inference(unit_resulting_resolution,[],[f1379,f86])).

fof(f1379,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(u1_struct_0(sK0))))
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f1432,plain,
    ( ~ spl5_179
    | spl5_167 ),
    inference(avatar_split_clause,[],[f1390,f1364,f1430])).

fof(f1430,plain,
    ( spl5_179
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_179])])).

fof(f1364,plain,
    ( spl5_167
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f1390,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0))))
    | ~ spl5_167 ),
    inference(unit_resulting_resolution,[],[f1365,f86])).

fof(f1365,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0))))
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f1425,plain,
    ( ~ spl5_177
    | spl5_155 ),
    inference(avatar_split_clause,[],[f1291,f1287,f1423])).

fof(f1423,plain,
    ( spl5_177
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1291,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_155 ),
    inference(unit_resulting_resolution,[],[f84,f1288,f94])).

fof(f1418,plain,
    ( ~ spl5_175
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1230,f1219,f1416])).

fof(f1416,plain,
    ( spl5_175
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f1219,plain,
    ( spl5_145
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f1230,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK2(k1_xboole_0))))
    | ~ spl5_145 ),
    inference(unit_resulting_resolution,[],[f84,f1220,f94])).

fof(f1220,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(k1_xboole_0))
    | ~ spl5_145 ),
    inference(avatar_component_clause,[],[f1219])).

fof(f1411,plain,
    ( ~ spl5_173
    | spl5_129 ),
    inference(avatar_split_clause,[],[f1105,f1101,f1409])).

fof(f1409,plain,
    ( spl5_173
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f1101,plain,
    ( spl5_129
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f1105,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f84,f1102,f94])).

fof(f1102,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_129 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1387,plain,
    ( ~ spl5_171
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f1276,f1257,f1385])).

fof(f1276,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(sK2(sK2(k1_xboole_0))))
    | ~ spl5_150 ),
    inference(unit_resulting_resolution,[],[f1258,f189])).

fof(f1380,plain,
    ( ~ spl5_169
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f1092,f1049,f1378])).

fof(f1049,plain,
    ( spl5_120
  <=> r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1092,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(sK2(u1_struct_0(sK0))))
    | ~ spl5_120 ),
    inference(unit_resulting_resolution,[],[f1050,f189])).

fof(f1050,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_120 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1366,plain,
    ( ~ spl5_167
    | spl5_69
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f950,f726,f549,f1364])).

fof(f549,plain,
    ( spl5_69
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f950,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0))))
    | ~ spl5_69
    | ~ spl5_90 ),
    inference(unit_resulting_resolution,[],[f727,f550,f94])).

fof(f550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_69 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1357,plain,
    ( ~ spl5_165
    | spl5_93 ),
    inference(avatar_split_clause,[],[f740,f737,f1355])).

fof(f1355,plain,
    ( spl5_165
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f740,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_93 ),
    inference(unit_resulting_resolution,[],[f84,f738,f94])).

fof(f1350,plain,
    ( ~ spl5_163
    | spl5_69 ),
    inference(avatar_split_clause,[],[f555,f549,f1348])).

fof(f1348,plain,
    ( spl5_163
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f555,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(k1_zfmisc_1(sK2(k1_xboole_0)))))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f84,f550,f94])).

fof(f1329,plain,
    ( ~ spl5_161
    | spl5_159 ),
    inference(avatar_split_clause,[],[f1321,f1316,f1327])).

fof(f1327,plain,
    ( spl5_161
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f1316,plain,
    ( spl5_159
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1321,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_159 ),
    inference(unit_resulting_resolution,[],[f1317,f86])).

fof(f1317,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_159 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1318,plain,
    ( ~ spl5_159
    | ~ spl5_90
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1192,f1177,f726,f1316])).

fof(f1177,plain,
    ( spl5_137
  <=> ~ m1_subset_1(k1_xboole_0,sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f1192,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_90
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f727,f1178,f94])).

fof(f1178,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK2(k1_xboole_0))
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1300,plain,
    ( ~ spl5_157
    | spl5_155 ),
    inference(avatar_split_clause,[],[f1292,f1287,f1298])).

fof(f1292,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_155 ),
    inference(unit_resulting_resolution,[],[f1288,f86])).

fof(f1289,plain,
    ( ~ spl5_155
    | ~ spl5_34
    | ~ spl5_150 ),
    inference(avatar_split_clause,[],[f1277,f1257,f267,f1287])).

fof(f1277,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_150 ),
    inference(unit_resulting_resolution,[],[f1258,f633])).

fof(f1266,plain,
    ( ~ spl5_153
    | spl5_137 ),
    inference(avatar_split_clause,[],[f1194,f1177,f1264])).

fof(f1264,plain,
    ( spl5_153
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(sK2(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f1194,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_zfmisc_1(sK2(k1_xboole_0))))
    | ~ spl5_137 ),
    inference(unit_resulting_resolution,[],[f84,f1178,f94])).

fof(f1259,plain,
    ( spl5_150
    | spl5_139 ),
    inference(avatar_split_clause,[],[f1188,f1180,f1257])).

fof(f1180,plain,
    ( spl5_139
  <=> ~ v1_xboole_0(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f1188,plain,
    ( r2_hidden(sK2(sK2(k1_xboole_0)),sK2(k1_xboole_0))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f84,f1181,f87])).

fof(f1181,plain,
    ( ~ v1_xboole_0(sK2(k1_xboole_0))
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1252,plain,
    ( ~ spl5_149
    | spl5_139 ),
    inference(avatar_split_clause,[],[f1187,f1180,f1250])).

fof(f1250,plain,
    ( spl5_149
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK2(sK2(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f1187,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK2(sK2(k1_xboole_0)))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f84,f1181,f159])).

fof(f1228,plain,
    ( ~ spl5_147
    | spl5_143 ),
    inference(avatar_split_clause,[],[f1213,f1208,f1226])).

fof(f1226,plain,
    ( spl5_147
  <=> ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f1208,plain,
    ( spl5_143
  <=> ~ m1_subset_1(sK2(k1_xboole_0),sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f1213,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),sK2(k1_xboole_0))
    | ~ spl5_143 ),
    inference(unit_resulting_resolution,[],[f1209,f86])).

fof(f1209,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),sK2(k1_xboole_0))
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f1221,plain,
    ( ~ spl5_145
    | spl5_99
    | spl5_139 ),
    inference(avatar_split_clause,[],[f1189,f1180,f778,f1219])).

fof(f778,plain,
    ( spl5_99
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f1189,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(k1_xboole_0))
    | ~ spl5_99
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f779,f1181,f87])).

fof(f779,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_xboole_0))
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f778])).

fof(f1210,plain,
    ( ~ spl5_143
    | spl5_139 ),
    inference(avatar_split_clause,[],[f1186,f1180,f1208])).

fof(f1186,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),sK2(k1_xboole_0))
    | ~ spl5_139 ),
    inference(unit_resulting_resolution,[],[f1181,f187])).

fof(f1203,plain,
    ( spl5_140
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f313,f116,f1201])).

fof(f1201,plain,
    ( spl5_140
  <=> m1_subset_1(k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f313,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK2(k1_zfmisc_1(u1_struct_0(sK4)))),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f117,f84,f88])).

fof(f1185,plain,
    ( ~ spl5_137
    | spl5_138
    | spl5_57 ),
    inference(avatar_split_clause,[],[f478,f456,f1183,f1177])).

fof(f1183,plain,
    ( spl5_138
  <=> v1_xboole_0(sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f456,plain,
    ( spl5_57
  <=> ~ r2_hidden(k1_xboole_0,sK2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f478,plain,
    ( v1_xboole_0(sK2(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK2(k1_xboole_0))
    | ~ spl5_57 ),
    inference(resolution,[],[f457,f87])).

fof(f457,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_xboole_0))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f456])).

fof(f1144,plain,
    ( spl5_134
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f758,f751,f171,f102,f1142])).

fof(f758,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f754,f220])).

fof(f754,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ spl5_0
    | ~ spl5_18
    | ~ spl5_94 ),
    inference(unit_resulting_resolution,[],[f103,f172,f752,f82])).

fof(f1136,plain,
    ( ~ spl5_133
    | spl5_71
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f945,f833,f563,f1134])).

fof(f1134,plain,
    ( spl5_133
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f945,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_71
    | ~ spl5_106 ),
    inference(unit_resulting_resolution,[],[f564,f834,f94])).

fof(f1114,plain,
    ( ~ spl5_131
    | spl5_129 ),
    inference(avatar_split_clause,[],[f1106,f1101,f1112])).

fof(f1112,plain,
    ( spl5_131
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f1106,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_129 ),
    inference(unit_resulting_resolution,[],[f1102,f86])).

fof(f1103,plain,
    ( ~ spl5_129
    | ~ spl5_50
    | ~ spl5_120 ),
    inference(avatar_split_clause,[],[f1091,f1049,f394,f1101])).

fof(f394,plain,
    ( spl5_50
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f1091,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_50
    | ~ spl5_120 ),
    inference(unit_resulting_resolution,[],[f395,f1050,f95])).

fof(f395,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f394])).

fof(f1086,plain,
    ( spl5_126
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f312,f102,f1084])).

fof(f312,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f103,f84,f88])).

fof(f1078,plain,
    ( ~ spl5_125
    | spl5_93
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f955,f833,f737,f1076])).

fof(f1076,plain,
    ( spl5_125
  <=> ~ r2_hidden(sK2(k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f955,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_93
    | ~ spl5_106 ),
    inference(unit_resulting_resolution,[],[f834,f738,f94])).

fof(f1060,plain,
    ( spl5_122
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_106
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f1052,f1022,f833,f152,f102,f1058])).

fof(f1022,plain,
    ( spl5_114
  <=> k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1052,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_xboole_0),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_106
    | ~ spl5_114 ),
    inference(unit_resulting_resolution,[],[f103,f153,f834,f1023,f81])).

fof(f1023,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1051,plain,
    ( spl5_120
    | spl5_45 ),
    inference(avatar_split_clause,[],[f338,f333,f1049])).

fof(f338,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f84,f334,f87])).

fof(f1044,plain,
    ( ~ spl5_119
    | spl5_45 ),
    inference(avatar_split_clause,[],[f337,f333,f1042])).

fof(f1042,plain,
    ( spl5_119
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f337,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f84,f334,f159])).

fof(f1035,plain,
    ( ~ spl5_117
    | spl5_113 ),
    inference(avatar_split_clause,[],[f1027,f1015,f1033])).

fof(f1033,plain,
    ( spl5_117
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1015,plain,
    ( spl5_113
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f1027,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_113 ),
    inference(unit_resulting_resolution,[],[f1016,f86])).

fof(f1016,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f1024,plain,
    ( spl5_114
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f613,f267,f139,f102,f1022])).

fof(f613,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f483])).

fof(f1017,plain,
    ( ~ spl5_113
    | spl5_109 ),
    inference(avatar_split_clause,[],[f911,f855,f1015])).

fof(f911,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_109 ),
    inference(unit_resulting_resolution,[],[f856,f187])).

fof(f1008,plain,
    ( ~ spl5_111
    | spl5_71 ),
    inference(avatar_split_clause,[],[f772,f563,f1006])).

fof(f1006,plain,
    ( spl5_111
  <=> ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f772,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_71 ),
    inference(unit_resulting_resolution,[],[f564,f86])).

fof(f883,plain,
    ( spl5_53
    | ~ spl5_86
    | ~ spl5_108 ),
    inference(avatar_contradiction_clause,[],[f882])).

fof(f882,plain,
    ( $false
    | ~ spl5_53
    | ~ spl5_86
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f877,f418])).

fof(f418,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl5_53
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f877,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_86
    | ~ spl5_108 ),
    inference(backward_demodulation,[],[f870,f710])).

fof(f710,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f709])).

fof(f709,plain,
    ( spl5_86
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f870,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl5_108 ),
    inference(unit_resulting_resolution,[],[f859,f76])).

fof(f860,plain,
    ( spl5_108
    | ~ spl5_86
    | spl5_91 ),
    inference(avatar_split_clause,[],[f851,f729,f709,f858])).

fof(f729,plain,
    ( spl5_91
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f851,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_86
    | ~ spl5_91 ),
    inference(unit_resulting_resolution,[],[f730,f710,f87])).

fof(f730,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f729])).

fof(f844,plain,
    ( spl5_86
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f839,f817,f709])).

fof(f817,plain,
    ( spl5_102
  <=> k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f839,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_102 ),
    inference(superposition,[],[f84,f818])).

fof(f818,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f817])).

fof(f841,plain,
    ( spl5_87
    | ~ spl5_102 ),
    inference(avatar_contradiction_clause,[],[f840])).

fof(f840,plain,
    ( $false
    | ~ spl5_87
    | ~ spl5_102 ),
    inference(subsumption_resolution,[],[f839,f713])).

fof(f835,plain,
    ( spl5_106
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f611,f267,f139,f102,f833])).

fof(f611,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f314])).

fof(f826,plain,
    ( ~ spl5_105
    | ~ spl5_18
    | spl5_93 ),
    inference(avatar_split_clause,[],[f741,f737,f171,f824])).

fof(f741,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k2_struct_0(sK0))
    | ~ spl5_18
    | ~ spl5_93 ),
    inference(unit_resulting_resolution,[],[f172,f738,f94])).

fof(f819,plain,
    ( spl5_102
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f693,f514,f817])).

fof(f514,plain,
    ( spl5_64
  <=> v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f693,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f515,f76])).

fof(f515,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f514])).

fof(f812,plain,
    ( ~ spl5_101
    | ~ spl5_34
    | spl5_77 ),
    inference(avatar_split_clause,[],[f623,f581,f267,f810])).

fof(f810,plain,
    ( spl5_101
  <=> ~ r2_hidden(sK2(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f581,plain,
    ( spl5_77
  <=> ~ r2_hidden(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f623,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_34
    | ~ spl5_77 ),
    inference(backward_demodulation,[],[f591,f582])).

fof(f582,plain,
    ( ~ r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f581])).

fof(f780,plain,
    ( ~ spl5_99
    | ~ spl5_34
    | spl5_75 ),
    inference(avatar_split_clause,[],[f622,f577,f267,f778])).

fof(f622,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_75 ),
    inference(backward_demodulation,[],[f591,f578])).

fof(f768,plain,
    ( ~ spl5_97
    | spl5_69 ),
    inference(avatar_split_clause,[],[f556,f549,f766])).

fof(f766,plain,
    ( spl5_97
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f556,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_69 ),
    inference(unit_resulting_resolution,[],[f550,f86])).

fof(f753,plain,
    ( spl5_94
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f745,f719,f171,f152,f102,f751])).

fof(f745,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_0
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f103,f153,f172,f720,f81])).

fof(f739,plain,
    ( ~ spl5_93
    | ~ spl5_34
    | spl5_47 ),
    inference(avatar_split_clause,[],[f612,f341,f267,f737])).

fof(f341,plain,
    ( spl5_47
  <=> ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f612,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_34
    | ~ spl5_47 ),
    inference(backward_demodulation,[],[f591,f342])).

fof(f342,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f341])).

fof(f731,plain,
    ( ~ spl5_91
    | ~ spl5_34
    | spl5_63 ),
    inference(avatar_split_clause,[],[f617,f502,f267,f729])).

fof(f502,plain,
    ( spl5_63
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f617,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_63 ),
    inference(backward_demodulation,[],[f591,f503])).

fof(f503,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f502])).

fof(f721,plain,
    ( spl5_88
    | ~ spl5_30
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f626,f267,f254,f719])).

fof(f626,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl5_30
    | ~ spl5_34 ),
    inference(forward_demodulation,[],[f601,f74])).

fof(f601,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)) = k4_xboole_0(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl5_30
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f255])).

fof(f714,plain,
    ( ~ spl5_87
    | ~ spl5_34
    | spl5_61 ),
    inference(avatar_split_clause,[],[f614,f492,f267,f712])).

fof(f614,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_34
    | ~ spl5_61 ),
    inference(backward_demodulation,[],[f591,f493])).

fof(f681,plain,
    ( ~ spl5_85
    | spl5_33
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f602,f267,f261,f679])).

fof(f602,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_33
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f262])).

fof(f667,plain,
    ( ~ spl5_83
    | spl5_23
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f598,f267,f205,f665])).

fof(f205,plain,
    ( spl5_23
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f598,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_23
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f206])).

fof(f206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f658,plain,
    ( spl5_80
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f591,f267,f656])).

fof(f642,plain,
    ( spl5_78
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f596,f267,f139,f640])).

fof(f596,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f591,f140])).

fof(f586,plain,
    ( spl5_76
    | spl5_45
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f537,f344,f333,f584])).

fof(f344,plain,
    ( spl5_46
  <=> m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f537,plain,
    ( r2_hidden(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f334,f345,f87])).

fof(f345,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f344])).

fof(f579,plain,
    ( ~ spl5_75
    | spl5_45
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f536,f344,f333,f577])).

fof(f536,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK1))
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(unit_resulting_resolution,[],[f334,f345,f159])).

fof(f572,plain,
    ( ~ spl5_73
    | spl5_65 ),
    inference(avatar_split_clause,[],[f534,f511,f570])).

fof(f534,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_65 ),
    inference(unit_resulting_resolution,[],[f195,f512,f87])).

fof(f195,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f84,f189])).

fof(f565,plain,
    ( ~ spl5_71
    | spl5_45 ),
    inference(avatar_split_clause,[],[f336,f333,f563])).

fof(f336,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_45 ),
    inference(unit_resulting_resolution,[],[f334,f187])).

fof(f551,plain,
    ( ~ spl5_69
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f526,f463,f549])).

fof(f526,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2(k1_xboole_0)))
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f464,f189])).

fof(f544,plain,
    ( ~ spl5_67
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f447,f308,f542])).

fof(f308,plain,
    ( spl5_42
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f447,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK1)))
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f309,f189])).

fof(f309,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f308])).

fof(f516,plain,
    ( spl5_64
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f508,f394,f514])).

fof(f508,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f84,f467,f87])).

fof(f467,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f84,f395,f95])).

fof(f504,plain,
    ( ~ spl5_63
    | spl5_61 ),
    inference(avatar_split_clause,[],[f496,f492,f502])).

fof(f496,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f493,f86])).

fof(f494,plain,
    ( ~ spl5_61
    | ~ spl5_42
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f466,f394,f308,f492])).

fof(f466,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_42
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f309,f395,f95])).

fof(f465,plain,
    ( spl5_58
    | spl5_51 ),
    inference(avatar_split_clause,[],[f403,f391,f463])).

fof(f403,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl5_51 ),
    inference(unit_resulting_resolution,[],[f84,f392,f87])).

fof(f458,plain,
    ( ~ spl5_57
    | spl5_51 ),
    inference(avatar_split_clause,[],[f402,f391,f456])).

fof(f402,plain,
    ( ~ r2_hidden(k1_xboole_0,sK2(k1_xboole_0))
    | ~ spl5_51 ),
    inference(unit_resulting_resolution,[],[f84,f392,f159])).

fof(f431,plain,
    ( ~ spl5_55
    | spl5_53 ),
    inference(avatar_split_clause,[],[f421,f417,f429])).

fof(f429,plain,
    ( spl5_55
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f421,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl5_53 ),
    inference(unit_resulting_resolution,[],[f418,f86])).

fof(f419,plain,
    ( ~ spl5_53
    | spl5_51 ),
    inference(avatar_split_clause,[],[f401,f391,f417])).

fof(f401,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_51 ),
    inference(unit_resulting_resolution,[],[f392,f187])).

fof(f396,plain,
    ( spl5_50
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f363,f267,f394])).

fof(f363,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f351,f268])).

fof(f351,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f268,f76])).

fof(f389,plain,
    ( ~ spl5_49
    | spl5_13
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f357,f267,f143,f387])).

fof(f357,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f351,f144])).

fof(f346,plain,
    ( spl5_46
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f322,f308,f139,f344])).

fof(f322,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f140,f309,f94])).

fof(f335,plain,
    ( ~ spl5_45
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f323,f308,f139,f333])).

fof(f323,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f140,f309,f95])).

fof(f310,plain,
    ( spl5_42
    | spl5_35 ),
    inference(avatar_split_clause,[],[f272,f264,f308])).

fof(f272,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f84,f265,f87])).

fof(f303,plain,
    ( ~ spl5_41
    | spl5_35 ),
    inference(avatar_split_clause,[],[f271,f264,f301])).

fof(f271,plain,
    ( ~ r2_hidden(sK1,sK2(sK1))
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f84,f265,f159])).

fof(f291,plain,
    ( ~ spl5_39
    | spl5_37 ),
    inference(avatar_split_clause,[],[f283,f279,f289])).

fof(f289,plain,
    ( spl5_39
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f279,plain,
    ( spl5_37
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f283,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f280,f86])).

fof(f280,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f279])).

fof(f281,plain,
    ( ~ spl5_37
    | spl5_35 ),
    inference(avatar_split_clause,[],[f270,f264,f279])).

fof(f270,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f265,f187])).

fof(f269,plain,
    ( ~ spl5_33
    | spl5_34
    | spl5_23 ),
    inference(avatar_split_clause,[],[f208,f205,f267,f261])).

fof(f208,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl5_23 ),
    inference(resolution,[],[f206,f87])).

fof(f256,plain,
    ( spl5_30
    | spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f229,f171,f143,f254])).

fof(f229,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f227,f144])).

fof(f227,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f220,f70])).

fof(f70,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f247,plain,
    ( ~ spl5_29
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f199,f178,f245])).

fof(f245,plain,
    ( spl5_29
  <=> ~ r2_hidden(u1_struct_0(sK4),k2_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f199,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),k2_struct_0(sK4))
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f179,f189])).

fof(f240,plain,
    ( ~ spl5_27
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f197,f164,f238])).

fof(f238,plain,
    ( spl5_27
  <=> ~ r2_hidden(u1_struct_0(sK3),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f197,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),k2_struct_0(sK3))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f165,f189])).

fof(f215,plain,
    ( ~ spl5_25
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f198,f171,f213])).

fof(f198,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f172,f189])).

fof(f207,plain,
    ( ~ spl5_23
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f196,f139,f205])).

fof(f196,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f140,f189])).

fof(f180,plain,
    ( spl5_20
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f157,f132,f178])).

fof(f132,plain,
    ( spl5_8
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f157,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f133,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',dt_k2_struct_0)).

fof(f133,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f173,plain,
    ( spl5_18
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f156,f125,f171])).

fof(f156,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f126,f77])).

fof(f166,plain,
    ( spl5_16
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f155,f109,f164])).

fof(f155,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f110,f77])).

fof(f154,plain,
    ( spl5_12
    | spl5_14 ),
    inference(avatar_split_clause,[],[f68,f152,f146])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f141,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f67,f139])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f134,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f120,f116,f132])).

fof(f120,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f117,f79])).

fof(f127,plain,
    ( spl5_6
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f119,f102,f125])).

fof(f119,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f103,f79])).

fof(f118,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f97,f116])).

fof(f97,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f64])).

fof(f64,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK4) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',existence_l1_pre_topc)).

fof(f111,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f96,f109])).

fof(f96,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f62])).

fof(f62,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t53_pre_topc.p',existence_l1_struct_0)).

fof(f104,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f66,f102])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------

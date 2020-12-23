%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t124_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  979 (10871 expanded)
%              Number of leaves         :  138 (3633 expanded)
%              Depth                    :   20
%              Number of atoms          : 2982 (23777 expanded)
%              Number of equality atoms :  292 (6582 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4997,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f91,f98,f347,f1574,f1647,f1654,f1661,f1671,f1681,f1685,f1689,f1699,f1709,f1719,f1723,f1727,f1731,f1740,f1747,f1757,f1762,f1766,f1773,f1774,f1781,f1782,f1793,f1803,f1813,f2029,f2032,f2035,f2046,f2057,f2065,f2068,f2085,f2090,f2092,f2097,f2099,f2101,f2105,f2109,f2111,f2116,f2118,f2122,f2124,f2125,f2126,f2128,f2132,f2136,f2140,f2141,f2147,f2153,f2160,f2162,f2166,f2170,f2174,f2175,f2181,f2187,f2190,f2197,f2200,f2204,f2209,f2213,f2218,f2220,f2224,f2228,f2229,f2231,f2232,f2234,f2235,f2236,f2242,f2246,f2251,f2256,f2258,f2259,f2260,f2263,f2266,f2267,f2269,f2278,f2279,f2281,f2283,f2285,f2293,f2294,f2295,f2297,f2305,f2329,f2330,f2331,f2345,f2352,f2359,f2366,f2373,f2386,f2389,f2405,f2418,f2440,f2447,f2474,f2506,f2529,f2536,f2543,f2550,f2557,f2564,f2573,f2579,f2646,f2671,f2672,f2674,f2706,f2712,f2730,f2737,f2758,f2787,f2792,f2796,f2798,f2800,f2803,f2805,f2807,f2809,f2919,f2922,f2933,f2943,f2946,f2956,f2957,f2959,f2960,f2961,f2962,f2964,f2966,f2969,f2981,f2988,f2992,f3008,f3010,f3030,f3031,f3037,f3045,f3075,f3080,f3086,f3107,f3203,f3215,f3260,f3376,f3380,f3381,f3382,f3383,f3384,f3406,f3538,f3542,f3625,f3669,f3789,f3827,f3832,f3858,f3879,f3881,f3883,f3884,f3885,f3889,f3893,f3897,f3901,f3902,f3903,f3907,f3938,f3939,f3977,f3986,f3993,f4000,f4069,f4116,f4142,f4182,f4265,f4378,f4382,f4713,f4726,f4728,f4731,f4741,f4743,f4871,f4898,f4970,f4977,f4992,f4996])).

fof(f4996,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_204 ),
    inference(avatar_contradiction_clause,[],[f4995])).

fof(f4995,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f4994,f83])).

fof(f83,plain,
    ( ~ v2_funct_1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_1
  <=> ~ v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f4994,plain,
    ( v2_funct_1(sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f4993,f97])).

fof(f97,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f4993,plain,
    ( ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | ~ spl5_2
    | ~ spl5_204 ),
    inference(subsumption_resolution,[],[f4985,f90])).

fof(f90,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f4985,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | ~ spl5_204 ),
    inference(trivial_inequality_removal,[],[f4983])).

fof(f4983,plain,
    ( sK1(sK0) != sK1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | ~ spl5_204 ),
    inference(superposition,[],[f57,f4976])).

fof(f4976,plain,
    ( sK1(sK0) = sK2(sK0)
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f4975])).

fof(f4975,plain,
    ( spl5_204
  <=> sK1(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f57,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',d8_funct_1)).

fof(f4992,plain,
    ( ~ spl5_207
    | spl5_181
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f4979,f4975,f3614,f4990])).

fof(f4990,plain,
    ( spl5_207
  <=> k1_funct_1(sK0,sK1(sK0)) != sK1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f3614,plain,
    ( spl5_181
  <=> k1_funct_1(sK0,sK1(sK0)) != sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f4979,plain,
    ( k1_funct_1(sK0,sK1(sK0)) != sK1(sK0)
    | ~ spl5_181
    | ~ spl5_204 ),
    inference(backward_demodulation,[],[f4976,f3615])).

fof(f3615,plain,
    ( k1_funct_1(sK0,sK1(sK0)) != sK2(sK0)
    | ~ spl5_181 ),
    inference(avatar_component_clause,[],[f3614])).

fof(f4977,plain,
    ( spl5_204
    | ~ spl5_4
    | ~ spl5_106
    | spl5_111 ),
    inference(avatar_split_clause,[],[f4962,f2357,f2343,f96,f4975])).

fof(f2343,plain,
    ( spl5_106
  <=> k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f2357,plain,
    ( spl5_111
  <=> k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f4962,plain,
    ( sK1(sK0) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_111 ),
    inference(trivial_inequality_removal,[],[f4937])).

fof(f4937,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k11_relat_1(sK0,sK1(sK0))
    | sK1(sK0) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_111 ),
    inference(superposition,[],[f2358,f2378])).

fof(f2378,plain,
    ( ! [X1] :
        ( k11_relat_1(sK0,X1) = k4_xboole_0(k11_relat_1(sK0,X1),k11_relat_1(sK0,sK1(sK0)))
        | sK2(sK0) = X1 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f591,f2344])).

fof(f2344,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f591,plain,
    ( ! [X12,X13] :
        ( k11_relat_1(sK0,X12) = k4_xboole_0(k11_relat_1(sK0,X12),k11_relat_1(sK0,X13))
        | X12 = X13 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f551,f115])).

fof(f115,plain,
    ( ! [X0] : k9_relat_1(sK0,k1_tarski(X0)) = k11_relat_1(sK0,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f60,f97])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k9_relat_1(X0,k1_tarski(X1)) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',d16_relat_1)).

fof(f551,plain,
    ( ! [X12,X13] :
        ( k9_relat_1(sK0,k1_tarski(X12)) = k4_xboole_0(k11_relat_1(sK0,X12),k11_relat_1(sK0,X13))
        | X12 = X13 )
    | ~ spl5_4 ),
    inference(superposition,[],[f127,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t20_zfmisc_1)).

fof(f127,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k4_xboole_0(k11_relat_1(sK0,X1),k11_relat_1(sK0,X0))
    | ~ spl5_4 ),
    inference(superposition,[],[f116,f115])).

fof(f116,plain,
    ( ! [X0,X1] : k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)) = k4_xboole_0(k11_relat_1(sK0,X0),k9_relat_1(sK0,X1))
    | ~ spl5_4 ),
    inference(superposition,[],[f73,f115])).

fof(f73,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(definition_unfolding,[],[f51,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X2,X1] : k6_subset_1(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) = k9_relat_1(sK0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t124_funct_1)).

fof(f2358,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f2357])).

fof(f4970,plain,
    ( spl5_202
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | spl5_181 ),
    inference(avatar_split_clause,[],[f4963,f3614,f2364,f2343,f96,f4968])).

fof(f4968,plain,
    ( spl5_202
  <=> k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k4_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f2364,plain,
    ( spl5_112
  <=> k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f4963,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k4_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | ~ spl5_181 ),
    inference(subsumption_resolution,[],[f4930,f3615])).

fof(f4930,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k4_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112 ),
    inference(superposition,[],[f2378,f2365])).

fof(f2365,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f2364])).

fof(f4898,plain,
    ( spl5_176
    | ~ spl5_4
    | ~ spl5_198 ),
    inference(avatar_split_clause,[],[f4890,f4711,f96,f3404])).

fof(f3404,plain,
    ( spl5_176
  <=> m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f4711,plain,
    ( spl5_198
  <=> k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f4890,plain,
    ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_4
    | ~ spl5_198 ),
    inference(superposition,[],[f131,f4712])).

fof(f4712,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK1(sK0))
    | ~ spl5_198 ),
    inference(avatar_component_clause,[],[f4711])).

fof(f131,plain,
    ( ! [X6,X7] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X6),X7)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X6)))))
    | ~ spl5_4 ),
    inference(superposition,[],[f100,f116])).

fof(f100,plain,(
    ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0)))) ),
    inference(superposition,[],[f99,f73])).

fof(f99,plain,(
    ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(X0,X1)),k1_zfmisc_1(k9_relat_1(sK0,X0))) ),
    inference(superposition,[],[f74,f73])).

fof(f74,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f59,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',dt_k6_subset_1)).

fof(f4871,plain,
    ( spl5_176
    | ~ spl5_4
    | ~ spl5_198 ),
    inference(avatar_split_clause,[],[f4870,f4711,f96,f3404])).

fof(f4870,plain,
    ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_4
    | ~ spl5_198 ),
    inference(forward_demodulation,[],[f4858,f115])).

fof(f4858,plain,
    ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k1_tarski(sK1(sK0)))))))
    | ~ spl5_198 ),
    inference(superposition,[],[f101,f4712])).

fof(f101,plain,(
    ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,X0))))) ),
    inference(superposition,[],[f100,f73])).

fof(f4743,plain,
    ( ~ spl5_201
    | ~ spl5_112
    | spl5_131 ),
    inference(avatar_split_clause,[],[f4742,f2469,f2364,f4736])).

fof(f4736,plain,
    ( spl5_201
  <=> k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) != k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f2469,plain,
    ( spl5_131
  <=> k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) != k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f4742,plain,
    ( k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) != k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_112
    | ~ spl5_131 ),
    inference(forward_demodulation,[],[f2470,f2365])).

fof(f2470,plain,
    ( k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) != k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_131 ),
    inference(avatar_component_clause,[],[f2469])).

fof(f4741,plain,
    ( spl5_200
    | ~ spl5_112
    | ~ spl5_130 ),
    inference(avatar_split_clause,[],[f4734,f2472,f2364,f4739])).

fof(f4739,plain,
    ( spl5_200
  <=> k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f2472,plain,
    ( spl5_130
  <=> k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) = k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f4734,plain,
    ( k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_112
    | ~ spl5_130 ),
    inference(forward_demodulation,[],[f2473,f2365])).

fof(f2473,plain,
    ( k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) = k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_130 ),
    inference(avatar_component_clause,[],[f2472])).

fof(f4731,plain,
    ( spl5_180
    | spl5_198
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f4730,f2343,f1811,f96,f4711,f3617])).

fof(f3617,plain,
    ( spl5_180
  <=> k1_funct_1(sK0,sK1(sK0)) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f1811,plain,
    ( spl5_66
  <=> k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f4730,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK1(sK0))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4729,f2344])).

fof(f4729,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK2(sK0))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4671,f115])).

fof(f4671,plain,
    ( k9_relat_1(sK0,k1_tarski(sK2(sK0))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0))))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106 ),
    inference(superposition,[],[f2619,f2333])).

fof(f2333,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k11_relat_1(sK0,sK1(sK0)))
        | k1_funct_1(sK0,sK1(sK0)) = X0 )
    | ~ spl5_66 ),
    inference(superposition,[],[f68,f1812])).

fof(f1812,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f2619,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X0)) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f2605,f116])).

fof(f2605,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0)) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f116,f2344])).

fof(f4728,plain,
    ( spl5_118
    | spl5_120
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f3942,f2371,f2403,f2397])).

fof(f2397,plain,
    ( spl5_118
  <=> r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f2403,plain,
    ( spl5_120
  <=> v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2371,plain,
    ( spl5_114
  <=> m1_subset_1(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f3942,plain,
    ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_114 ),
    inference(resolution,[],[f2372,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t2_subset)).

fof(f2372,plain,
    ( m1_subset_1(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_114 ),
    inference(avatar_component_clause,[],[f2371])).

fof(f4726,plain,
    ( spl5_62
    | spl5_118
    | spl5_120
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f4725,f2343,f96,f2403,f2397,f1795])).

fof(f1795,plain,
    ( spl5_62
  <=> ! [X1] : sK2(sK0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f4725,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4555,f2344])).

fof(f4555,plain,
    ( ! [X0] :
        ( r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK2(sK0))))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f612,f2344])).

fof(f612,plain,
    ( ! [X57,X56] :
        ( r2_hidden(k11_relat_1(sK0,X56),k1_zfmisc_1(k11_relat_1(sK0,X56)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X56)))
        | X56 = X57 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f611,f115])).

fof(f611,plain,
    ( ! [X57,X56] :
        ( r2_hidden(k11_relat_1(sK0,X56),k1_zfmisc_1(k11_relat_1(sK0,X56)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X56))))
        | X56 = X57 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f573,f115])).

fof(f573,plain,(
    ! [X57,X56] :
      ( r2_hidden(k9_relat_1(sK0,k1_tarski(X56)),k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X56))))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X56))))
      | X56 = X57 ) ),
    inference(superposition,[],[f106,f68])).

fof(f106,plain,(
    ! [X4,X3] :
      ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(X3,X4)),k1_zfmisc_1(k9_relat_1(sK0,X3)))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) ) ),
    inference(resolution,[],[f63,f99])).

fof(f4713,plain,
    ( spl5_198
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106
    | spl5_181 ),
    inference(avatar_split_clause,[],[f4706,f3614,f2343,f1811,f96,f4711])).

fof(f4706,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK1(sK0))
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106
    | ~ spl5_181 ),
    inference(forward_demodulation,[],[f4705,f2344])).

fof(f4705,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106
    | ~ spl5_181 ),
    inference(forward_demodulation,[],[f4704,f115])).

fof(f4704,plain,
    ( k9_relat_1(sK0,k1_tarski(sK2(sK0))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_106
    | ~ spl5_181 ),
    inference(subsumption_resolution,[],[f4671,f3615])).

fof(f4382,plain,
    ( spl5_178
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f4381,f2343,f96,f3536])).

fof(f3536,plain,
    ( spl5_178
  <=> k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f4381,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4380,f2344])).

fof(f4380,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4345,f127])).

fof(f4345,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f2619,f2643])).

fof(f2643,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK1(sK0)))) = k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK2(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f2630,f117])).

fof(f117,plain,
    ( ! [X2,X3] : k9_relat_1(sK0,k4_xboole_0(X3,k1_tarski(X2))) = k4_xboole_0(k9_relat_1(sK0,X3),k11_relat_1(sK0,X2))
    | ~ spl5_4 ),
    inference(superposition,[],[f73,f115])).

fof(f2630,plain,
    ( ! [X0] : k9_relat_1(sK0,k4_xboole_0(X0,k1_tarski(sK2(sK0)))) = k4_xboole_0(k9_relat_1(sK0,X0),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f117,f2344])).

fof(f4378,plain,
    ( spl5_178
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f4377,f2343,f96,f3536])).

fof(f4377,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4376,f2344])).

fof(f4376,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f4343,f127])).

fof(f4343,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f2643,f2619])).

fof(f4265,plain,
    ( spl5_50
    | spl5_176
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f4264,f2364,f96,f3404,f1749])).

fof(f1749,plain,
    ( spl5_50
  <=> ! [X52] : k1_funct_1(sK0,sK1(sK0)) = X52 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f4264,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
        | k1_funct_1(sK0,sK1(sK0)) = X1 )
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(superposition,[],[f608,f2365])).

fof(f608,plain,
    ( ! [X50,X51] :
        ( m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,X50)),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X50))))
        | X50 = X51 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f570,f115])).

fof(f570,plain,(
    ! [X50,X51] :
      ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k1_tarski(X50))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k1_tarski(X50)))))
      | X50 = X51 ) ),
    inference(superposition,[],[f100,f68])).

fof(f4182,plain,
    ( ~ spl5_171
    | ~ spl5_158 ),
    inference(avatar_split_clause,[],[f4179,f2785,f3258])).

fof(f3258,plain,
    ( spl5_171
  <=> ~ r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f2785,plain,
    ( spl5_158
  <=> r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f4179,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_158 ),
    inference(resolution,[],[f2786,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',antisymmetry_r2_hidden)).

fof(f2786,plain,
    ( r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_158 ),
    inference(avatar_component_clause,[],[f2785])).

fof(f4142,plain,
    ( ~ spl5_151
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f4139,f2669,f2728])).

fof(f2728,plain,
    ( spl5_151
  <=> ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f2669,plain,
    ( spl5_146
  <=> r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f4139,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_146 ),
    inference(resolution,[],[f2670,f62])).

fof(f2670,plain,
    ( r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_146 ),
    inference(avatar_component_clause,[],[f2669])).

fof(f4116,plain,
    ( spl5_146
    | spl5_133
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f4115,f2571,f2524,f2669])).

fof(f2524,plain,
    ( spl5_133
  <=> ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_133])])).

fof(f2571,plain,
    ( spl5_144
  <=> m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f4115,plain,
    ( r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_133
    | ~ spl5_144 ),
    inference(subsumption_resolution,[],[f4114,f2525])).

fof(f2525,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_133 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f4114,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_144 ),
    inference(resolution,[],[f2572,f63])).

fof(f2572,plain,
    ( m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_144 ),
    inference(avatar_component_clause,[],[f2571])).

fof(f4069,plain,
    ( spl5_50
    | spl5_144
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f4057,f2364,f96,f2571,f1749])).

fof(f4057,plain,
    ( ! [X5] :
        ( m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
        | k1_funct_1(sK0,sK1(sK0)) = X5 )
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(superposition,[],[f607,f2365])).

fof(f607,plain,
    ( ! [X48,X49] :
        ( m1_subset_1(k11_relat_1(sK0,X48),k1_zfmisc_1(k11_relat_1(sK0,X48)))
        | X48 = X49 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f569,f115])).

fof(f569,plain,(
    ! [X48,X49] :
      ( m1_subset_1(k9_relat_1(sK0,k1_tarski(X48)),k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X48))))
      | X48 = X49 ) ),
    inference(superposition,[],[f99,f68])).

fof(f4000,plain,
    ( ~ spl5_37
    | spl5_168
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3998,f1811,f96,f3073,f1714])).

fof(f1714,plain,
    ( spl5_37
  <=> ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f3073,plain,
    ( spl5_168
  <=> ! [X0] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f3998,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f307,f1812])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f285,f194])).

fof(f194,plain,(
    ! [X3] :
      ( ~ sP4(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f104,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f66,f76_D])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f76_D])).

fof(f76_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t5_subset)).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f63,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',existence_m1_subset_1)).

fof(f285,plain,
    ( ! [X21,X20] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X20),X21)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X20)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f118])).

fof(f118,plain,
    ( ! [X4,X5] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X4),X5)),k1_zfmisc_1(k11_relat_1(sK0,X4)))
    | ~ spl5_4 ),
    inference(superposition,[],[f99,f115])).

fof(f3993,plain,
    ( ~ spl5_37
    | spl5_160
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3991,f1811,f96,f2790,f1714])).

fof(f2790,plain,
    ( spl5_160
  <=> ! [X0] : sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f3991,plain,
    ( ! [X0] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f285,f1812])).

fof(f3986,plain,
    ( ~ spl5_59
    | spl5_168
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3984,f1811,f96,f3073,f1771])).

fof(f1771,plain,
    ( spl5_59
  <=> ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f3984,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f758,f1812])).

fof(f758,plain,
    ( ! [X6,X7] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X6),X7)))
        | ~ sP4(k11_relat_1(sK0,X6)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f493,f77])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f468,f115])).

fof(f468,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k9_relat_1(sK0,k4_xboole_0(X0,X1))),k9_relat_1(sK0,X0))
      | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f457,f287])).

fof(f287,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1)))
      | ~ v1_xboole_0(k9_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f277,f194])).

fof(f277,plain,(
    ! [X4,X3] :
      ( sP4(k9_relat_1(sK0,k4_xboole_0(X3,X4)))
      | ~ v1_xboole_0(k9_relat_1(sK0,X3)) ) ),
    inference(resolution,[],[f76,f99])).

fof(f457,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1)))
      | v1_xboole_0(k9_relat_1(sK0,X0))
      | r2_hidden(sK3(k9_relat_1(sK0,k4_xboole_0(X0,X1))),k9_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f434,f63])).

fof(f434,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(k9_relat_1(sK0,k4_xboole_0(X0,X1))),k9_relat_1(sK0,X0))
      | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) ) ),
    inference(resolution,[],[f424,f104])).

fof(f424,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK0,k4_xboole_0(X6,X7)))
      | m1_subset_1(X5,k9_relat_1(sK0,X6)) ) ),
    inference(resolution,[],[f67,f99])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t4_subset)).

fof(f3977,plain,
    ( ~ spl5_197
    | ~ spl5_184 ),
    inference(avatar_split_clause,[],[f3968,f3667,f3975])).

fof(f3975,plain,
    ( spl5_197
  <=> ~ r2_hidden(k11_relat_1(sK0,sK1(sK0)),sK3(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f3667,plain,
    ( spl5_184
  <=> r2_hidden(sK3(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f3968,plain,
    ( ~ r2_hidden(k11_relat_1(sK0,sK1(sK0)),sK3(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_184 ),
    inference(resolution,[],[f3668,f62])).

fof(f3668,plain,
    ( r2_hidden(sK3(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_184 ),
    inference(avatar_component_clause,[],[f3667])).

fof(f3939,plain,
    ( spl5_112
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3937,f1811,f96,f2364])).

fof(f3937,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f115,f1812])).

fof(f3938,plain,
    ( ~ spl5_111
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3936,f1811,f2357])).

fof(f3936,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_66 ),
    inference(superposition,[],[f75,f1812])).

fof(f75,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3907,plain,
    ( spl5_194
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3097,f2343,f96,f2756,f3905])).

fof(f3905,plain,
    ( spl5_194
  <=> ! [X0] : v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f2756,plain,
    ( spl5_157
  <=> ~ sP4(k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f3097,plain,
    ( ! [X0] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3095,f2344])).

fof(f3095,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)))
        | ~ sP4(k11_relat_1(sK0,sK2(sK0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f516,f2344])).

fof(f516,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f515,f115])).

fof(f515,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ sP4(k9_relat_1(sK0,k1_tarski(X0))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f484,f127])).

fof(f484,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X15,X16)))
      | ~ sP4(k9_relat_1(sK0,X15)) ) ),
    inference(resolution,[],[f468,f77])).

fof(f3903,plain,
    ( spl5_154
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3225,f2343,f96,f2756,f2750])).

fof(f2750,plain,
    ( spl5_154
  <=> ! [X1,X0] :
        ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0)) = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f3225,plain,
    ( ! [X0,X1] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f525,f2344])).

fof(f525,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP4(k11_relat_1(sK0,X0))
        | k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)) = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl5_4 ),
    inference(superposition,[],[f507,f115])).

fof(f507,plain,(
    ! [X17,X15,X16] :
      ( ~ sP4(k9_relat_1(sK0,X15))
      | k9_relat_1(sK0,k4_xboole_0(X15,X17)) = X16
      | ~ v1_xboole_0(X16) ) ),
    inference(resolution,[],[f484,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t8_boole)).

fof(f3902,plain,
    ( spl5_190
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3460,f2343,f96,f2756,f3895])).

fof(f3895,plain,
    ( spl5_190
  <=> ! [X19] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f3460,plain,
    ( ! [X6] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X6))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3428,f2344])).

fof(f3428,plain,
    ( ! [X6] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X6)))
        | ~ sP4(k11_relat_1(sK0,sK2(sK0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f758,f2619])).

fof(f3901,plain,
    ( spl5_62
    | spl5_192
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3461,f2343,f96,f2756,f3899,f1795])).

fof(f3899,plain,
    ( spl5_192
  <=> ! [X7] : sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f3461,plain,
    ( ! [X8,X7] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X7)))
        | sK2(sK0) = X8 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3429,f2344])).

fof(f3429,plain,
    ( ! [X8,X7] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X7)))
        | sK2(sK0) = X8
        | ~ sP4(k11_relat_1(sK0,sK2(sK0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f814,f2619])).

fof(f814,plain,
    ( ! [X2,X0,X1] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X2)))
        | X0 = X1
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f772,f516])).

fof(f772,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | X4 = X5
        | sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X4),X6))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f550,f76])).

fof(f550,plain,
    ( ! [X10,X11,X9] :
        ( m1_subset_1(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X9),X11)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X9),k11_relat_1(sK0,X10))))
        | X9 = X10 )
    | ~ spl5_4 ),
    inference(superposition,[],[f157,f68])).

fof(f157,plain,
    ( ! [X24,X23,X22] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X22),k1_tarski(X23)),X24)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X22),k11_relat_1(sK0,X23))))
    | ~ spl5_4 ),
    inference(superposition,[],[f99,f127])).

fof(f3897,plain,
    ( spl5_190
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3485,f2343,f96,f2756,f3895])).

fof(f3485,plain,
    ( ! [X19] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X19))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3484,f2344])).

fof(f3484,plain,
    ( ! [X19] :
        ( ~ sP4(k11_relat_1(sK0,sK2(sK0)))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X19))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3439,f115])).

fof(f3439,plain,
    ( ! [X19] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),X19)))
        | ~ sP4(k9_relat_1(sK0,k1_tarski(sK2(sK0)))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f484,f2619])).

fof(f3893,plain,
    ( spl5_188
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3584,f2343,f96,f2756,f3891])).

fof(f3891,plain,
    ( spl5_188
  <=> ! [X1,X0] :
        ( k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,X0)) = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f3584,plain,
    ( ! [X0,X1] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f517,f2344])).

fof(f517,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP4(k11_relat_1(sK0,X0))
        | k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X2)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f516,f72])).

fof(f3889,plain,
    ( spl5_186
    | spl5_156
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3596,f2343,f96,f2753,f3887])).

fof(f3887,plain,
    ( spl5_186
  <=> ! [X0] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)))
        | sK2(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f2753,plain,
    ( spl5_156
  <=> sP4(k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f3596,plain,
    ( ! [X0] :
        ( sP4(k11_relat_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3590,f2344])).

fof(f3590,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)))
        | sK2(sK0) = X0
        | sP4(k11_relat_1(sK0,sK2(sK0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f781,f2344])).

fof(f781,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X3),k11_relat_1(sK0,X4)))
        | X3 = X4
        | sP4(k11_relat_1(sK0,X3)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f779,f76])).

fof(f779,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k11_relat_1(sK0,X0),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))))
        | X0 = X1 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f778,f115])).

fof(f778,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | m1_subset_1(k9_relat_1(sK0,k1_tarski(X0)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))) )
    | ~ spl5_4 ),
    inference(condensation,[],[f774])).

fof(f774,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_relat_1(sK0,k1_tarski(X0)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X2))))
        | X0 = X2
        | X0 = X1 )
    | ~ spl5_4 ),
    inference(superposition,[],[f550,f68])).

fof(f3885,plain,
    ( ~ spl5_157
    | ~ spl5_4
    | spl5_183 ),
    inference(avatar_split_clause,[],[f3627,f3623,f96,f2756])).

fof(f3623,plain,
    ( spl5_183
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f3627,plain,
    ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_183 ),
    inference(resolution,[],[f3624,f758])).

fof(f3624,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_183 ),
    inference(avatar_component_clause,[],[f3623])).

fof(f3884,plain,
    ( ~ spl5_157
    | ~ spl5_4
    | spl5_183 ),
    inference(avatar_split_clause,[],[f3631,f3623,f96,f2756])).

fof(f3631,plain,
    ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_183 ),
    inference(forward_demodulation,[],[f3629,f115])).

fof(f3629,plain,
    ( ~ sP4(k9_relat_1(sK0,k1_tarski(sK1(sK0))))
    | ~ spl5_183 ),
    inference(resolution,[],[f3624,f484])).

fof(f3883,plain,
    ( spl5_62
    | spl5_184
    | spl5_156
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3661,f2343,f96,f2753,f3667,f1795])).

fof(f3661,plain,
    ( ! [X0] :
        ( sP4(k11_relat_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3659,f2344])).

fof(f3659,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
        | sK2(sK0) = X0
        | sP4(k11_relat_1(sK0,sK2(sK0))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f857,f2344])).

fof(f857,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X6)),k11_relat_1(sK0,X6))
        | X6 = X7
        | sP4(k11_relat_1(sK0,X6)) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f849])).

fof(f849,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X6)),k11_relat_1(sK0,X6))
        | X6 = X7
        | X6 = X7
        | sP4(k11_relat_1(sK0,X6)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f626,f781])).

fof(f626,plain,
    ( ! [X88,X89] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X88),k11_relat_1(sK0,X89)))
        | r2_hidden(sK3(k11_relat_1(sK0,X88)),k11_relat_1(sK0,X88))
        | X88 = X89 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f625,f127])).

fof(f625,plain,
    ( ! [X88,X89] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X88)),k11_relat_1(sK0,X88))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X88),k1_tarski(X89))))
        | X88 = X89 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f588,f115])).

fof(f588,plain,(
    ! [X88,X89] :
      ( r2_hidden(sK3(k9_relat_1(sK0,k1_tarski(X88))),k9_relat_1(sK0,k1_tarski(X88)))
      | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X88),k1_tarski(X89))))
      | X88 = X89 ) ),
    inference(superposition,[],[f468,f68])).

fof(f3881,plain,(
    ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f3880])).

fof(f3880,plain,
    ( $false
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f3781,f1796])).

fof(f1796,plain,
    ( ! [X1] : sK2(sK0) = X1
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f1795])).

fof(f3781,plain,
    ( ! [X0] : k1_tarski(X0) != sK2(sK0)
    | ~ spl5_62 ),
    inference(superposition,[],[f75,f1796])).

fof(f3879,plain,(
    ~ spl5_62 ),
    inference(avatar_contradiction_clause,[],[f3878])).

fof(f3878,plain,
    ( $false
    | ~ spl5_62 ),
    inference(subsumption_resolution,[],[f3770,f1796])).

fof(f3770,plain,
    ( k4_xboole_0(sK2(sK0),sK2(sK0)) != sK2(sK0)
    | ~ spl5_62 ),
    inference(superposition,[],[f75,f1796])).

fof(f3858,plain,
    ( ~ spl5_62
    | spl5_111 ),
    inference(avatar_contradiction_clause,[],[f3857])).

fof(f3857,plain,
    ( $false
    | ~ spl5_62
    | ~ spl5_111 ),
    inference(subsumption_resolution,[],[f3737,f1796])).

fof(f3737,plain,
    ( k4_xboole_0(sK2(sK0),sK2(sK0)) != sK2(sK0)
    | ~ spl5_62
    | ~ spl5_111 ),
    inference(backward_demodulation,[],[f1796,f2358])).

fof(f3832,plain,
    ( ~ spl5_62
    | ~ spl5_158 ),
    inference(avatar_contradiction_clause,[],[f3831])).

fof(f3831,plain,
    ( $false
    | ~ spl5_62
    | ~ spl5_158 ),
    inference(subsumption_resolution,[],[f3830,f62])).

fof(f3830,plain,
    ( r2_hidden(sK2(sK0),sK2(sK0))
    | ~ spl5_62
    | ~ spl5_158 ),
    inference(forward_demodulation,[],[f3705,f1796])).

fof(f3705,plain,
    ( r2_hidden(sK3(sK2(sK0)),sK2(sK0))
    | ~ spl5_62
    | ~ spl5_158 ),
    inference(backward_demodulation,[],[f1796,f2786])).

fof(f3827,plain,
    ( ~ spl5_62
    | ~ spl5_146 ),
    inference(avatar_contradiction_clause,[],[f3826])).

fof(f3826,plain,
    ( $false
    | ~ spl5_62
    | ~ spl5_146 ),
    inference(subsumption_resolution,[],[f3825,f62])).

fof(f3825,plain,
    ( r2_hidden(sK2(sK0),sK2(sK0))
    | ~ spl5_62
    | ~ spl5_146 ),
    inference(forward_demodulation,[],[f3702,f1796])).

fof(f3702,plain,
    ( r2_hidden(sK2(sK0),k1_zfmisc_1(sK2(sK0)))
    | ~ spl5_62
    | ~ spl5_146 ),
    inference(backward_demodulation,[],[f1796,f2670])).

fof(f3789,plain,
    ( ~ spl5_62
    | spl5_181 ),
    inference(avatar_contradiction_clause,[],[f3670])).

fof(f3670,plain,
    ( $false
    | ~ spl5_62
    | ~ spl5_181 ),
    inference(subsumption_resolution,[],[f3615,f1796])).

fof(f3669,plain,
    ( spl5_62
    | spl5_184
    | ~ spl5_4
    | ~ spl5_106
    | spl5_157 ),
    inference(avatar_split_clause,[],[f3662,f2756,f2343,f96,f3667,f1795])).

fof(f3662,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_157 ),
    inference(subsumption_resolution,[],[f3661,f2757])).

fof(f2757,plain,
    ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f3625,plain,
    ( spl5_180
    | ~ spl5_183
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | spl5_157 ),
    inference(avatar_split_clause,[],[f3612,f2756,f2364,f2343,f96,f3623,f3617])).

fof(f3612,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | ~ spl5_157 ),
    inference(forward_demodulation,[],[f3610,f116])).

fof(f3610,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | k1_funct_1(sK0,sK1(sK0)) = sK2(sK0)
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | ~ spl5_157 ),
    inference(superposition,[],[f3597,f2365])).

fof(f3597,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)))
        | sK2(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_157 ),
    inference(subsumption_resolution,[],[f3596,f2757])).

fof(f3542,plain,
    ( spl5_178
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3541,f2343,f96,f3536])).

fof(f3541,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3540,f2344])).

fof(f3540,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3517,f127])).

fof(f3517,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f2619,f2643])).

fof(f3538,plain,
    ( spl5_178
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3531,f2343,f96,f3536])).

fof(f3531,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3530,f2344])).

fof(f3530,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f3497,f127])).

fof(f3497,plain,
    ( k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0)))) = k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),k1_tarski(sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f2643,f2619])).

fof(f3406,plain,
    ( spl5_50
    | spl5_176
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f3399,f2364,f96,f3404,f1749])).

fof(f3399,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
        | k1_funct_1(sK0,sK1(sK0)) = X1 )
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(superposition,[],[f608,f2365])).

fof(f3384,plain,
    ( spl5_118
    | spl5_120
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f3035,f2371,f2403,f2397])).

fof(f3035,plain,
    ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_114 ),
    inference(resolution,[],[f2372,f63])).

fof(f3383,plain,
    ( ~ spl5_121
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2432,f2397,f2400])).

fof(f2400,plain,
    ( spl5_121
  <=> ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f2432,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_118 ),
    inference(resolution,[],[f2398,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t7_boole)).

fof(f2398,plain,
    ( r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_118 ),
    inference(avatar_component_clause,[],[f2397])).

fof(f3382,plain,
    ( spl5_174
    | spl5_120
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2590,f2343,f96,f2403,f3378])).

fof(f3378,plain,
    ( spl5_174
  <=> ! [X3] : r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X3)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f2590,plain,
    ( ! [X3] :
        ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X3)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(resolution,[],[f2424,f63])).

fof(f2424,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f118,f2344])).

fof(f3381,plain,
    ( ~ spl5_121
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f3043,f2397,f2400])).

fof(f3043,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_118 ),
    inference(resolution,[],[f2398,f71])).

fof(f3380,plain,
    ( spl5_174
    | spl5_120
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f3115,f2343,f96,f2403,f3378])).

fof(f3115,plain,
    ( ! [X3] :
        ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X3)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(resolution,[],[f2424,f63])).

fof(f3376,plain,
    ( spl5_172
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | spl5_121 ),
    inference(avatar_split_clause,[],[f3369,f2400,f2364,f2343,f96,f3374])).

fof(f3374,plain,
    ( spl5_172
  <=> r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f3369,plain,
    ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | ~ spl5_121 ),
    inference(forward_demodulation,[],[f3367,f116])).

fof(f3367,plain,
    ( r2_hidden(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_112
    | ~ spl5_121 ),
    inference(superposition,[],[f3332,f2365])).

fof(f3332,plain,
    ( ! [X40] : r2_hidden(k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,X40)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121 ),
    inference(forward_demodulation,[],[f3303,f2344])).

fof(f3303,plain,
    ( ! [X40] : r2_hidden(k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,X40)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121 ),
    inference(superposition,[],[f2592,f127])).

fof(f2592,plain,
    ( ! [X3] : r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X3)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f2590,f2401])).

fof(f2401,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_121 ),
    inference(avatar_component_clause,[],[f2400])).

fof(f3260,plain,
    ( ~ spl5_171
    | ~ spl5_158 ),
    inference(avatar_split_clause,[],[f3251,f2785,f3258])).

fof(f3251,plain,
    ( ~ r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_158 ),
    inference(resolution,[],[f2786,f62])).

fof(f3215,plain,
    ( ~ spl5_151
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f3212,f2669,f2728])).

fof(f3212,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_146 ),
    inference(resolution,[],[f2670,f62])).

fof(f3203,plain,
    ( spl5_146
    | spl5_133
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f3202,f2571,f2524,f2669])).

fof(f3202,plain,
    ( r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_133
    | ~ spl5_144 ),
    inference(subsumption_resolution,[],[f3201,f2525])).

fof(f3201,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_144 ),
    inference(resolution,[],[f2572,f63])).

fof(f3107,plain,
    ( spl5_50
    | spl5_144
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f3104,f2364,f96,f2571,f1749])).

fof(f3104,plain,
    ( ! [X3] :
        ( m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
        | k1_funct_1(sK0,sK1(sK0)) = X3 )
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(superposition,[],[f607,f2365])).

fof(f3086,plain,
    ( ~ spl5_37
    | spl5_168
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3084,f1811,f96,f3073,f1714])).

fof(f3084,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f307,f1812])).

fof(f3080,plain,
    ( ~ spl5_37
    | spl5_160
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3078,f1811,f96,f2790,f1714])).

fof(f3078,plain,
    ( ! [X0] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f285,f1812])).

fof(f3075,plain,
    ( ~ spl5_59
    | spl5_168
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3070,f1811,f96,f3073,f1771])).

fof(f3070,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f758,f1812])).

fof(f3045,plain,
    ( ~ spl5_127
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f3042,f2397,f2438])).

fof(f2438,plain,
    ( spl5_127
  <=> ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f3042,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_118 ),
    inference(resolution,[],[f2398,f62])).

fof(f3037,plain,
    ( spl5_118
    | ~ spl5_114
    | spl5_121 ),
    inference(avatar_split_clause,[],[f3036,f2400,f2371,f2397])).

fof(f3036,plain,
    ( r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_114
    | ~ spl5_121 ),
    inference(subsumption_resolution,[],[f3035,f2401])).

fof(f3031,plain,
    ( spl5_112
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3029,f1811,f96,f2364])).

fof(f3029,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f115,f1812])).

fof(f3030,plain,
    ( ~ spl5_111
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f3028,f1811,f2357])).

fof(f3028,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_66 ),
    inference(superposition,[],[f75,f1812])).

fof(f3010,plain,(
    ~ spl5_122 ),
    inference(avatar_contradiction_clause,[],[f3009])).

fof(f3009,plain,
    ( $false
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2906,f2411])).

fof(f2411,plain,
    ( ! [X0] : sK1(sK0) = X0
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f2410])).

fof(f2410,plain,
    ( spl5_122
  <=> ! [X0] : sK1(sK0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f2906,plain,
    ( ! [X0] : k1_tarski(X0) != sK1(sK0)
    | ~ spl5_122 ),
    inference(superposition,[],[f75,f2411])).

fof(f3008,plain,(
    ~ spl5_122 ),
    inference(avatar_contradiction_clause,[],[f3007])).

fof(f3007,plain,
    ( $false
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2898,f2411])).

fof(f2898,plain,
    ( k4_xboole_0(sK1(sK0),sK1(sK0)) != sK1(sK0)
    | ~ spl5_122 ),
    inference(superposition,[],[f75,f2411])).

fof(f2992,plain,
    ( ~ spl5_118
    | ~ spl5_122 ),
    inference(avatar_contradiction_clause,[],[f2991])).

fof(f2991,plain,
    ( $false
    | ~ spl5_118
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2990,f62])).

fof(f2990,plain,
    ( r2_hidden(sK1(sK0),sK1(sK0))
    | ~ spl5_118
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2863,f2411])).

fof(f2863,plain,
    ( r2_hidden(sK1(sK0),k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_118
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f2398])).

fof(f2988,plain,
    ( spl5_111
    | ~ spl5_122 ),
    inference(avatar_contradiction_clause,[],[f2987])).

fof(f2987,plain,
    ( $false
    | ~ spl5_111
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2861,f2411])).

fof(f2861,plain,
    ( k4_xboole_0(sK1(sK0),sK1(sK0)) != sK1(sK0)
    | ~ spl5_111
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f2358])).

fof(f2981,plain,
    ( ~ spl5_4
    | ~ spl5_106
    | spl5_121
    | ~ spl5_122 ),
    inference(avatar_contradiction_clause,[],[f2980])).

fof(f2980,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2979,f62])).

fof(f2979,plain,
    ( r2_hidden(sK1(sK0),sK1(sK0))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2848,f2411])).

fof(f2848,plain,
    ( r2_hidden(sK1(sK0),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_4
    | ~ spl5_106
    | ~ spl5_121
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f2592])).

fof(f2969,plain,
    ( ~ spl5_122
    | ~ spl5_146 ),
    inference(avatar_contradiction_clause,[],[f2968])).

fof(f2968,plain,
    ( $false
    | ~ spl5_122
    | ~ spl5_146 ),
    inference(subsumption_resolution,[],[f2967,f62])).

fof(f2967,plain,
    ( r2_hidden(sK1(sK0),sK1(sK0))
    | ~ spl5_122
    | ~ spl5_146 ),
    inference(forward_demodulation,[],[f2835,f2411])).

fof(f2835,plain,
    ( r2_hidden(sK1(sK0),k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_122
    | ~ spl5_146 ),
    inference(backward_demodulation,[],[f2411,f2670])).

fof(f2966,plain,
    ( spl5_162
    | ~ spl5_122
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f2965,f2571,f2410,f2917])).

fof(f2917,plain,
    ( spl5_162
  <=> m1_subset_1(sK1(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f2965,plain,
    ( m1_subset_1(sK1(sK0),sK1(sK0))
    | ~ spl5_122
    | ~ spl5_144 ),
    inference(forward_demodulation,[],[f2834,f2411])).

fof(f2834,plain,
    ( m1_subset_1(sK1(sK0),k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_122
    | ~ spl5_144 ),
    inference(backward_demodulation,[],[f2411,f2572])).

fof(f2964,plain,
    ( ~ spl5_165
    | ~ spl5_122
    | spl5_133 ),
    inference(avatar_split_clause,[],[f2963,f2524,f2410,f2928])).

fof(f2928,plain,
    ( spl5_165
  <=> ~ v1_xboole_0(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f2963,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_133 ),
    inference(forward_demodulation,[],[f2833,f2411])).

fof(f2833,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_122
    | ~ spl5_133 ),
    inference(backward_demodulation,[],[f2411,f2525])).

fof(f2962,plain,
    ( ~ spl5_165
    | ~ spl5_122
    | spl5_125 ),
    inference(avatar_split_clause,[],[f2832,f2413,f2410,f2928])).

fof(f2413,plain,
    ( spl5_125
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f2832,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_125 ),
    inference(backward_demodulation,[],[f2411,f2414])).

fof(f2414,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_125 ),
    inference(avatar_component_clause,[],[f2413])).

fof(f2961,plain,
    ( ~ spl5_167
    | ~ spl5_122
    | spl5_141 ),
    inference(avatar_split_clause,[],[f2830,f2555,f2410,f2938])).

fof(f2938,plain,
    ( spl5_167
  <=> ~ sP4(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f2555,plain,
    ( spl5_141
  <=> ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_141])])).

fof(f2830,plain,
    ( ~ sP4(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_141 ),
    inference(backward_demodulation,[],[f2411,f2556])).

fof(f2556,plain,
    ( ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_141 ),
    inference(avatar_component_clause,[],[f2555])).

fof(f2960,plain,
    ( ~ spl5_165
    | ~ spl5_122
    | spl5_139 ),
    inference(avatar_split_clause,[],[f2829,f2548,f2410,f2928])).

fof(f2548,plain,
    ( spl5_139
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_139])])).

fof(f2829,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_139 ),
    inference(backward_demodulation,[],[f2411,f2549])).

fof(f2549,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_139 ),
    inference(avatar_component_clause,[],[f2548])).

fof(f2959,plain,
    ( ~ spl5_165
    | ~ spl5_122
    | spl5_135 ),
    inference(avatar_split_clause,[],[f2958,f2534,f2410,f2928])).

fof(f2534,plain,
    ( spl5_135
  <=> ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_135])])).

fof(f2958,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_135 ),
    inference(forward_demodulation,[],[f2828,f2411])).

fof(f2828,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_122
    | ~ spl5_135 ),
    inference(backward_demodulation,[],[f2411,f2535])).

fof(f2535,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_135 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f2957,plain,
    ( ~ spl5_165
    | ~ spl5_122
    | spl5_137 ),
    inference(avatar_split_clause,[],[f2827,f2541,f2410,f2928])).

fof(f2541,plain,
    ( spl5_137
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f2827,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_137 ),
    inference(backward_demodulation,[],[f2411,f2542])).

fof(f2542,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_137 ),
    inference(avatar_component_clause,[],[f2541])).

fof(f2956,plain,
    ( ~ spl5_167
    | ~ spl5_122
    | spl5_143 ),
    inference(avatar_split_clause,[],[f2826,f2562,f2410,f2938])).

fof(f2562,plain,
    ( spl5_143
  <=> ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f2826,plain,
    ( ~ sP4(sK1(sK0))
    | ~ spl5_122
    | ~ spl5_143 ),
    inference(backward_demodulation,[],[f2411,f2563])).

fof(f2563,plain,
    ( ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f2562])).

fof(f2946,plain,
    ( ~ spl5_165
    | spl5_166
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2945,f2410,f2941,f2928])).

fof(f2941,plain,
    ( spl5_166
  <=> sP4(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f2945,plain,
    ( sP4(sK1(sK0))
    | ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2944,f2411])).

fof(f2944,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(sK1(sK0))
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6)))) )
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2818,f2411])).

fof(f2818,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,sK1(sK0)))
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6)))) )
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f278])).

fof(f278,plain,(
    ! [X6,X5] :
      ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6))))
      | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,X5))) ) ),
    inference(resolution,[],[f76,f100])).

fof(f2943,plain,
    ( ~ spl5_165
    | spl5_166
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2936,f2410,f2941,f2928])).

fof(f2936,plain,
    ( sP4(sK1(sK0))
    | ~ v1_xboole_0(sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2817,f2411])).

fof(f2817,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(sK1(sK0))
        | sP4(k9_relat_1(sK0,k4_xboole_0(X3,X4))) )
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f277])).

fof(f2933,plain,
    ( spl5_164
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2926,f2410,f2931])).

fof(f2931,plain,
    ( spl5_164
  <=> v1_xboole_0(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f2926,plain,
    ( v1_xboole_0(sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2925,f2411])).

fof(f2925,plain,
    ( ! [X3] : v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3)))
    | ~ spl5_122 ),
    inference(subsumption_resolution,[],[f2924,f62])).

fof(f2924,plain,
    ( ! [X3] :
        ( r2_hidden(sK1(sK0),sK1(sK0))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) )
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2923,f2411])).

fof(f2923,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(X3,X4)),sK1(sK0))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) )
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2814,f2411])).

fof(f2814,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(X3,X4)),k1_zfmisc_1(sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) )
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f106])).

fof(f2922,plain,
    ( spl5_162
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2921,f2410,f2917])).

fof(f2921,plain,
    ( m1_subset_1(sK1(sK0),sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2920,f2411])).

fof(f2920,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))),sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2813,f2411])).

fof(f2813,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))),k1_zfmisc_1(k9_relat_1(sK0,sK1(sK0))))
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f100])).

fof(f2919,plain,
    ( spl5_162
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f2912,f2410,f2917])).

fof(f2912,plain,
    ( m1_subset_1(sK1(sK0),sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2911,f2411])).

fof(f2911,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(X0,X1)),sK1(sK0))
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f2812,f2411])).

fof(f2812,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k4_xboole_0(X0,X1)),k1_zfmisc_1(sK1(sK0)))
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2411,f99])).

fof(f2809,plain,
    ( ~ spl5_117
    | spl5_59
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2808,f2364,f1771,f2384])).

fof(f2384,plain,
    ( spl5_117
  <=> ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f2808,plain,
    ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_59
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1772,f2365])).

fof(f1772,plain,
    ( ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f2807,plain,
    ( spl5_158
    | ~ spl5_60
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2806,f2364,f1779,f2785])).

fof(f1779,plain,
    ( spl5_60
  <=> r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2806,plain,
    ( r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_60
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1780,f2365])).

fof(f1780,plain,
    ( r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f2805,plain,
    ( ~ spl5_117
    | spl5_65
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2804,f2343,f1798,f2384])).

fof(f1798,plain,
    ( spl5_65
  <=> ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f2804,plain,
    ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_65
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1799,f2344])).

fof(f1799,plain,
    ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f2803,plain,
    ( spl5_160
    | ~ spl5_38
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2802,f2343,f1717,f2790])).

fof(f1717,plain,
    ( spl5_38
  <=> ! [X22] : sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X22))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f2802,plain,
    ( ! [X22] : sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X22)))
    | ~ spl5_38
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1718,f2344])).

fof(f1718,plain,
    ( ! [X22] : sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X22)))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f2800,plain,
    ( spl5_116
    | ~ spl5_58
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2799,f2364,f1768,f2381])).

fof(f2381,plain,
    ( spl5_116
  <=> sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f1768,plain,
    ( spl5_58
  <=> sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2799,plain,
    ( sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_58
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1769,f2365])).

fof(f1769,plain,
    ( sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f2798,plain,
    ( ~ spl5_159
    | spl5_61
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2797,f2364,f1776,f2782])).

fof(f2782,plain,
    ( spl5_159
  <=> ~ r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f1776,plain,
    ( spl5_61
  <=> ~ r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f2797,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_61
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1777,f2365])).

fof(f1777,plain,
    ( ~ r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f2796,plain,
    ( spl5_116
    | ~ spl5_64
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2795,f2343,f1801,f2381])).

fof(f1801,plain,
    ( spl5_64
  <=> sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2795,plain,
    ( sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_64
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1802,f2344])).

fof(f1802,plain,
    ( sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f1801])).

fof(f2792,plain,
    ( spl5_50
    | spl5_160
    | ~ spl5_117
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2776,f2364,f1811,f96,f2384,f2790,f1749])).

fof(f2776,plain,
    ( ! [X0,X1] :
        ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
        | sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | k1_funct_1(sK0,sK1(sK0)) = X1 )
    | ~ spl5_4
    | ~ spl5_66
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f2773,f2365])).

fof(f2773,plain,
    ( ! [X0,X1] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X0)))
        | k1_funct_1(sK0,sK1(sK0)) = X1
        | ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f814,f1812])).

fof(f2787,plain,
    ( spl5_158
    | ~ spl5_60
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2780,f2364,f1779,f2785])).

fof(f2780,plain,
    ( r2_hidden(sK3(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_60
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1780,f2365])).

fof(f2758,plain,
    ( spl5_154
    | ~ spl5_157
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2747,f2343,f96,f2756,f2750])).

fof(f2747,plain,
    ( ! [X0,X1] :
        ( ~ sP4(k11_relat_1(sK0,sK1(sK0)))
        | k9_relat_1(sK0,k4_xboole_0(k1_tarski(sK2(sK0)),X0)) = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_4
    | ~ spl5_106 ),
    inference(superposition,[],[f525,f2344])).

fof(f2737,plain,
    ( ~ spl5_153
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f2723,f2669,f2735])).

fof(f2735,plain,
    ( spl5_153
  <=> ~ sP4(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f2723,plain,
    ( ~ sP4(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_146 ),
    inference(resolution,[],[f2670,f77])).

fof(f2730,plain,
    ( ~ spl5_151
    | ~ spl5_146 ),
    inference(avatar_split_clause,[],[f2721,f2669,f2728])).

fof(f2721,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_146 ),
    inference(resolution,[],[f2670,f62])).

fof(f2712,plain,
    ( ~ spl5_133
    | spl5_17
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2711,f2364,f1663,f2524])).

fof(f1663,plain,
    ( spl5_17
  <=> ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f2711,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_17
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1664,f2365])).

fof(f1664,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f2706,plain,
    ( spl5_148
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f2696,f2527,f2704])).

fof(f2704,plain,
    ( spl5_148
  <=> k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f2527,plain,
    ( spl5_132
  <=> v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f2696,plain,
    ( k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = sK3(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_132 ),
    inference(resolution,[],[f2683,f2528])).

fof(f2528,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f2527])).

fof(f2683,plain,
    ( ! [X12] :
        ( ~ v1_xboole_0(X12)
        | k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = sK3(k1_zfmisc_1(X12)) )
    | ~ spl5_132 ),
    inference(resolution,[],[f2675,f384])).

fof(f384,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f275,f194])).

fof(f275,plain,(
    ! [X0] :
      ( sP4(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f65])).

fof(f2675,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) = X0 )
    | ~ spl5_132 ),
    inference(resolution,[],[f2528,f72])).

fof(f2674,plain,
    ( spl5_132
    | ~ spl5_16
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2673,f2364,f1666,f2527])).

fof(f1666,plain,
    ( spl5_16
  <=> v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f2673,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_16
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1667,f2365])).

fof(f1667,plain,
    ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f1666])).

fof(f2672,plain,
    ( spl5_146
    | spl5_132
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f2663,f2571,f2527,f2669])).

fof(f2663,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_144 ),
    inference(resolution,[],[f2572,f63])).

fof(f2671,plain,
    ( spl5_146
    | spl5_133
    | ~ spl5_144 ),
    inference(avatar_split_clause,[],[f2664,f2571,f2524,f2669])).

fof(f2664,plain,
    ( r2_hidden(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_133
    | ~ spl5_144 ),
    inference(subsumption_resolution,[],[f2663,f2525])).

fof(f2646,plain,
    ( ~ spl5_111
    | spl5_13
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2645,f2343,f1652,f2357])).

fof(f1652,plain,
    ( spl5_13
  <=> k11_relat_1(sK0,sK2(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f2645,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_13
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1653,f2344])).

fof(f1653,plain,
    ( k11_relat_1(sK0,sK2(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK2(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1652])).

fof(f2579,plain,
    ( ~ spl5_133
    | spl5_17
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2578,f2364,f1663,f2524])).

fof(f2578,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_17
    | ~ spl5_112 ),
    inference(forward_demodulation,[],[f1664,f2365])).

fof(f2573,plain,
    ( spl5_50
    | spl5_144
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2521,f2364,f96,f2571,f1749])).

fof(f2521,plain,
    ( ! [X5] :
        ( m1_subset_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
        | k1_funct_1(sK0,sK1(sK0)) = X5 )
    | ~ spl5_4
    | ~ spl5_112 ),
    inference(superposition,[],[f607,f2365])).

fof(f2564,plain,
    ( ~ spl5_143
    | spl5_49
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2513,f2364,f1745,f2562])).

fof(f1745,plain,
    ( spl5_49
  <=> ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2513,plain,
    ( ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_49
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1746])).

fof(f1746,plain,
    ( ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f1745])).

fof(f2557,plain,
    ( ~ spl5_141
    | spl5_47
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2512,f2364,f1738,f2555])).

fof(f1738,plain,
    ( spl5_47
  <=> ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f2512,plain,
    ( ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_47
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1739])).

fof(f1739,plain,
    ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f1738])).

fof(f2550,plain,
    ( ~ spl5_139
    | spl5_33
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2510,f2364,f1704,f2548])).

fof(f1704,plain,
    ( spl5_33
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f2510,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_33
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1705])).

fof(f1705,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f1704])).

fof(f2543,plain,
    ( ~ spl5_137
    | spl5_29
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2509,f2364,f1694,f2541])).

fof(f1694,plain,
    ( spl5_29
  <=> ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f2509,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_29
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1695])).

fof(f1695,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f1694])).

fof(f2536,plain,
    ( ~ spl5_135
    | spl5_21
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2508,f2364,f1673,f2534])).

fof(f1673,plain,
    ( spl5_21
  <=> ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f2508,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))))
    | ~ spl5_21
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1674])).

fof(f1674,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f1673])).

fof(f2529,plain,
    ( spl5_132
    | ~ spl5_16
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2507,f2364,f1666,f2527])).

fof(f2507,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))))
    | ~ spl5_16
    | ~ spl5_112 ),
    inference(backward_demodulation,[],[f2365,f1667])).

fof(f2506,plain,
    ( spl5_112
    | ~ spl5_14
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2505,f2343,f1659,f2364])).

fof(f1659,plain,
    ( spl5_14
  <=> k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f2505,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_14
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1660,f2344])).

fof(f1660,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f1659])).

fof(f2474,plain,
    ( spl5_130
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f2465,f1676,f1666,f2472])).

fof(f1676,plain,
    ( spl5_20
  <=> v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f2465,plain,
    ( k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) = k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(resolution,[],[f1783,f1677])).

fof(f1677,plain,
    ( v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f1783,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) = X0 )
    | ~ spl5_16 ),
    inference(resolution,[],[f1667,f72])).

fof(f2447,plain,
    ( ~ spl5_129
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2433,f2397,f2445])).

fof(f2445,plain,
    ( spl5_129
  <=> ~ sP4(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_129])])).

fof(f2433,plain,
    ( ~ sP4(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_118 ),
    inference(resolution,[],[f2398,f77])).

fof(f2440,plain,
    ( ~ spl5_127
    | ~ spl5_118 ),
    inference(avatar_split_clause,[],[f2431,f2397,f2438])).

fof(f2431,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_118 ),
    inference(resolution,[],[f2398,f62])).

fof(f2418,plain,
    ( spl5_122
    | spl5_124
    | ~ spl5_4
    | ~ spl5_40
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2408,f2343,f1721,f96,f2416,f2410])).

fof(f2416,plain,
    ( spl5_124
  <=> v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1721,plain,
    ( spl5_40
  <=> ! [X27] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f2408,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
        | sK1(sK0) = X0 )
    | ~ spl5_4
    | ~ spl5_40
    | ~ spl5_106 ),
    inference(superposition,[],[f2406,f591])).

fof(f2406,plain,
    ( ! [X27] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),X27)))
    | ~ spl5_40
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1722,f2344])).

fof(f1722,plain,
    ( ! [X27] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X27)))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f1721])).

fof(f2405,plain,
    ( spl5_118
    | spl5_120
    | ~ spl5_114 ),
    inference(avatar_split_clause,[],[f2392,f2371,f2403,f2397])).

fof(f2392,plain,
    ( v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | r2_hidden(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_114 ),
    inference(resolution,[],[f2372,f63])).

fof(f2389,plain,
    ( spl5_114
    | ~ spl5_52
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2388,f2343,f1755,f2371])).

fof(f1755,plain,
    ( spl5_52
  <=> m1_subset_1(k11_relat_1(sK0,sK2(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK2(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f2388,plain,
    ( m1_subset_1(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_52
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1756,f2344])).

fof(f1756,plain,
    ( m1_subset_1(k11_relat_1(sK0,sK2(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK2(sK0))))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f2386,plain,
    ( ~ spl5_117
    | spl5_65
    | ~ spl5_106 ),
    inference(avatar_split_clause,[],[f2375,f2343,f1798,f2384])).

fof(f2375,plain,
    ( ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))))
    | ~ spl5_65
    | ~ spl5_106 ),
    inference(backward_demodulation,[],[f2344,f1799])).

fof(f2373,plain,
    ( spl5_50
    | spl5_114
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2338,f1811,f2371,f1749])).

fof(f2338,plain,
    ( ! [X2] :
        ( m1_subset_1(k11_relat_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK1(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X2 )
    | ~ spl5_66 ),
    inference(superposition,[],[f568,f1812])).

fof(f568,plain,(
    ! [X47,X46] :
      ( m1_subset_1(k1_tarski(X46),k1_zfmisc_1(k1_tarski(X46)))
      | X46 = X47 ) ),
    inference(superposition,[],[f74,f68])).

fof(f2366,plain,
    ( spl5_112
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2337,f1811,f96,f2364])).

fof(f2337,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK1(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_66 ),
    inference(superposition,[],[f115,f1812])).

fof(f2359,plain,
    ( ~ spl5_111
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2336,f1811,f2357])).

fof(f2336,plain,
    ( k11_relat_1(sK0,sK1(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_66 ),
    inference(superposition,[],[f75,f1812])).

fof(f2352,plain,
    ( ~ spl5_109
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2335,f1811,f2350])).

fof(f2350,plain,
    ( spl5_109
  <=> ~ v1_xboole_0(k11_relat_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f2335,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK1(sK0)))
    | ~ spl5_66 ),
    inference(superposition,[],[f70,f1812])).

fof(f70,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',fc2_xboole_0)).

fof(f2345,plain,
    ( spl5_106
    | ~ spl5_8
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2332,f1811,f1572,f2343])).

fof(f1572,plain,
    ( spl5_8
  <=> k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f2332,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0))
    | ~ spl5_8
    | ~ spl5_66 ),
    inference(backward_demodulation,[],[f1812,f1573])).

fof(f1573,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f1572])).

fof(f2331,plain,
    ( spl5_50
    | spl5_52
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f2328,f1572,f1755,f1749])).

fof(f2328,plain,
    ( ! [X2] :
        ( m1_subset_1(k11_relat_1(sK0,sK2(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK2(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X2 )
    | ~ spl5_8 ),
    inference(superposition,[],[f568,f1573])).

fof(f2330,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f2327,f1572,f96,f1659])).

fof(f2327,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f115,f1573])).

fof(f2329,plain,
    ( ~ spl5_13
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f2326,f1572,f1652])).

fof(f2326,plain,
    ( k11_relat_1(sK0,sK2(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK2(sK0)))
    | ~ spl5_8 ),
    inference(superposition,[],[f75,f1573])).

fof(f2305,plain,(
    ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f2304])).

fof(f2304,plain,
    ( $false
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2007,f1750])).

fof(f1750,plain,
    ( ! [X52] : k1_funct_1(sK0,sK1(sK0)) = X52
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f2007,plain,
    ( ! [X0] : k1_tarski(X0) != k1_funct_1(sK0,sK1(sK0))
    | ~ spl5_50 ),
    inference(superposition,[],[f75,f1750])).

fof(f2297,plain,(
    ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f2296])).

fof(f2296,plain,
    ( $false
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f1979,f1750])).

fof(f1979,plain,
    ( k1_funct_1(sK0,sK1(sK0)) != k4_xboole_0(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(superposition,[],[f75,f1750])).

fof(f2295,plain,
    ( ~ spl5_71
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1978,f1749,f2041])).

fof(f2041,plain,
    ( spl5_71
  <=> ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f1978,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(superposition,[],[f70,f1750])).

fof(f2294,plain,
    ( spl5_104
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1975,f1749,f96,f2041,f2276])).

fof(f2276,plain,
    ( spl5_104
  <=> ! [X3,X4] :
        ( X3 = X4
        | sP4(k11_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1975,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X0 = X1
        | sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(superposition,[],[f628,f1750])).

fof(f628,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,X3))
        | X3 = X4
        | sP4(k11_relat_1(sK0,X3)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f607,f76])).

fof(f2293,plain,
    ( spl5_76
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1969,f1749,f2095])).

fof(f2095,plain,
    ( spl5_76
  <=> ! [X25,X26] : X25 = X26 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1969,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl5_50 ),
    inference(superposition,[],[f1750,f1750])).

fof(f2285,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2284,f1749,f96,f2207,f2044])).

fof(f2044,plain,
    ( spl5_70
  <=> v1_xboole_0(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f2207,plain,
    ( spl5_96
  <=> ! [X3,X4] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X3))
        | X3 = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f2284,plain,
    ( ! [X6,X4] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X4))
        | v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X4 = X6 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1961,f1750])).

fof(f1961,plain,
    ( ! [X6,X4] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,X4)),k11_relat_1(sK0,X4))
        | X4 = X6 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1151])).

fof(f1151,plain,
    ( ! [X6,X4,X5] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | r2_hidden(sK3(k11_relat_1(sK0,X4)),k11_relat_1(sK0,X4))
        | X4 = X6 )
    | ~ spl5_4 ),
    inference(resolution,[],[f1116,f194])).

fof(f1116,plain,
    ( ! [X2,X0,X1] :
        ( sP4(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X2)))
        | r2_hidden(sK3(k11_relat_1(sK0,X0)),k11_relat_1(sK0,X0))
        | X0 = X1 )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f1110])).

fof(f1110,plain,
    ( ! [X2,X0,X1] :
        ( X0 = X1
        | sP4(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X2)))
        | r2_hidden(sK3(k11_relat_1(sK0,X0)),k11_relat_1(sK0,X0))
        | X0 = X1 )
    | ~ spl5_4 ),
    inference(resolution,[],[f1095,f626])).

fof(f1095,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | X4 = X5
        | sP4(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X6))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f775,f76])).

fof(f775,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X2))))
        | X0 = X2 )
    | ~ spl5_4 ),
    inference(superposition,[],[f550,f127])).

fof(f2283,plain,
    ( spl5_74
    | spl5_96
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2282,f1749,f96,f2207,f2063])).

fof(f2063,plain,
    ( spl5_74
  <=> sP4(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f2282,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))
        | sP4(k1_funct_1(sK0,sK1(sK0)))
        | X0 = X1 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1960,f1750])).

fof(f1960,plain,
    ( ! [X0,X1] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,X0)),k11_relat_1(sK0,X0))
        | X0 = X1 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1116])).

fof(f2281,plain,
    ( spl5_76
    | ~ spl5_71
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2280,f1749,f96,f2063,f2041,f2095])).

fof(f2280,plain,
    ( ! [X4,X5] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X4 = X5 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1959,f1750])).

fof(f1959,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X4 = X5
        | sP4(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X6))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1095])).

fof(f2279,plain,
    ( spl5_94
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1958,f1749,f96,f2063,f2202])).

fof(f2202,plain,
    ( spl5_94
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ sP4(k11_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f1958,plain,
    ( ! [X2,X0] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | X0 = X2
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f824])).

fof(f824,plain,
    ( ! [X2,X0,X1] :
        ( sP4(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | X0 = X2
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(superposition,[],[f814,f127])).

fof(f2278,plain,
    ( spl5_104
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1957,f1749,f96,f2041,f2276])).

fof(f1957,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4
        | sP4(k11_relat_1(sK0,X3)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f781])).

fof(f2269,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2268,f1749,f96,f2207,f2044])).

fof(f2268,plain,
    ( ! [X88,X89] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X88))
        | v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X88 = X89 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1953,f1750])).

fof(f1953,plain,
    ( ! [X88,X89] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,X88)),k11_relat_1(sK0,X88))
        | X88 = X89 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f626])).

fof(f2267,plain,
    ( spl5_92
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1951,f1749,f96,f2044,f2195])).

fof(f2195,plain,
    ( spl5_92
  <=> ! [X6] : ~ sP4(k11_relat_1(sK0,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1951,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f516])).

fof(f2266,plain,
    ( spl5_90
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2265,f1749,f96,f2044,f2185])).

fof(f2185,plain,
    ( spl5_90
  <=> ! [X0] : r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f2265,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2264,f1750])).

fof(f2264,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1950,f1750])).

fof(f1950,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_funct_1(sK0,sK1(sK0))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f503])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f502,f127])).

fof(f502,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f492,f115])).

fof(f492,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k9_relat_1(sK0,k1_tarski(X0)))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f468,f127])).

fof(f2263,plain,
    ( spl5_88
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2262,f1749,f96,f2044,f2179])).

fof(f2179,plain,
    ( spl5_88
  <=> ! [X0] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f2262,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2261,f1750])).

fof(f2261,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1949,f1750])).

fof(f1949,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k1_funct_1(sK0,sK1(sK0))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f477])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f476,f127])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f465,f115])).

fof(f465,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1))),k9_relat_1(sK0,k1_tarski(X0)))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f434,f127])).

fof(f2260,plain,
    ( spl5_86
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1946,f1749,f96,f2044,f2172])).

fof(f2172,plain,
    ( spl5_86
  <=> ! [X20] : ~ v1_xboole_0(k11_relat_1(sK0,X20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1946,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f306])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f305,f115])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ v1_xboole_0(k9_relat_1(sK0,k1_tarski(X0))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f287,f127])).

fof(f2259,plain,
    ( spl5_86
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1945,f1749,f96,f2063,f2172])).

fof(f1945,plain,
    ( ! [X0] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f296])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( sP4(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f295,f115])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( sP4(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)))
        | ~ v1_xboole_0(k9_relat_1(sK0,k1_tarski(X0))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f277,f127])).

fof(f2258,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2257,f1749,f96,f2027,f2095])).

fof(f2027,plain,
    ( spl5_68
  <=> m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f2257,plain,
    ( ! [X2,X0] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X0 = X2 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1943,f1750])).

fof(f1943,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_xboole_0(k11_relat_1(sK0,X0),k11_relat_1(sK0,X1)),k1_funct_1(sK0,sK1(sK0)))
        | X0 = X2 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f775])).

fof(f2256,plain,
    ( spl5_102
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2252,f1749,f96,f2044,f2254])).

fof(f2254,plain,
    ( spl5_102
  <=> ! [X60,X61] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X60))
        | X60 = X61 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f2252,plain,
    ( ! [X61,X60] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X60))
        | X60 = X61 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1942,f1750])).

fof(f1942,plain,
    ( ! [X61,X60] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X60))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X60)))
        | X60 = X61 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f616])).

fof(f616,plain,
    ( ! [X61,X60] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X60)),k11_relat_1(sK0,X60))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X60)))
        | X60 = X61 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f615,f115])).

fof(f615,plain,
    ( ! [X61,X60] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X60)),k11_relat_1(sK0,X60))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X60))))
        | X60 = X61 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f575,f115])).

fof(f575,plain,(
    ! [X61,X60] :
      ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X60))),k9_relat_1(sK0,k1_tarski(X60)))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X60))))
      | X60 = X61 ) ),
    inference(superposition,[],[f111,f68])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,X2)),k9_relat_1(sK0,k4_xboole_0(X2,X3)))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X2))) ) ),
    inference(resolution,[],[f106,f62])).

fof(f2251,plain,
    ( spl5_100
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2247,f1749,f96,f2044,f2249])).

fof(f2249,plain,
    ( spl5_100
  <=> ! [X56,X57] :
        ( r2_hidden(k11_relat_1(sK0,X56),k1_funct_1(sK0,sK1(sK0)))
        | X56 = X57 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f2247,plain,
    ( ! [X57,X56] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(k11_relat_1(sK0,X56),k1_funct_1(sK0,sK1(sK0)))
        | X56 = X57 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1941,f1750])).

fof(f1941,plain,
    ( ! [X57,X56] :
        ( r2_hidden(k11_relat_1(sK0,X56),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X56)))
        | X56 = X57 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f612])).

fof(f2246,plain,
    ( spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2245,f1749,f96,f2044])).

fof(f2245,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2244,f1750])).

fof(f2244,plain,
    ( ! [X6] : v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X6)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2243,f62])).

fof(f2243,plain,
    ( ! [X6] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X6))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1939,f1750])).

fof(f1939,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_xboole_0(k11_relat_1(sK0,X6),k11_relat_1(sK0,X7)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X6))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f169])).

fof(f169,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_xboole_0(k11_relat_1(sK0,X6),k11_relat_1(sK0,X7)),k1_zfmisc_1(k11_relat_1(sK0,X6)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X6))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f168,f115])).

fof(f168,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_xboole_0(k11_relat_1(sK0,X6),k11_relat_1(sK0,X7)),k1_zfmisc_1(k11_relat_1(sK0,X6)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X6)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f150,f115])).

fof(f150,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_xboole_0(k11_relat_1(sK0,X6),k11_relat_1(sK0,X7)),k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X6))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X6)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f106,f127])).

fof(f2242,plain,
    ( ~ spl5_73
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2241,f1749,f96,f2055])).

fof(f2055,plain,
    ( spl5_73
  <=> ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2241,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2240,f71])).

fof(f2240,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2239,f1750])).

fof(f2239,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X4))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1938,f1750])).

fof(f1938,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X4))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f167])).

fof(f167,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X4)),k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X4))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f166,f115])).

fof(f166,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X4)),k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X4)))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f149,f115])).

fof(f149,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X4))),k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X4)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f111,f127])).

fof(f2236,plain,
    ( ~ spl5_75
    | ~ spl5_50
    | spl5_59 ),
    inference(avatar_split_clause,[],[f1935,f1771,f1749,f2060])).

fof(f2060,plain,
    ( spl5_75
  <=> ~ sP4(k1_funct_1(sK0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f1935,plain,
    ( ~ sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50
    | ~ spl5_59 ),
    inference(backward_demodulation,[],[f1750,f1772])).

fof(f2235,plain,
    ( ~ spl5_71
    | spl5_37
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1934,f1749,f1714,f2041])).

fof(f1934,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_37
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1715])).

fof(f1715,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f2234,plain,
    ( spl5_70
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2233,f1749,f1666,f2044])).

fof(f2233,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1933,f1750])).

fof(f1933,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_16
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1667])).

fof(f2232,plain,
    ( ~ spl5_71
    | spl5_11
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1931,f1749,f1645,f2041])).

fof(f1645,plain,
    ( spl5_11
  <=> ~ v1_xboole_0(k11_relat_1(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1931,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_11
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1646])).

fof(f1646,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK2(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f1645])).

fof(f2231,plain,
    ( spl5_70
    | spl5_80
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2230,f1749,f2145,f2044])).

fof(f2145,plain,
    ( spl5_80
  <=> ! [X0] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f2230,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0))
        | v1_xboole_0(k1_funct_1(sK0,sK1(sK0))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1909,f1750])).

fof(f1909,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | m1_subset_1(sK3(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(X0,X1),X2))),k9_relat_1(sK0,X0)) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f478])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(X0,X1),X2))),k9_relat_1(sK0,X0))
      | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ) ),
    inference(resolution,[],[f468,f424])).

fof(f2229,plain,
    ( spl5_98
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1906,f1749,f96,f2044,f2226])).

fof(f2226,plain,
    ( spl5_98
  <=> ! [X5,X4] :
        ( ~ v1_xboole_0(k11_relat_1(sK0,X4))
        | X4 = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f1906,plain,
    ( ! [X12,X11] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X11 = X12
        | ~ v1_xboole_0(k11_relat_1(sK0,X11)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f729])).

fof(f729,plain,
    ( ! [X12,X13,X11] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X11),k1_tarski(X12)),X13)))
        | X11 = X12
        | ~ v1_xboole_0(k11_relat_1(sK0,X11)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f717,f194])).

fof(f717,plain,
    ( ! [X6,X4,X5] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X4),k1_tarski(X5)),X6)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X4))
        | X4 = X5 )
    | ~ spl5_4 ),
    inference(resolution,[],[f632,f76])).

fof(f632,plain,
    ( ! [X6,X8,X7] :
        ( m1_subset_1(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X6),k1_tarski(X7)),X8)),k1_zfmisc_1(k11_relat_1(sK0,X6)))
        | X6 = X7 )
    | ~ spl5_4 ),
    inference(superposition,[],[f157,f591])).

fof(f2228,plain,
    ( spl5_98
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1905,f1749,f96,f2063,f2226])).

fof(f1905,plain,
    ( ! [X4,X5] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X4))
        | X4 = X5 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f717])).

fof(f2224,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2223,f1749,f96,f2027,f2095])).

fof(f2223,plain,
    ( ! [X6,X7] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X6 = X7 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1903,f1750])).

fof(f1903,plain,
    ( ! [X6,X7] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,X6)))
        | X6 = X7 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f632])).

fof(f2220,plain,
    ( spl5_74
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2219,f1749,f96,f2041,f2063])).

fof(f2219,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1899,f1750])).

fof(f1899,plain,
    ( ! [X23,X22] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X22),k11_relat_1(sK0,X23))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f286])).

fof(f286,plain,
    ( ! [X24,X23,X22] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X22),k1_tarski(X23)),X24)))
        | ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X22),k11_relat_1(sK0,X23))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f157])).

fof(f2218,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2217,f1749,f96,f2027])).

fof(f2217,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1898,f1750])).

fof(f1898,plain,
    ( ! [X23,X22] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X22),k11_relat_1(sK0,X23))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f157])).

fof(f2213,plain,
    ( spl5_70
    | spl5_96
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2212,f1749,f96,f2207,f2044])).

fof(f2212,plain,
    ( ! [X20,X18] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X18))
        | v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X18 = X20 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1894,f1750])).

fof(f1894,plain,
    ( ! [X20,X18] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,X18)),k11_relat_1(sK0,X18))
        | X18 = X20 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f871])).

fof(f871,plain,
    ( ! [X19,X20,X18] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X18)),k11_relat_1(sK0,X18))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X18),X19)))
        | X18 = X20 )
    | ~ spl5_4 ),
    inference(resolution,[],[f858,f194])).

fof(f858,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X3)),k11_relat_1(sK0,X3))
        | sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X3),X5)))
        | X3 = X4 )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f848])).

fof(f848,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(sK3(k11_relat_1(sK0,X3)),k11_relat_1(sK0,X3))
        | X3 = X4
        | X3 = X4
        | sP4(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X3),X5))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f626,f772])).

fof(f2209,plain,
    ( spl5_74
    | spl5_96
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2205,f1749,f96,f2207,f2063])).

fof(f2205,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X3))
        | sP4(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1892,f1750])).

fof(f1892,plain,
    ( ! [X4,X3] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(sK3(k11_relat_1(sK0,X3)),k11_relat_1(sK0,X3))
        | X3 = X4 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f858])).

fof(f2204,plain,
    ( spl5_94
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1891,f1749,f96,f2063,f2202])).

fof(f1891,plain,
    ( ! [X0,X1] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | X0 = X1
        | ~ sP4(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f814])).

fof(f2200,plain,
    ( spl5_76
    | spl5_74
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2199,f1749,f96,f2041,f2063,f2095])).

fof(f2199,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | sP4(k1_funct_1(sK0,sK1(sK0)))
        | X4 = X5 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1890,f1750])).

fof(f1890,plain,
    ( ! [X4,X5] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k4_xboole_0(k11_relat_1(sK0,X4),k11_relat_1(sK0,X5)))
        | X4 = X5 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f772])).

fof(f2197,plain,
    ( spl5_92
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1888,f1749,f96,f2044,f2195])).

fof(f1888,plain,
    ( ! [X6] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ sP4(k11_relat_1(sK0,X6)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f758])).

fof(f2190,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2189,f1749,f96,f2027,f2095])).

fof(f2189,plain,
    ( ! [X10,X9] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X9 = X10 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1885,f1750])).

fof(f1885,plain,
    ( ! [X10,X9] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k4_xboole_0(k11_relat_1(sK0,X9),k11_relat_1(sK0,X10))))
        | X9 = X10 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f550])).

fof(f2187,plain,
    ( spl5_90
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2183,f1749,f96,f2044,f2185])).

fof(f2183,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2182,f1750])).

fof(f2182,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1882,f1750])).

fof(f1882,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_funct_1(sK0,sK1(sK0))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f493])).

fof(f2181,plain,
    ( spl5_88
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2177,f1749,f96,f2044,f2179])).

fof(f2177,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2176,f1750])).

fof(f2176,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1881,f1750])).

fof(f1881,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k1_funct_1(sK0,sK1(sK0))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f444])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))),k11_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f432,f104])).

fof(f432,plain,
    ( ! [X30,X31,X32] :
        ( ~ r2_hidden(X30,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X31),X32)))
        | m1_subset_1(X30,k11_relat_1(sK0,X31)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f118])).

fof(f2175,plain,
    ( spl5_86
    | spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1878,f1749,f96,f2044,f2172])).

fof(f1878,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f307])).

fof(f2174,plain,
    ( spl5_86
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1877,f1749,f96,f2063,f2172])).

fof(f1877,plain,
    ( ! [X20] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k11_relat_1(sK0,X20)) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f285])).

fof(f2170,plain,
    ( ~ spl5_73
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2169,f1749,f96,f2055])).

fof(f2169,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2168,f71])).

fof(f2168,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2167,f1750])).

fof(f2167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X0))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1876,f1750])).

fof(f1876,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X0))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X0)),k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X0))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f141,f115])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,X0)),k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X0)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f111,f115])).

fof(f2166,plain,
    ( spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2165,f1749,f96,f2044])).

fof(f2165,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2164,f1750])).

fof(f2164,plain,
    ( ! [X12] : v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X12)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2163,f62])).

fof(f2163,plain,
    ( ! [X12] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X12))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1875,f1750])).

fof(f1875,plain,
    ( ! [X12] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,X12)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X12))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f123])).

fof(f123,plain,
    ( ! [X12,X13] :
        ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X12),X13)),k1_zfmisc_1(k11_relat_1(sK0,X12)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,X12))) )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f122,f115])).

fof(f122,plain,
    ( ! [X12,X13] :
        ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(k1_tarski(X12),X13)),k1_zfmisc_1(k11_relat_1(sK0,X12)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k1_tarski(X12)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f106,f115])).

fof(f2162,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2161,f1749,f96,f2027])).

fof(f2161,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1874,f1750])).

fof(f1874,plain,
    ( ! [X4] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k11_relat_1(sK0,X4)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f118])).

fof(f2160,plain,
    ( spl5_84
    | spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1871,f1749,f2044,f2158])).

fof(f2158,plain,
    ( spl5_84
  <=> ! [X15] : ~ sP4(k9_relat_1(sK0,X15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f1871,plain,
    ( ! [X15] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ sP4(k9_relat_1(sK0,X15)) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f484])).

fof(f2153,plain,
    ( spl5_82
    | spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2149,f1749,f2044,f2151])).

fof(f2151,plain,
    ( spl5_82
  <=> ! [X0] : r2_hidden(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f2149,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | r2_hidden(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0)) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2148,f1750])).

fof(f2148,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1869,f1750])).

fof(f1869,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k1_funct_1(sK0,sK1(sK0))),k9_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f468])).

fof(f2147,plain,
    ( spl5_80
    | spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2143,f1749,f2044,f2145])).

fof(f2143,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0)) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2142,f1750])).

fof(f2142,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k9_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1868,f1750])).

fof(f1868,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3(k1_funct_1(sK0,sK1(sK0))),k9_relat_1(sK0,X0))
        | v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(X0,X1))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f434])).

fof(f2141,plain,
    ( spl5_78
    | spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1865,f1749,f2044,f2138])).

fof(f2138,plain,
    ( spl5_78
  <=> ! [X3] : ~ v1_xboole_0(k9_relat_1(sK0,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1865,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k9_relat_1(sK0,X0)) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f287])).

fof(f2140,plain,
    ( spl5_78
    | spl5_74
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1864,f1749,f2063,f2138])).

fof(f1864,plain,
    ( ! [X3] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k9_relat_1(sK0,X3)) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f277])).

fof(f2136,plain,
    ( ~ spl5_73
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2135,f1749,f2055])).

fof(f2135,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2134,f71])).

fof(f2134,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2133,f1750])).

fof(f2133,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X2))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1863,f1750])).

fof(f1863,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,X2)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X2))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f111])).

fof(f2132,plain,
    ( spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2131,f1749,f2044])).

fof(f2131,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2130,f1750])).

fof(f2130,plain,
    ( ! [X3] : v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3)))
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2129,f62])).

fof(f2129,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1862,f1750])).

fof(f1862,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,X3)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,X3))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f106])).

fof(f2128,plain,
    ( spl5_68
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2127,f1749,f2027])).

fof(f2127,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1861,f1750])).

fof(f1861,plain,
    ( ! [X0] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,X0)))
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f99])).

fof(f2126,plain,
    ( ~ spl5_75
    | spl5_47
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1859,f1749,f1738,f2060])).

fof(f1859,plain,
    ( ~ sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_47
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1739])).

fof(f2125,plain,
    ( ~ spl5_71
    | spl5_33
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f1858,f1749,f1704,f2041])).

fof(f1858,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_33
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f1705])).

fof(f2124,plain,
    ( spl5_76
    | ~ spl5_71
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2123,f1749,f96,f2063,f2041,f2095])).

fof(f2123,plain,
    ( ! [X4,X3] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1857,f1750])).

fof(f1857,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4
        | sP4(k9_relat_1(sK0,k11_relat_1(sK0,X3))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f668])).

fof(f668,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,X3)))
        | X3 = X4
        | sP4(k9_relat_1(sK0,k11_relat_1(sK0,X3))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f608,f76])).

fof(f2122,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2121,f1749,f96,f2027,f2095])).

fof(f2121,plain,
    ( ! [X50,X51] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X50 = X51 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1856,f1750])).

fof(f1856,plain,
    ( ! [X50,X51] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))))
        | X50 = X51 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f608])).

fof(f2118,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2117,f1749,f96,f2027])).

fof(f2117,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1851,f1750])).

fof(f1851,plain,
    ( ! [X26,X25] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,X25),k11_relat_1(sK0,X26)))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f158])).

fof(f158,plain,
    ( ! [X26,X27,X25] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X25),k1_tarski(X26)),X27))),k1_zfmisc_1(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,X25),k11_relat_1(sK0,X26)))))
    | ~ spl5_4 ),
    inference(superposition,[],[f100,f127])).

fof(f2116,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2115,f1749,f96,f2027,f2095])).

fof(f2115,plain,
    ( ! [X10,X9] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X9 = X10 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1850,f1750])).

fof(f1850,plain,
    ( ! [X10,X9] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X9))))
        | X9 = X10 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f633])).

fof(f633,plain,
    ( ! [X10,X11,X9] :
        ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k1_tarski(X9),k1_tarski(X10)),X11))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X9))))
        | X9 = X10 )
    | ~ spl5_4 ),
    inference(superposition,[],[f158,f591])).

fof(f2111,plain,
    ( spl5_74
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2110,f1749,f96,f2041,f2063])).

fof(f2110,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1844,f1750])).

fof(f1844,plain,
    ( ! [X15] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,X15))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f283])).

fof(f283,plain,
    ( ! [X15,X16] :
        ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X15),X16))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,X15))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f119])).

fof(f119,plain,
    ( ! [X6,X7] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X6),X7))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X6))))
    | ~ spl5_4 ),
    inference(superposition,[],[f100,f115])).

fof(f2109,plain,
    ( ~ spl5_73
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2108,f1749,f96,f2055])).

fof(f2108,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2107,f71])).

fof(f2107,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2106,f1750])).

fof(f2106,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X2)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1843,f1750])).

fof(f1843,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X2))),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X2)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f143])).

fof(f143,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X2))),k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X2),X3))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X2)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f111,f116])).

fof(f2105,plain,
    ( spl5_70
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2104,f1749,f96,f2044])).

fof(f2104,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2103,f1750])).

fof(f2103,plain,
    ( ! [X0] : v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2102,f62])).

fof(f2102,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1842,f1750])).

fof(f1842,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X0)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f106,f116])).

fof(f2101,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2100,f1749,f96,f2027])).

fof(f2100,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1841,f1750])).

fof(f1841,plain,
    ( ! [X6] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,X6))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f119])).

fof(f2099,plain,
    ( spl5_76
    | ~ spl5_71
    | spl5_74
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2098,f1749,f96,f2063,f2041,f2095])).

fof(f2098,plain,
    ( ! [X4,X3] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1840,f1750])).

fof(f1840,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | X3 = X4
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X3)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f845])).

fof(f845,plain,
    ( ! [X4,X3] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X3))))
        | X3 = X4
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X3)))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f597,f76])).

fof(f597,plain,
    ( ! [X26,X25] :
        ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X25))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X25)))))
        | X25 = X26 )
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f558,f115])).

fof(f558,plain,
    ( ! [X26,X25] :
        ( m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k1_tarski(X25)))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X25)))))
        | X25 = X26 )
    | ~ spl5_4 ),
    inference(superposition,[],[f131,f68])).

fof(f2097,plain,
    ( spl5_76
    | spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2093,f1749,f96,f2027,f2095])).

fof(f2093,plain,
    ( ! [X26,X25] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | X25 = X26 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1839,f1750])).

fof(f1839,plain,
    ( ! [X26,X25] :
        ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))))
        | X25 = X26 )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f597])).

fof(f2092,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2091,f1749,f96,f2027])).

fof(f2091,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1838,f1750])).

fof(f1838,plain,
    ( ! [X6] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X6)))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f131])).

fof(f2090,plain,
    ( spl5_74
    | ~ spl5_71
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2089,f1749,f96,f2041,f2063])).

fof(f2089,plain,
    ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1837,f1750])).

fof(f1837,plain,
    ( ! [X13] :
        ( sP4(k1_funct_1(sK0,sK1(sK0)))
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X13)))) )
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f282])).

fof(f282,plain,
    ( ! [X14,X13] :
        ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X13),X14)))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X13)))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f131])).

fof(f2085,plain,
    ( spl5_68
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2084,f1749,f96,f2027])).

fof(f2084,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1833,f1750])).

fof(f1833,plain,
    ( ! [X4] : m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X4))))))
    | ~ spl5_4
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f130])).

fof(f130,plain,
    ( ! [X4,X5] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X4),X5))))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X4))))))
    | ~ spl5_4 ),
    inference(superposition,[],[f101,f116])).

fof(f2068,plain,
    ( ~ spl5_71
    | spl5_74
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2067,f1749,f2063,f2041])).

fof(f2067,plain,
    ( sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2066,f1750])).

fof(f2066,plain,
    ( ! [X8,X7] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X7,X8))))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1820,f1750])).

fof(f1820,plain,
    ( ! [X8,X7] :
        ( ~ v1_xboole_0(k9_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X7,X8))))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f279])).

fof(f279,plain,(
    ! [X8,X7] :
      ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X7,X8)))))
      | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,X7)))) ) ),
    inference(resolution,[],[f76,f101])).

fof(f2065,plain,
    ( ~ spl5_71
    | spl5_74
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2058,f1749,f2063,f2041])).

fof(f2058,plain,
    ( sP4(k1_funct_1(sK0,sK1(sK0)))
    | ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1819,f1750])).

fof(f1819,plain,
    ( ! [X6,X5] :
        ( ~ v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
        | sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6)))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f278])).

fof(f2057,plain,
    ( ~ spl5_73
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2050,f1749,f2055])).

fof(f2050,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2049,f71])).

fof(f2049,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2048,f1750])).

fof(f2048,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0)))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2047,f1750])).

fof(f2047,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0)))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1818,f1750])).

fof(f1818,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))),k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0)))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0))),k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X0)))) ) ),
    inference(superposition,[],[f111,f73])).

fof(f2046,plain,
    ( spl5_70
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2039,f1749,f2044])).

fof(f2039,plain,
    ( v1_xboole_0(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2038,f1750])).

fof(f2038,plain,
    ( ! [X5] : v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5))))
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f2037,f62])).

fof(f2037,plain,
    ( ! [X5] :
        ( r2_hidden(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5)))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2036,f1750])).

fof(f2036,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6))),k1_funct_1(sK0,sK1(sK0)))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5)))) )
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1817,f1750])).

fof(f1817,plain,
    ( ! [X6,X5] :
        ( r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6))),k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5)))) )
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f107])).

fof(f107,plain,(
    ! [X6,X5] :
      ( r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X5,X6))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5))))
      | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,X5)))) ) ),
    inference(resolution,[],[f63,f100])).

fof(f2035,plain,
    ( spl5_68
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2034,f1749,f2027])).

fof(f2034,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2033,f1750])).

fof(f2033,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1816,f1750])).

fof(f1816,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f102])).

fof(f102,plain,(
    ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))),k1_zfmisc_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,X0)))))) ),
    inference(superposition,[],[f101,f73])).

fof(f2032,plain,
    ( spl5_68
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2031,f1749,f2027])).

fof(f2031,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2030,f1750])).

fof(f2030,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1)))),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1815,f1750])).

fof(f1815,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1)))),k1_zfmisc_1(k9_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f101])).

fof(f2029,plain,
    ( spl5_68
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2022,f1749,f2027])).

fof(f2022,plain,
    ( m1_subset_1(k1_funct_1(sK0,sK1(sK0)),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f2021,f1750])).

fof(f2021,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))),k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_50 ),
    inference(forward_demodulation,[],[f1814,f1750])).

fof(f1814,plain,
    ( ! [X0,X1] : m1_subset_1(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))),k1_zfmisc_1(k1_funct_1(sK0,sK1(sK0))))
    | ~ spl5_50 ),
    inference(backward_demodulation,[],[f1750,f100])).

fof(f1813,plain,
    ( spl5_66
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1806,f96,f89,f82,f1811])).

fof(f1806,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1805,f83])).

fof(f1805,plain,
    ( k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | v2_funct_1(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1804,f97])).

fof(f1804,plain,
    ( ~ v1_relat_1(sK0)
    | k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | v2_funct_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f687,f90])).

fof(f687,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k11_relat_1(X0,sK1(X0)) = k1_tarski(k1_funct_1(X0,sK1(X0)))
      | v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f683])).

fof(f683,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k11_relat_1(X0,sK1(X0)) = k1_tarski(k1_funct_1(X0,sK1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t124_funct_1.p',t117_funct_1)).

fof(f1803,plain,
    ( spl5_62
    | spl5_64
    | ~ spl5_4
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1790,f1717,f96,f1801,f1795])).

fof(f1790,plain,
    ( ! [X1] :
        ( sP4(k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))))
        | sK2(sK0) = X1 )
    | ~ spl5_4
    | ~ spl5_38 ),
    inference(superposition,[],[f1718,f591])).

fof(f1793,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1788,f1717,f1721])).

fof(f1788,plain,
    ( ! [X18] : v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X18)))
    | ~ spl5_38 ),
    inference(resolution,[],[f1718,f194])).

fof(f1782,plain,
    ( spl5_50
    | spl5_60
    | spl5_40
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1640,f1572,f96,f1721,f1779,f1749])).

fof(f1640,plain,
    ( ! [X105,X104] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X104)))
        | r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X105 )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f871,f1573])).

fof(f1781,plain,
    ( spl5_50
    | spl5_60
    | spl5_38
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1639,f1572,f96,f1717,f1779,f1749])).

fof(f1639,plain,
    ( ! [X103,X102] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X102)))
        | r2_hidden(sK3(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X103 )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f858,f1573])).

fof(f1774,plain,
    ( ~ spl5_59
    | spl5_50
    | spl5_38
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1638,f1572,f96,f1717,f1749,f1771])).

fof(f1638,plain,
    ( ! [X101,X100] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X100)))
        | k1_funct_1(sK0,sK1(sK0)) = X101
        | ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f814,f1573])).

fof(f1773,plain,
    ( ~ spl5_59
    | spl5_40
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1636,f1572,f96,f1721,f1771])).

fof(f1636,plain,
    ( ! [X96] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X96)))
        | ~ sP4(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f758,f1573])).

fof(f1766,plain,
    ( ~ spl5_37
    | spl5_56
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1635,f1572,f96,f1764,f1714])).

fof(f1764,plain,
    ( spl5_56
  <=> ! [X95,X94] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k1_tarski(X94)),X95)))
        | k1_funct_1(sK0,sK1(sK0)) = X94 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1635,plain,
    ( ! [X94,X95] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k1_tarski(X94)),X95)))
        | k1_funct_1(sK0,sK1(sK0)) = X94
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f729,f1573])).

fof(f1762,plain,
    ( ~ spl5_37
    | spl5_54
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1632,f1572,f96,f1760,f1714])).

fof(f1760,plain,
    ( spl5_54
  <=> ! [X89,X88] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k1_tarski(X88)),X89)))
        | k1_funct_1(sK0,sK1(sK0)) = X88 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1632,plain,
    ( ! [X88,X89] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k1_tarski(X88)),X89)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X88 )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f717,f1573])).

fof(f1757,plain,
    ( spl5_50
    | spl5_52
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1614,f1572,f1755,f1749])).

fof(f1614,plain,
    ( ! [X52] :
        ( m1_subset_1(k11_relat_1(sK0,sK2(sK0)),k1_zfmisc_1(k11_relat_1(sK0,sK2(sK0))))
        | k1_funct_1(sK0,sK1(sK0)) = X52 )
    | ~ spl5_8 ),
    inference(superposition,[],[f568,f1573])).

fof(f1747,plain,
    ( ~ spl5_49
    | spl5_44
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1612,f1572,f96,f1729,f1745])).

fof(f1729,plain,
    ( spl5_44
  <=> ! [X33] : v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X33))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1612,plain,
    ( ! [X49] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X49)))))
        | ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f533,f1573])).

fof(f533,plain,
    ( ! [X2,X3] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X2),X3)))))
        | ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X2)))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f508,f116])).

fof(f508,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(X0,X1))))
      | ~ sP4(k9_relat_1(sK0,k9_relat_1(sK0,X0))) ) ),
    inference(superposition,[],[f484,f73])).

fof(f1740,plain,
    ( ~ spl5_47
    | spl5_42
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1611,f1572,f96,f1725,f1738])).

fof(f1725,plain,
    ( spl5_42
  <=> ! [X28] : v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X28)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1611,plain,
    ( ! [X48] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X48))))
        | ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f509,f1573])).

fof(f509,plain,
    ( ! [X2,X3] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X2),X3))))
        | ~ sP4(k9_relat_1(sK0,k11_relat_1(sK0,X2))) )
    | ~ spl5_4 ),
    inference(superposition,[],[f484,f116])).

fof(f1731,plain,
    ( ~ spl5_29
    | spl5_44
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1603,f1572,f96,f1729,f1694])).

fof(f1603,plain,
    ( ! [X33] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X33)))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f420,f1573])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1)))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,X0)))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f282,f194])).

fof(f1727,plain,
    ( ~ spl5_33
    | spl5_42
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1600,f1572,f96,f1725,f1704])).

fof(f1600,plain,
    ( ! [X28] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X28))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f348,f1573])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k1_tarski(X0),X1))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,X0))) )
    | ~ spl5_4 ),
    inference(resolution,[],[f283,f194])).

fof(f1723,plain,
    ( ~ spl5_37
    | spl5_40
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1599,f1572,f96,f1721,f1714])).

fof(f1599,plain,
    ( ! [X27] :
        ( v1_xboole_0(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X27)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f307,f1573])).

fof(f1719,plain,
    ( ~ spl5_37
    | spl5_38
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1596,f1572,f96,f1717,f1714])).

fof(f1596,plain,
    ( ! [X22] :
        ( sP4(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X22)))
        | ~ v1_xboole_0(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f285,f1573])).

fof(f1709,plain,
    ( ~ spl5_33
    | spl5_34
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1595,f1572,f96,f1707,f1704])).

fof(f1707,plain,
    ( spl5_34
  <=> ! [X21] : sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X21)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1595,plain,
    ( ! [X21] :
        ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X21))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f283,f1573])).

fof(f1699,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1594,f1572,f96,f1697,f1694])).

fof(f1697,plain,
    ( spl5_30
  <=> ! [X20] : sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X20))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1594,plain,
    ( ! [X20] :
        ( sP4(k9_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X20)))))
        | ~ v1_xboole_0(k9_relat_1(sK0,k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f282,f1573])).

fof(f1689,plain,
    ( spl5_16
    | spl5_26
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1589,f1572,f96,f1687,f1666])).

fof(f1687,plain,
    ( spl5_26
  <=> ! [X11] : ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1589,plain,
    ( ! [X11] :
        ( ~ r2_hidden(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))),k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X11)))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f145,f1573])).

fof(f1685,plain,
    ( spl5_20
    | spl5_24
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1588,f1572,f96,f1683,f1676])).

fof(f1683,plain,
    ( spl5_24
  <=> ! [X10] : ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))),k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1588,plain,
    ( ! [X10] :
        ( ~ r2_hidden(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))),k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X10))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f143,f1573])).

fof(f1681,plain,
    ( spl5_20
    | spl5_22
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1585,f1572,f96,f1679,f1676])).

fof(f1679,plain,
    ( spl5_22
  <=> ! [X7] : r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X7))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1585,plain,
    ( ! [X7] :
        ( r2_hidden(k9_relat_1(sK0,k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X7))),k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))))
        | v1_xboole_0(k1_zfmisc_1(k9_relat_1(sK0,k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f128,f1573])).

fof(f1671,plain,
    ( spl5_16
    | spl5_18
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1582,f1572,f96,f1669,f1666])).

fof(f1669,plain,
    ( spl5_18
  <=> ! [X4] : r2_hidden(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X4)),k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1582,plain,
    ( ! [X4] :
        ( r2_hidden(k9_relat_1(sK0,k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),X4)),k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))))
        | v1_xboole_0(k1_zfmisc_1(k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0))))) )
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f123,f1573])).

fof(f1661,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1579,f1572,f96,f1659])).

fof(f1579,plain,
    ( k9_relat_1(sK0,k11_relat_1(sK0,sK2(sK0))) = k11_relat_1(sK0,k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f115,f1573])).

fof(f1654,plain,
    ( ~ spl5_13
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1578,f1572,f1652])).

fof(f1578,plain,
    ( k11_relat_1(sK0,sK2(sK0)) != k4_xboole_0(k11_relat_1(sK0,sK2(sK0)),k11_relat_1(sK0,sK2(sK0)))
    | ~ spl5_8 ),
    inference(superposition,[],[f75,f1573])).

fof(f1647,plain,
    ( ~ spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1577,f1572,f1645])).

fof(f1577,plain,
    ( ~ v1_xboole_0(k11_relat_1(sK0,sK2(sK0)))
    | ~ spl5_8 ),
    inference(superposition,[],[f70,f1573])).

fof(f1574,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1567,f345,f96,f89,f82,f1572])).

fof(f345,plain,
    ( spl5_6
  <=> k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1567,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f1566,f346])).

fof(f346,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f345])).

fof(f1566,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1565,f83])).

fof(f1565,plain,
    ( k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | v2_funct_1(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1564,f97])).

fof(f1564,plain,
    ( ~ v1_relat_1(sK0)
    | k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0)))
    | v2_funct_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f686,f90])).

fof(f686,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k11_relat_1(X1,sK2(X1)) = k1_tarski(k1_funct_1(X1,sK2(X1)))
      | v2_funct_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f684])).

fof(f684,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k11_relat_1(X1,sK2(X1)) = k1_tarski(k1_funct_1(X1,sK2(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f347,plain,
    ( spl5_6
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f340,f96,f89,f82,f345])).

fof(f340,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f339,f83])).

fof(f339,plain,
    ( k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | v2_funct_1(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f338,f97])).

fof(f338,plain,
    ( ~ v1_relat_1(sK0)
    | k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0))
    | v2_funct_1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f90])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f50,f89])).

fof(f50,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f52,f82])).

fof(f52,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t54_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:30 EDT 2019

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       : 1099 (4889 expanded)
%              Number of leaves         :  258 (1881 expanded)
%              Depth                    :   14
%              Number of atoms          : 3188 (12838 expanded)
%              Number of equality atoms :   84 ( 837 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3764,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f137,f144,f151,f158,f170,f182,f199,f206,f215,f225,f239,f246,f248,f249,f265,f272,f285,f300,f310,f328,f349,f379,f387,f396,f404,f411,f423,f432,f459,f468,f479,f491,f502,f512,f522,f529,f538,f545,f561,f570,f581,f604,f613,f620,f641,f648,f672,f679,f690,f733,f740,f747,f754,f769,f776,f785,f818,f833,f840,f847,f862,f872,f882,f900,f904,f916,f923,f937,f944,f955,f973,f980,f993,f1000,f1027,f1034,f1041,f1048,f1059,f1079,f1090,f1108,f1118,f1130,f1137,f1144,f1151,f1163,f1170,f1183,f1202,f1209,f1216,f1227,f1234,f1249,f1259,f1266,f1268,f1315,f1317,f1439,f1446,f1453,f1479,f1486,f1503,f1510,f1528,f1553,f1560,f1567,f1574,f1581,f1588,f1595,f1622,f1634,f1647,f1674,f1734,f1787,f1794,f1801,f1808,f1825,f1835,f1842,f1849,f1856,f1863,f1870,f1877,f1884,f1891,f1898,f1905,f1912,f1924,f1944,f1962,f1969,f1976,f1988,f2012,f2040,f2061,f2070,f2080,f2096,f2105,f2129,f2139,f2165,f2172,f2174,f2281,f2283,f2285,f2287,f2289,f2294,f2481,f2482,f2491,f2513,f2520,f2541,f2564,f2571,f2578,f2585,f2619,f2626,f2639,f2646,f2660,f2667,f2677,f2684,f2691,f2719,f2737,f2758,f2781,f2791,f2798,f2805,f2823,f2838,f2845,f2858,f2884,f2901,f2929,f2936,f2948,f2955,f2968,f2975,f2996,f3045,f3052,f3060,f3080,f3095,f3097,f3104,f3106,f3109,f3111,f3113,f3115,f3118,f3120,f3170,f3221,f3234,f3236,f3238,f3240,f3242,f3247,f3249,f3253,f3255,f3257,f3259,f3261,f3263,f3265,f3267,f3269,f3271,f3273,f3377,f3379,f3384,f3387,f3410,f3417,f3464,f3475,f3590,f3592,f3594,f3656,f3658,f3665,f3683,f3685,f3704,f3713,f3716,f3740,f3754])).

fof(f3754,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_38
    | spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(avatar_contradiction_clause,[],[f3753])).

fof(f3753,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(subsumption_resolution,[],[f3752,f2736])).

fof(f2736,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_342 ),
    inference(avatar_component_clause,[],[f2735])).

fof(f2735,plain,
    ( spl6_342
  <=> m1_subset_1(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_342])])).

fof(f3752,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3751,f3604])).

fof(f3604,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3603,f3501])).

fof(f3501,plain,
    ( k1_tops_1(sK0,sK2) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f171,f103,f235,f276])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | X1 = X2
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f106,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t8_boole)).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t2_subset)).

fof(f235,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl6_24
  <=> v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',existence_m1_subset_1)).

fof(f171,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f143,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t7_boole)).

fof(f143,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f3603,plain,
    ( k1_zfmisc_1(k1_tops_1(sK0,sK2)) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(subsumption_resolution,[],[f3572,f3334])).

fof(f3334,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_139 ),
    inference(backward_demodulation,[],[f3313,f972])).

fof(f972,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_139 ),
    inference(avatar_component_clause,[],[f971])).

fof(f971,plain,
    ( spl6_139
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f3313,plain,
    ( k1_zfmisc_1(sK2) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f171,f103,f327,f276])).

fof(f327,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl6_38
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f3572,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | k1_zfmisc_1(k1_tops_1(sK0,sK2)) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_336 ),
    inference(backward_demodulation,[],[f3501,f3037])).

fof(f3037,plain,
    ( r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | k1_zfmisc_1(k1_tops_1(sK0,sK2)) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_336 ),
    inference(resolution,[],[f2690,f277])).

fof(f277,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,X4)
        | r2_hidden(X3,X4)
        | o_0_0_xboole_0 = X4 )
    | ~ spl6_4 ),
    inference(resolution,[],[f106,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f159,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t6_boole)).

fof(f159,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f143,f97])).

fof(f2690,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_336 ),
    inference(avatar_component_clause,[],[f2689])).

fof(f2689,plain,
    ( spl6_336
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_336])])).

fof(f3751,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f3486,f3501])).

fof(f3486,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_24
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f235,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t5_subset)).

fof(f271,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl6_30
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f3740,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_40
    | spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(avatar_contradiction_clause,[],[f3739])).

fof(f3739,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(subsumption_resolution,[],[f3738,f2736])).

fof(f3738,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_40
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3737,f3604])).

fof(f3737,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f3492,f3501])).

fof(f3492,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_24
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f348,f235,f122])).

fof(f348,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl6_40
  <=> r2_hidden(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f3716,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_58
    | spl6_139
    | spl6_331
    | ~ spl6_336 ),
    inference(avatar_contradiction_clause,[],[f3715])).

fof(f3715,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_58
    | ~ spl6_139
    | ~ spl6_331
    | ~ spl6_336 ),
    inference(subsumption_resolution,[],[f3714,f467])).

fof(f467,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl6_58
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f3714,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_331
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3584,f3604])).

fof(f3584,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_331 ),
    inference(backward_demodulation,[],[f3501,f3358])).

fof(f3358,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_331 ),
    inference(backward_demodulation,[],[f3313,f2666])).

fof(f2666,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_331 ),
    inference(avatar_component_clause,[],[f2665])).

fof(f2665,plain,
    ( spl6_331
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_331])])).

fof(f3713,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | spl6_139
    | spl6_327
    | ~ spl6_336
    | ~ spl6_394 ),
    inference(avatar_contradiction_clause,[],[f3712])).

fof(f3712,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_327
    | ~ spl6_336
    | ~ spl6_394 ),
    inference(subsumption_resolution,[],[f3711,f3416])).

fof(f3416,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_394 ),
    inference(avatar_component_clause,[],[f3415])).

fof(f3415,plain,
    ( spl6_394
  <=> m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_394])])).

fof(f3711,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_327
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3710,f3604])).

fof(f3710,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_327
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3583,f3604])).

fof(f3583,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_327 ),
    inference(backward_demodulation,[],[f3501,f3357])).

fof(f3357,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2))))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_327 ),
    inference(backward_demodulation,[],[f3313,f2645])).

fof(f2645,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2))))
    | ~ spl6_327 ),
    inference(avatar_component_clause,[],[f2644])).

fof(f2644,plain,
    ( spl6_327
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_327])])).

fof(f3704,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | spl6_241
    | ~ spl6_394 ),
    inference(avatar_contradiction_clause,[],[f3703])).

fof(f3703,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_241
    | ~ spl6_394 ),
    inference(subsumption_resolution,[],[f3579,f3416])).

fof(f3579,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_241 ),
    inference(backward_demodulation,[],[f3501,f3350])).

fof(f3350,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_tops_1(sK0,sK2))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_241 ),
    inference(backward_demodulation,[],[f3313,f1807])).

fof(f1807,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_241 ),
    inference(avatar_component_clause,[],[f1806])).

fof(f1806,plain,
    ( spl6_241
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_241])])).

fof(f3685,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_58
    | spl6_139
    | spl6_185
    | ~ spl6_336 ),
    inference(avatar_contradiction_clause,[],[f3684])).

fof(f3684,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_58
    | ~ spl6_139
    | ~ spl6_185
    | ~ spl6_336 ),
    inference(subsumption_resolution,[],[f3624,f467])).

fof(f3624,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_185
    | ~ spl6_336 ),
    inference(backward_demodulation,[],[f3604,f3337])).

fof(f3337,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_185 ),
    inference(backward_demodulation,[],[f3313,f1226])).

fof(f1226,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_185 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1225,plain,
    ( spl6_185
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).

fof(f3683,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | spl6_139
    | spl6_179
    | ~ spl6_336
    | ~ spl6_394 ),
    inference(avatar_contradiction_clause,[],[f3682])).

fof(f3682,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_179
    | ~ spl6_336
    | ~ spl6_394 ),
    inference(subsumption_resolution,[],[f3681,f3416])).

fof(f3681,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_179
    | ~ spl6_336 ),
    inference(forward_demodulation,[],[f3623,f3604])).

fof(f3623,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_139
    | ~ spl6_179
    | ~ spl6_336 ),
    inference(backward_demodulation,[],[f3604,f3336])).

fof(f3336,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_179 ),
    inference(backward_demodulation,[],[f3313,f1201])).

fof(f1201,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_179 ),
    inference(avatar_component_clause,[],[f1200])).

fof(f1200,plain,
    ( spl6_179
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f3665,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | spl6_91
    | spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(avatar_contradiction_clause,[],[f3664])).

fof(f3664,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_91
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_342 ),
    inference(subsumption_resolution,[],[f3607,f2736])).

fof(f3607,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_91
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(backward_demodulation,[],[f3604,f671])).

fof(f671,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl6_91
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f3658,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | spl6_139
    | ~ spl6_336
    | ~ spl6_344
    | spl6_369 ),
    inference(avatar_contradiction_clause,[],[f3657])).

fof(f3657,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_344
    | ~ spl6_369 ),
    inference(subsumption_resolution,[],[f3631,f3364])).

fof(f3364,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_369 ),
    inference(backward_demodulation,[],[f3313,f2939])).

fof(f2939,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(sK3))
    | ~ spl6_369 ),
    inference(resolution,[],[f2928,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t3_subset)).

fof(f2928,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_369 ),
    inference(avatar_component_clause,[],[f2927])).

fof(f2927,plain,
    ( spl6_369
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_369])])).

fof(f3631,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK3))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_344 ),
    inference(backward_demodulation,[],[f3605,f2773])).

fof(f2773,plain,
    ( m1_subset_1(sK4(o_0_0_xboole_0),k1_zfmisc_1(sK3))
    | ~ spl6_344 ),
    inference(unit_resulting_resolution,[],[f2757,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2757,plain,
    ( r1_tarski(sK4(o_0_0_xboole_0),sK3)
    | ~ spl6_344 ),
    inference(avatar_component_clause,[],[f2756])).

fof(f2756,plain,
    ( spl6_344
  <=> r1_tarski(sK4(o_0_0_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_344])])).

fof(f3605,plain,
    ( o_0_0_xboole_0 = sK4(o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | ~ spl6_139
    | ~ spl6_336 ),
    inference(backward_demodulation,[],[f3604,f458])).

fof(f458,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl6_56
  <=> o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f3656,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | spl6_139
    | ~ spl6_336
    | ~ spl6_344
    | spl6_369 ),
    inference(avatar_contradiction_clause,[],[f3655])).

fof(f3655,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_344
    | ~ spl6_369 ),
    inference(subsumption_resolution,[],[f3630,f3362])).

fof(f3362,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_369 ),
    inference(backward_demodulation,[],[f3313,f2928])).

fof(f3630,plain,
    ( r1_tarski(o_0_0_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_38
    | ~ spl6_56
    | ~ spl6_139
    | ~ spl6_336
    | ~ spl6_344 ),
    inference(backward_demodulation,[],[f3605,f2757])).

fof(f3594,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_95
    | ~ spl6_176 ),
    inference(avatar_contradiction_clause,[],[f3593])).

fof(f3593,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_95
    | ~ spl6_176 ),
    inference(subsumption_resolution,[],[f3524,f689])).

fof(f689,plain,
    ( ~ r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl6_95
  <=> ~ r1_tarski(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f3524,plain,
    ( r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_176 ),
    inference(backward_demodulation,[],[f3501,f1179])).

fof(f1179,plain,
    ( r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl6_176 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f1178,plain,
    ( spl6_176
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f3592,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_91
    | ~ spl6_170 ),
    inference(avatar_contradiction_clause,[],[f3591])).

fof(f3591,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_91
    | ~ spl6_170 ),
    inference(subsumption_resolution,[],[f3522,f671])).

fof(f3522,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_170 ),
    inference(backward_demodulation,[],[f3501,f1147])).

fof(f1147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_170 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1146,plain,
    ( spl6_170
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f3590,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_26
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f3589])).

fof(f3589,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f3513,f395])).

fof(f395,plain,
    ( ~ m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl6_47
  <=> ~ m1_subset_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f3513,plain,
    ( m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(backward_demodulation,[],[f3501,f245])).

fof(f245,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_26
  <=> m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f3475,plain,
    ( ~ spl6_399
    | ~ spl6_4
    | ~ spl6_38
    | spl6_107 ),
    inference(avatar_split_clause,[],[f3331,f774,f326,f142,f3473])).

fof(f3473,plain,
    ( spl6_399
  <=> ~ m1_subset_1(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_399])])).

fof(f774,plain,
    ( spl6_107
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f3331,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_107 ),
    inference(backward_demodulation,[],[f3313,f775])).

fof(f775,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_107 ),
    inference(avatar_component_clause,[],[f774])).

fof(f3464,plain,
    ( ~ spl6_397
    | ~ spl6_4
    | ~ spl6_38
    | spl6_99 ),
    inference(avatar_split_clause,[],[f3330,f738,f326,f142,f3462])).

fof(f3462,plain,
    ( spl6_397
  <=> ~ r2_hidden(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_397])])).

fof(f738,plain,
    ( spl6_99
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f3330,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_99 ),
    inference(backward_demodulation,[],[f3313,f739])).

fof(f739,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f738])).

fof(f3417,plain,
    ( spl6_394
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f3326,f406,f326,f142,f3415])).

fof(f406,plain,
    ( spl6_50
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f3326,plain,
    ( m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_50 ),
    inference(backward_demodulation,[],[f3313,f407])).

fof(f407,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f406])).

fof(f3410,plain,
    ( spl6_342
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f3323,f326,f210,f142,f2735])).

fof(f210,plain,
    ( spl6_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f3323,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f3313,f211])).

fof(f211,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f3387,plain,
    ( ~ spl6_4
    | ~ spl6_38
    | ~ spl6_388 ),
    inference(avatar_contradiction_clause,[],[f3386])).

fof(f3386,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_388 ),
    inference(subsumption_resolution,[],[f3371,f171])).

fof(f3371,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_388 ),
    inference(backward_demodulation,[],[f3313,f3079])).

fof(f3079,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK2))
    | ~ spl6_388 ),
    inference(avatar_component_clause,[],[f3078])).

fof(f3078,plain,
    ( spl6_388
  <=> r2_hidden(k3_subset_1(sK2,sK4(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_388])])).

fof(f3384,plain,
    ( ~ spl6_4
    | ~ spl6_38
    | ~ spl6_50
    | spl6_365 ),
    inference(avatar_contradiction_clause,[],[f3383])).

fof(f3383,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_50
    | ~ spl6_365 ),
    inference(subsumption_resolution,[],[f3361,f3326])).

fof(f3361,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_365 ),
    inference(backward_demodulation,[],[f3313,f2883])).

fof(f2883,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl6_365 ),
    inference(avatar_component_clause,[],[f2882])).

fof(f2882,plain,
    ( spl6_365
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_365])])).

fof(f3379,plain,
    ( ~ spl6_4
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(avatar_contradiction_clause,[],[f3378])).

fof(f3378,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f3327,f171])).

fof(f3327,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f3313,f419])).

fof(f419,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl6_52
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f3377,plain,
    ( ~ spl6_4
    | ~ spl6_20
    | ~ spl6_38
    | spl6_343 ),
    inference(avatar_contradiction_clause,[],[f3376])).

fof(f3376,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_38
    | ~ spl6_343 ),
    inference(subsumption_resolution,[],[f3323,f2733])).

fof(f2733,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_343 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f2732,plain,
    ( spl6_343
  <=> ~ m1_subset_1(sK3,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_343])])).

fof(f3273,plain,
    ( ~ spl6_38
    | ~ spl6_206 ),
    inference(avatar_contradiction_clause,[],[f3272])).

fof(f3272,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_206 ),
    inference(subsumption_resolution,[],[f1538,f327])).

fof(f1538,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_206 ),
    inference(resolution,[],[f1509,f120])).

fof(f1509,plain,
    ( r2_hidden(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_206 ),
    inference(avatar_component_clause,[],[f1508])).

fof(f1508,plain,
    ( spl6_206
  <=> r2_hidden(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_206])])).

fof(f3271,plain,
    ( ~ spl6_38
    | ~ spl6_206 ),
    inference(avatar_contradiction_clause,[],[f3270])).

fof(f3270,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_206 ),
    inference(subsumption_resolution,[],[f1533,f327])).

fof(f1533,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_206 ),
    inference(unit_resulting_resolution,[],[f1509,f120])).

fof(f3269,plain,
    ( ~ spl6_38
    | ~ spl6_192 ),
    inference(avatar_contradiction_clause,[],[f3268])).

fof(f3268,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_192 ),
    inference(subsumption_resolution,[],[f1496,f327])).

fof(f1496,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_192 ),
    inference(resolution,[],[f1265,f120])).

fof(f1265,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2))
    | ~ spl6_192 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f1264,plain,
    ( spl6_192
  <=> r2_hidden(sK4(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_192])])).

fof(f3267,plain,
    ( ~ spl6_38
    | ~ spl6_192 ),
    inference(avatar_contradiction_clause,[],[f3266])).

fof(f3266,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_192 ),
    inference(subsumption_resolution,[],[f1491,f327])).

fof(f1491,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_192 ),
    inference(unit_resulting_resolution,[],[f1265,f120])).

fof(f3265,plain,
    ( ~ spl6_4
    | ~ spl6_132
    | ~ spl6_206
    | ~ spl6_230 ),
    inference(avatar_contradiction_clause,[],[f3264])).

fof(f3264,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_132
    | ~ spl6_206
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f1722,f933])).

fof(f933,plain,
    ( m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_132 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl6_132
  <=> m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f1722,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_206
    | ~ spl6_230 ),
    inference(forward_demodulation,[],[f1681,f1693])).

fof(f1693,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_230 ),
    inference(unit_resulting_resolution,[],[f1673,f161])).

fof(f1673,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl6_230 ),
    inference(avatar_component_clause,[],[f1672])).

fof(f1672,plain,
    ( spl6_230
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).

fof(f1681,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl6_206
    | ~ spl6_230 ),
    inference(unit_resulting_resolution,[],[f1509,f1673,f122])).

fof(f3263,plain,
    ( ~ spl6_4
    | ~ spl6_132
    | ~ spl6_192
    | ~ spl6_230 ),
    inference(avatar_contradiction_clause,[],[f3262])).

fof(f3262,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_132
    | ~ spl6_192
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f1715,f933])).

fof(f1715,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_192
    | ~ spl6_230 ),
    inference(forward_demodulation,[],[f1688,f1693])).

fof(f1688,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)))
    | ~ spl6_192
    | ~ spl6_230 ),
    inference(unit_resulting_resolution,[],[f1265,f1673,f122])).

fof(f3261,plain,
    ( ~ spl6_4
    | ~ spl6_132
    | ~ spl6_206 ),
    inference(avatar_contradiction_clause,[],[f3260])).

fof(f3260,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_132
    | ~ spl6_206 ),
    inference(subsumption_resolution,[],[f1529,f933])).

fof(f1529,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_206 ),
    inference(unit_resulting_resolution,[],[f143,f1509,f122])).

fof(f3259,plain,
    ( ~ spl6_4
    | ~ spl6_132
    | ~ spl6_192 ),
    inference(avatar_contradiction_clause,[],[f3258])).

fof(f3258,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_132
    | ~ spl6_192 ),
    inference(subsumption_resolution,[],[f1487,f933])).

fof(f1487,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_192 ),
    inference(unit_resulting_resolution,[],[f143,f1265,f122])).

fof(f3257,plain,
    ( ~ spl6_24
    | ~ spl6_32
    | ~ spl6_336 ),
    inference(avatar_contradiction_clause,[],[f3256])).

fof(f3256,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_336 ),
    inference(subsumption_resolution,[],[f235,f3025])).

fof(f3025,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl6_32
    | ~ spl6_336 ),
    inference(unit_resulting_resolution,[],[f2690,f2531])).

fof(f2531,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(X1)) )
    | ~ spl6_32 ),
    inference(resolution,[],[f284,f122])).

fof(f284,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl6_32
  <=> r2_hidden(sK4(k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3255,plain,
    ( ~ spl6_38
    | ~ spl6_204 ),
    inference(avatar_contradiction_clause,[],[f3254])).

fof(f3254,plain,
    ( $false
    | ~ spl6_38
    | ~ spl6_204 ),
    inference(subsumption_resolution,[],[f327,f2401])).

fof(f2401,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_204 ),
    inference(resolution,[],[f1502,f120])).

fof(f1502,plain,
    ( r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl6_204 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1501,plain,
    ( spl6_204
  <=> r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_204])])).

fof(f3253,plain,
    ( ~ spl6_4
    | ~ spl6_32
    | ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f3252])).

fof(f3252,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_32
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f487,f2982])).

fof(f2982,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_32 ),
    inference(resolution,[],[f2531,f143])).

fof(f487,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl6_62
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f3249,plain,
    ( ~ spl6_4
    | ~ spl6_132
    | ~ spl6_204 ),
    inference(avatar_contradiction_clause,[],[f3248])).

fof(f3248,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_132
    | ~ spl6_204 ),
    inference(subsumption_resolution,[],[f933,f2392])).

fof(f2392,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_204 ),
    inference(unit_resulting_resolution,[],[f143,f1502,f122])).

fof(f3247,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3246])).

fof(f3246,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3245,f511])).

fof(f511,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl6_66
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f3245,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_14
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3244,f537])).

fof(f537,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl6_72
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f3244,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_14
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3232,f1169])).

fof(f1169,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_174 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1168,plain,
    ( spl6_174
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_174])])).

fof(f3232,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_14
    | ~ spl6_126 ),
    inference(resolution,[],[f903,f192])).

fof(f192,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl6_14
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f903,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl6_126 ),
    inference(avatar_component_clause,[],[f902])).

fof(f902,plain,
    ( spl6_126
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f3242,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3241])).

fof(f3241,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3225,f1169])).

fof(f3225,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126 ),
    inference(unit_resulting_resolution,[],[f511,f537,f192,f903])).

fof(f3240,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3239])).

fof(f3239,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3226,f192])).

fof(f3226,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f511,f537,f1169,f903])).

fof(f3238,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3237])).

fof(f3237,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3227,f537])).

fof(f3227,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f511,f192,f1169,f903])).

fof(f3236,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3235])).

fof(f3235,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(subsumption_resolution,[],[f3228,f511])).

fof(f3228,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_14
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f537,f192,f1169,f903])).

fof(f3234,plain,
    ( ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(avatar_contradiction_clause,[],[f3229])).

fof(f3229,plain,
    ( $false
    | ~ spl6_14
    | ~ spl6_66
    | ~ spl6_72
    | ~ spl6_126
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f511,f537,f192,f1169,f903])).

fof(f3221,plain,
    ( ~ spl6_393
    | ~ spl6_4
    | spl6_339 ),
    inference(avatar_split_clause,[],[f3214,f2708,f142,f3219])).

fof(f3219,plain,
    ( spl6_393
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_393])])).

fof(f2708,plain,
    ( spl6_339
  <=> k1_zfmisc_1(sK3) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_339])])).

fof(f3214,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK3))
    | ~ spl6_4
    | ~ spl6_339 ),
    inference(unit_resulting_resolution,[],[f143,f2709,f119])).

fof(f2709,plain,
    ( k1_zfmisc_1(sK3) != o_0_0_xboole_0
    | ~ spl6_339 ),
    inference(avatar_component_clause,[],[f2708])).

fof(f3170,plain,
    ( ~ spl6_391
    | spl6_37
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f3128,f579,f305,f3168])).

fof(f3168,plain,
    ( spl6_391
  <=> ~ r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_391])])).

fof(f305,plain,
    ( spl6_37
  <=> ~ m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f579,plain,
    ( spl6_80
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f3128,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ spl6_37
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f306,f2017])).

fof(f2017,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | m1_subset_1(sK1,X0) )
    | ~ spl6_80 ),
    inference(resolution,[],[f630,f118])).

fof(f630,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | m1_subset_1(sK1,X0) )
    | ~ spl6_80 ),
    inference(resolution,[],[f580,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t4_subset)).

fof(f580,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f579])).

fof(f306,plain,
    ( ~ m1_subset_1(sK1,sK3)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f305])).

fof(f3120,plain,
    ( spl6_181
    | ~ spl6_188 ),
    inference(avatar_contradiction_clause,[],[f3119])).

fof(f3119,plain,
    ( $false
    | ~ spl6_181
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f1205,f1251])).

fof(f1251,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_188 ),
    inference(unit_resulting_resolution,[],[f1248,f118])).

fof(f1248,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),sK3)
    | ~ spl6_188 ),
    inference(avatar_component_clause,[],[f1247])).

fof(f1247,plain,
    ( spl6_188
  <=> r1_tarski(k3_subset_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f1205,plain,
    ( ~ m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_181 ),
    inference(avatar_component_clause,[],[f1204])).

fof(f1204,plain,
    ( spl6_181
  <=> ~ m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_181])])).

fof(f3118,plain,
    ( spl6_159
    | ~ spl6_188
    | ~ spl6_272 ),
    inference(avatar_contradiction_clause,[],[f3117])).

fof(f3117,plain,
    ( $false
    | ~ spl6_159
    | ~ spl6_188
    | ~ spl6_272 ),
    inference(subsumption_resolution,[],[f3116,f1251])).

fof(f3116,plain,
    ( ~ m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_159
    | ~ spl6_272 ),
    inference(subsumption_resolution,[],[f1991,f1086])).

fof(f1086,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl6_159 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1085,plain,
    ( spl6_159
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).

fof(f1991,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_272 ),
    inference(superposition,[],[f107,f1961])).

fof(f1961,plain,
    ( k3_subset_1(sK3,k3_subset_1(sK3,sK3)) = sK3
    | ~ spl6_272 ),
    inference(avatar_component_clause,[],[f1960])).

fof(f1960,plain,
    ( spl6_272
  <=> k3_subset_1(sK3,k3_subset_1(sK3,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_272])])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',dt_k3_subset_1)).

fof(f3115,plain,
    ( spl6_101
    | ~ spl6_108 ),
    inference(avatar_contradiction_clause,[],[f3114])).

fof(f3114,plain,
    ( $false
    | ~ spl6_101
    | ~ spl6_108 ),
    inference(subsumption_resolution,[],[f743,f809])).

fof(f809,plain,
    ( m1_subset_1(sK4(sK3),sK2)
    | ~ spl6_108 ),
    inference(resolution,[],[f784,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t1_subset)).

fof(f784,plain,
    ( r2_hidden(sK4(sK3),sK2)
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl6_108
  <=> r2_hidden(sK4(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f743,plain,
    ( ~ m1_subset_1(sK4(sK3),sK2)
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl6_101
  <=> ~ m1_subset_1(sK4(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f3113,plain,
    ( ~ spl6_8
    | ~ spl6_108
    | spl6_135 ),
    inference(avatar_contradiction_clause,[],[f3112])).

fof(f3112,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_108
    | ~ spl6_135 ),
    inference(subsumption_resolution,[],[f940,f800])).

fof(f800,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_108 ),
    inference(unit_resulting_resolution,[],[f157,f784,f121])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f940,plain,
    ( ~ m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_135 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl6_135
  <=> ~ m1_subset_1(sK4(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f3111,plain,
    ( spl6_157
    | ~ spl6_180
    | ~ spl6_272
    | ~ spl6_276 ),
    inference(avatar_contradiction_clause,[],[f3110])).

fof(f3110,plain,
    ( $false
    | ~ spl6_157
    | ~ spl6_180
    | ~ spl6_272
    | ~ spl6_276 ),
    inference(subsumption_resolution,[],[f1075,f2002])).

fof(f2002,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl6_180
    | ~ spl6_272
    | ~ spl6_276 ),
    inference(forward_demodulation,[],[f2000,f1961])).

fof(f2000,plain,
    ( r1_tarski(k3_subset_1(sK3,k3_subset_1(sK3,sK3)),k3_subset_1(sK3,k3_subset_1(sK3,sK3)))
    | ~ spl6_180
    | ~ spl6_276 ),
    inference(unit_resulting_resolution,[],[f1208,f1208,f1975,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t31_subset_1)).

fof(f1975,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK3))
    | ~ spl6_276 ),
    inference(avatar_component_clause,[],[f1974])).

fof(f1974,plain,
    ( spl6_276
  <=> r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_276])])).

fof(f1208,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_180 ),
    inference(avatar_component_clause,[],[f1207])).

fof(f1207,plain,
    ( spl6_180
  <=> m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f1075,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ spl6_157 ),
    inference(avatar_component_clause,[],[f1074])).

fof(f1074,plain,
    ( spl6_157
  <=> ~ r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).

fof(f3109,plain,
    ( spl6_159
    | ~ spl6_272
    | ~ spl6_338
    | ~ spl6_346 ),
    inference(avatar_contradiction_clause,[],[f3108])).

fof(f3108,plain,
    ( $false
    | ~ spl6_159
    | ~ spl6_272
    | ~ spl6_338
    | ~ spl6_346 ),
    inference(subsumption_resolution,[],[f3107,f3100])).

fof(f3100,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_272
    | ~ spl6_338
    | ~ spl6_346 ),
    inference(subsumption_resolution,[],[f3099,f2780])).

fof(f2780,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),o_0_0_xboole_0)
    | ~ spl6_346 ),
    inference(avatar_component_clause,[],[f2779])).

fof(f2779,plain,
    ( spl6_346
  <=> m1_subset_1(k3_subset_1(sK3,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_346])])).

fof(f3099,plain,
    ( ~ m1_subset_1(k3_subset_1(sK3,sK3),o_0_0_xboole_0)
    | m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_272
    | ~ spl6_338 ),
    inference(forward_demodulation,[],[f3098,f2712])).

fof(f2712,plain,
    ( k1_zfmisc_1(sK3) = o_0_0_xboole_0
    | ~ spl6_338 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f2711,plain,
    ( spl6_338
  <=> k1_zfmisc_1(sK3) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_338])])).

fof(f3098,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_272
    | ~ spl6_338 ),
    inference(forward_demodulation,[],[f1991,f2712])).

fof(f3107,plain,
    ( ~ m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_159
    | ~ spl6_338 ),
    inference(forward_demodulation,[],[f1086,f2712])).

fof(f3106,plain,
    ( spl6_167
    | ~ spl6_206 ),
    inference(avatar_contradiction_clause,[],[f3105])).

fof(f3105,plain,
    ( $false
    | ~ spl6_167
    | ~ spl6_206 ),
    inference(subsumption_resolution,[],[f1133,f1536])).

fof(f1536,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_206 ),
    inference(resolution,[],[f1509,f105])).

fof(f1133,plain,
    ( ~ m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_167 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1132,plain,
    ( spl6_167
  <=> ~ m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f3104,plain,
    ( ~ spl6_272
    | ~ spl6_338
    | spl6_343
    | ~ spl6_346 ),
    inference(avatar_contradiction_clause,[],[f3103])).

fof(f3103,plain,
    ( $false
    | ~ spl6_272
    | ~ spl6_338
    | ~ spl6_343
    | ~ spl6_346 ),
    inference(subsumption_resolution,[],[f2733,f3100])).

fof(f3097,plain,
    ( spl6_15
    | spl6_25
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f3096])).

fof(f3096,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f245,f2330])).

fof(f2330,plain,
    ( ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_15
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f238,f189,f106])).

fof(f189,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl6_15
  <=> ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f238,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl6_25
  <=> ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f3095,plain,
    ( ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148
    | ~ spl6_174
    | spl6_177
    | ~ spl6_202
    | ~ spl6_214
    | ~ spl6_274
    | ~ spl6_384 ),
    inference(avatar_contradiction_clause,[],[f3094])).

fof(f3094,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148
    | ~ spl6_174
    | ~ spl6_177
    | ~ spl6_202
    | ~ spl6_214
    | ~ spl6_274
    | ~ spl6_384 ),
    inference(subsumption_resolution,[],[f3091,f1397])).

fof(f1397,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_84
    | ~ spl6_174
    | ~ spl6_177 ),
    inference(unit_resulting_resolution,[],[f619,f1182,f1169,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1182,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl6_177 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1181,plain,
    ( spl6_177
  <=> ~ r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_177])])).

fof(f619,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl6_84
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f3091,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148
    | ~ spl6_202
    | ~ spl6_214
    | ~ spl6_274
    | ~ spl6_384 ),
    inference(backward_demodulation,[],[f3087,f2158])).

fof(f2158,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148
    | ~ spl6_202
    | ~ spl6_214
    | ~ spl6_274 ),
    inference(forward_demodulation,[],[f2153,f1065])).

fof(f1065,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148 ),
    inference(subsumption_resolution,[],[f1064,f136])).

fof(f136,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1064,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_84
    | ~ spl6_148 ),
    inference(subsumption_resolution,[],[f1063,f657])).

fof(f657,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f619,f107])).

fof(f1063,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_148 ),
    inference(resolution,[],[f1033,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t52_pre_topc)).

fof(f1033,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl6_148 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1032,plain,
    ( spl6_148
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f2153,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl6_2
    | ~ spl6_202
    | ~ spl6_214
    | ~ spl6_274 ),
    inference(unit_resulting_resolution,[],[f136,f1485,f1566,f1968,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t49_pre_topc)).

fof(f1968,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_274 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f1967,plain,
    ( spl6_274
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_274])])).

fof(f1566,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_214 ),
    inference(avatar_component_clause,[],[f1565])).

fof(f1565,plain,
    ( spl6_214
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_214])])).

fof(f1485,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_202 ),
    inference(avatar_component_clause,[],[f1484])).

fof(f1484,plain,
    ( spl6_202
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).

fof(f3087,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl6_2
    | ~ spl6_202
    | ~ spl6_384 ),
    inference(subsumption_resolution,[],[f3083,f1599])).

fof(f1599,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_202 ),
    inference(unit_resulting_resolution,[],[f136,f1485,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',dt_k2_pre_topc)).

fof(f3083,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_384 ),
    inference(superposition,[],[f108,f3051])).

fof(f3051,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl6_384 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl6_384
  <=> k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_384])])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',involutiveness_k3_subset_1)).

fof(f3080,plain,
    ( spl6_388
    | spl6_39 ),
    inference(avatar_split_clause,[],[f1771,f323,f3078])).

fof(f323,plain,
    ( spl6_39
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1771,plain,
    ( r2_hidden(k3_subset_1(sK2,sK4(k1_zfmisc_1(sK2))),k1_zfmisc_1(sK2))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f324,f413,f106])).

fof(f413,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK4(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f103,f107])).

fof(f324,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f323])).

fof(f3060,plain,
    ( ~ spl6_387
    | spl6_179 ),
    inference(avatar_split_clause,[],[f1218,f1200,f3058])).

fof(f3058,plain,
    ( spl6_387
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_387])])).

fof(f1218,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl6_179 ),
    inference(unit_resulting_resolution,[],[f103,f1201,f121])).

fof(f3052,plain,
    ( spl6_384
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f925,f156,f135,f3050])).

fof(f925,plain,
    ( k1_tops_1(sK0,sK2) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',d1_tops_1)).

fof(f3045,plain,
    ( spl6_382
    | ~ spl6_158
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2721,f2711,f1088,f3043])).

fof(f3043,plain,
    ( spl6_382
  <=> r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_382])])).

fof(f1088,plain,
    ( spl6_158
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f2721,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK4(o_0_0_xboole_0)))
    | ~ spl6_158
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1096])).

fof(f1096,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK4(k1_zfmisc_1(sK3))))
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f174,f103,f1089,f109])).

fof(f1089,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl6_158 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f174,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f103,f117])).

fof(f2996,plain,
    ( spl6_380
    | ~ spl6_320 ),
    inference(avatar_split_clause,[],[f2986,f2617,f2994])).

fof(f2994,plain,
    ( spl6_380
  <=> r1_tarski(k3_subset_1(sK2,k1_tops_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_380])])).

fof(f2617,plain,
    ( spl6_320
  <=> m1_subset_1(k3_subset_1(sK2,k1_tops_1(sK0,sK2)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_320])])).

fof(f2986,plain,
    ( r1_tarski(k3_subset_1(sK2,k1_tops_1(sK0,sK2)),sK2)
    | ~ spl6_320 ),
    inference(unit_resulting_resolution,[],[f2618,f117])).

fof(f2618,plain,
    ( m1_subset_1(k3_subset_1(sK2,k1_tops_1(sK0,sK2)),k1_zfmisc_1(sK2))
    | ~ spl6_320 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2975,plain,
    ( ~ spl6_379
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f2528,f283,f2973])).

fof(f2973,plain,
    ( spl6_379
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),sK4(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_379])])).

fof(f2528,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),sK4(k1_tops_1(sK0,sK2)))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f284,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',antisymmetry_r2_hidden)).

fof(f2968,plain,
    ( ~ spl6_377
    | spl6_107
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2724,f2711,f774,f2966])).

fof(f2966,plain,
    ( spl6_377
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK3,sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_377])])).

fof(f2724,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK3,sK4(o_0_0_xboole_0)))
    | ~ spl6_107
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1746])).

fof(f1746,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK3,sK4(k1_zfmisc_1(sK3))))
    | ~ spl6_107 ),
    inference(unit_resulting_resolution,[],[f775,f413,f121])).

fof(f2955,plain,
    ( spl6_374
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f505,f149,f2953])).

fof(f2953,plain,
    ( spl6_374
  <=> r1_tarski(k1_tops_1(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),sK4(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_374])])).

fof(f149,plain,
    ( spl6_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f505,plain,
    ( r1_tarski(k1_tops_1(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),sK4(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f150,f103,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t44_tops_1)).

fof(f150,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f2948,plain,
    ( ~ spl6_373
    | ~ spl6_338
    | spl6_363 ),
    inference(avatar_split_clause,[],[f2892,f2873,f2711,f2946])).

fof(f2946,plain,
    ( spl6_373
  <=> ~ r2_hidden(sK3,k3_subset_1(sK3,sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_373])])).

fof(f2873,plain,
    ( spl6_363
  <=> ~ m1_subset_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_363])])).

fof(f2892,plain,
    ( ~ r2_hidden(sK3,k3_subset_1(sK3,sK4(o_0_0_xboole_0)))
    | ~ spl6_338
    | ~ spl6_363 ),
    inference(forward_demodulation,[],[f2888,f2712])).

fof(f2888,plain,
    ( ~ r2_hidden(sK3,k3_subset_1(sK3,sK4(k1_zfmisc_1(sK3))))
    | ~ spl6_363 ),
    inference(unit_resulting_resolution,[],[f413,f2874,f121])).

fof(f2874,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl6_363 ),
    inference(avatar_component_clause,[],[f2873])).

fof(f2936,plain,
    ( ~ spl6_371
    | ~ spl6_338
    | spl6_363 ),
    inference(avatar_split_clause,[],[f2891,f2873,f2711,f2934])).

fof(f2934,plain,
    ( spl6_371
  <=> ~ r2_hidden(sK3,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_371])])).

fof(f2891,plain,
    ( ~ r2_hidden(sK3,sK4(o_0_0_xboole_0))
    | ~ spl6_338
    | ~ spl6_363 ),
    inference(forward_demodulation,[],[f2889,f2712])).

fof(f2889,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(sK3)))
    | ~ spl6_363 ),
    inference(unit_resulting_resolution,[],[f103,f2874,f121])).

fof(f2929,plain,
    ( ~ spl6_369
    | ~ spl6_22
    | spl6_363 ),
    inference(avatar_split_clause,[],[f2885,f2873,f220,f2927])).

fof(f220,plain,
    ( spl6_22
  <=> r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f2885,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_22
    | ~ spl6_363 ),
    inference(unit_resulting_resolution,[],[f2874,f2649])).

fof(f2649,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_zfmisc_1(sK2),X0)
        | m1_subset_1(sK3,X0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f1370,f118])).

fof(f1370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(X0))
        | m1_subset_1(sK3,X0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f221,f121])).

fof(f221,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f2901,plain,
    ( ~ spl6_367
    | spl6_363 ),
    inference(avatar_split_clause,[],[f2890,f2873,f2899])).

fof(f2899,plain,
    ( spl6_367
  <=> ~ r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_367])])).

fof(f2890,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ spl6_363 ),
    inference(unit_resulting_resolution,[],[f2874,f105])).

fof(f2884,plain,
    ( spl6_362
    | ~ spl6_365
    | ~ spl6_22
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2748,f2711,f220,f2882,f2876])).

fof(f2876,plain,
    ( spl6_362
  <=> m1_subset_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_362])])).

fof(f2748,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | m1_subset_1(sK3,sK3)
    | ~ spl6_22
    | ~ spl6_338 ),
    inference(superposition,[],[f1370,f2712])).

fof(f2858,plain,
    ( spl6_360
    | ~ spl6_278
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2728,f2711,f1986,f2856])).

fof(f2856,plain,
    ( spl6_360
  <=> m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK4(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_360])])).

fof(f1986,plain,
    ( spl6_278
  <=> r1_tarski(k3_subset_1(sK3,sK3),sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_278])])).

fof(f2728,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK4(o_0_0_xboole_0)))
    | ~ spl6_278
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f2004])).

fof(f2004,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))
    | ~ spl6_278 ),
    inference(unit_resulting_resolution,[],[f1987,f118])).

fof(f1987,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),sK4(k1_zfmisc_1(sK3)))
    | ~ spl6_278 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f2845,plain,
    ( spl6_358
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2750,f2711,f2843])).

fof(f2843,plain,
    ( spl6_358
  <=> r1_tarski(k3_subset_1(sK3,sK4(o_0_0_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_358])])).

fof(f2750,plain,
    ( r1_tarski(k3_subset_1(sK3,sK4(o_0_0_xboole_0)),sK3)
    | ~ spl6_338 ),
    inference(superposition,[],[f1744,f2712])).

fof(f1744,plain,(
    ! [X0] : r1_tarski(k3_subset_1(X0,sK4(k1_zfmisc_1(X0))),X0) ),
    inference(unit_resulting_resolution,[],[f413,f117])).

fof(f2838,plain,
    ( spl6_356
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2744,f2711,f2836])).

fof(f2836,plain,
    ( spl6_356
  <=> m1_subset_1(k3_subset_1(sK3,sK4(o_0_0_xboole_0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_356])])).

fof(f2744,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK4(o_0_0_xboole_0)),o_0_0_xboole_0)
    | ~ spl6_338 ),
    inference(superposition,[],[f413,f2712])).

fof(f2823,plain,
    ( ~ spl6_355
    | spl6_47
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2812,f2711,f394,f2821])).

fof(f2821,plain,
    ( spl6_355
  <=> ~ r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_355])])).

fof(f2812,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ spl6_47
    | ~ spl6_338 ),
    inference(unit_resulting_resolution,[],[f395,f2742])).

fof(f2742,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,o_0_0_xboole_0)
        | ~ r1_tarski(X1,sK3) )
    | ~ spl6_338 ),
    inference(superposition,[],[f118,f2712])).

fof(f2805,plain,
    ( spl6_352
    | ~ spl6_278
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2725,f2711,f1986,f2803])).

fof(f2803,plain,
    ( spl6_352
  <=> r1_tarski(k3_subset_1(sK3,sK3),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_352])])).

fof(f2725,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),sK4(o_0_0_xboole_0))
    | ~ spl6_278
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1987])).

fof(f2798,plain,
    ( spl6_350
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f504,f135,f2796])).

fof(f2796,plain,
    ( spl6_350
  <=> r1_tarski(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_350])])).

fof(f504,plain,
    ( r1_tarski(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK4(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f136,f103,f98])).

fof(f2791,plain,
    ( ~ spl6_349
    | spl6_211
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2723,f2711,f1551,f2789])).

fof(f2789,plain,
    ( spl6_349
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_349])])).

fof(f1551,plain,
    ( spl6_211
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_211])])).

fof(f2723,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(o_0_0_xboole_0))
    | ~ spl6_211
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1552])).

fof(f1552,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(sK3)))
    | ~ spl6_211 ),
    inference(avatar_component_clause,[],[f1551])).

fof(f2781,plain,
    ( spl6_346
    | ~ spl6_180
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2722,f2711,f1207,f2779])).

fof(f2722,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),o_0_0_xboole_0)
    | ~ spl6_180
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1208])).

fof(f2758,plain,
    ( spl6_344
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2743,f2711,f2756])).

fof(f2743,plain,
    ( r1_tarski(sK4(o_0_0_xboole_0),sK3)
    | ~ spl6_338 ),
    inference(superposition,[],[f174,f2712])).

fof(f2737,plain,
    ( spl6_342
    | ~ spl6_158
    | ~ spl6_338 ),
    inference(avatar_split_clause,[],[f2720,f2711,f1088,f2735])).

fof(f2720,plain,
    ( m1_subset_1(sK3,o_0_0_xboole_0)
    | ~ spl6_158
    | ~ spl6_338 ),
    inference(backward_demodulation,[],[f2712,f1089])).

fof(f2719,plain,
    ( spl6_338
    | spl6_340
    | ~ spl6_4
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f2450,f1088,f142,f2717,f2711])).

fof(f2717,plain,
    ( spl6_340
  <=> r2_hidden(sK3,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_340])])).

fof(f2450,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK3))
    | k1_zfmisc_1(sK3) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_158 ),
    inference(resolution,[],[f277,f1089])).

fof(f2691,plain,
    ( spl6_336
    | ~ spl6_260 ),
    inference(avatar_split_clause,[],[f1937,f1889,f2689])).

fof(f1889,plain,
    ( spl6_260
  <=> r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).

fof(f1937,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_260 ),
    inference(unit_resulting_resolution,[],[f1890,f118])).

fof(f1890,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_260 ),
    inference(avatar_component_clause,[],[f1889])).

fof(f2684,plain,
    ( spl6_334
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f1932,f1868,f2682])).

fof(f2682,plain,
    ( spl6_334
  <=> m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(k3_subset_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_334])])).

fof(f1868,plain,
    ( spl6_254
  <=> r1_tarski(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_254])])).

fof(f1932,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(k3_subset_1(sK2,sK3)))
    | ~ spl6_254 ),
    inference(unit_resulting_resolution,[],[f1869,f118])).

fof(f1869,plain,
    ( r1_tarski(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK3))
    | ~ spl6_254 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f2677,plain,
    ( spl6_332
    | ~ spl6_252 ),
    inference(avatar_split_clause,[],[f1927,f1861,f2675])).

fof(f2675,plain,
    ( spl6_332
  <=> m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(k2_pre_topc(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_332])])).

fof(f1861,plain,
    ( spl6_252
  <=> r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_252])])).

fof(f1927,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(k2_pre_topc(sK0,sK3)))
    | ~ spl6_252 ),
    inference(unit_resulting_resolution,[],[f1862,f118])).

fof(f1862,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK3))
    | ~ spl6_252 ),
    inference(avatar_component_clause,[],[f1861])).

fof(f2667,plain,
    ( ~ spl6_331
    | ~ spl6_22
    | spl6_171 ),
    inference(avatar_split_clause,[],[f2651,f1149,f220,f2665])).

fof(f1149,plain,
    ( spl6_171
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).

fof(f2651,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_22
    | ~ spl6_171 ),
    inference(unit_resulting_resolution,[],[f1150,f2649])).

fof(f1150,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_171 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f2660,plain,
    ( spl6_328
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f574,f149,f2658])).

fof(f2658,plain,
    ( spl6_328
  <=> m1_subset_1(k1_tops_1(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_328])])).

fof(f574,plain,
    ( m1_subset_1(k1_tops_1(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f150,f103,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',dt_k1_tops_1)).

fof(f2646,plain,
    ( ~ spl6_327
    | ~ spl6_22
    | spl6_171 ),
    inference(avatar_split_clause,[],[f1364,f1149,f220,f2644])).

fof(f1364,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2))))
    | ~ spl6_22
    | ~ spl6_171 ),
    inference(unit_resulting_resolution,[],[f1150,f221,f121])).

fof(f2639,plain,
    ( ~ spl6_325
    | spl6_171 ),
    inference(avatar_split_clause,[],[f1174,f1149,f2637])).

fof(f2637,plain,
    ( spl6_325
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_325])])).

fof(f1174,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_tops_1(sK0,sK2)))))
    | ~ spl6_171 ),
    inference(unit_resulting_resolution,[],[f103,f1150,f121])).

fof(f2626,plain,
    ( spl6_322
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f548,f149,f2624])).

fof(f2624,plain,
    ( spl6_322
  <=> m1_subset_1(k2_pre_topc(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_322])])).

fof(f548,plain,
    ( m1_subset_1(k2_pre_topc(sK5,sK4(k1_zfmisc_1(u1_struct_0(sK5)))),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f150,f103,f113])).

fof(f2619,plain,
    ( spl6_320
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f551,f543,f2617])).

fof(f543,plain,
    ( spl6_74
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f551,plain,
    ( m1_subset_1(k3_subset_1(sK2,k1_tops_1(sK0,sK2)),k1_zfmisc_1(sK2))
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f544,f107])).

fof(f544,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f543])).

fof(f2585,plain,
    ( spl6_318
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_214 ),
    inference(avatar_split_clause,[],[f1651,f1565,f135,f128,f2583])).

fof(f2583,plain,
    ( spl6_318
  <=> v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_318])])).

fof(f128,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1651,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK3)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_214 ),
    inference(unit_resulting_resolution,[],[f129,f136,f1566,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',fc9_tops_1)).

fof(f129,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f128])).

fof(f2578,plain,
    ( spl6_316
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_202 ),
    inference(avatar_split_clause,[],[f1598,f1484,f135,f128,f2576])).

fof(f2576,plain,
    ( spl6_316
  <=> v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_316])])).

fof(f1598,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_202 ),
    inference(unit_resulting_resolution,[],[f129,f136,f1485,f112])).

fof(f2571,plain,
    ( spl6_314
    | ~ spl6_190 ),
    inference(avatar_split_clause,[],[f1457,f1257,f2569])).

fof(f2569,plain,
    ( spl6_314
  <=> m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_314])])).

fof(f1257,plain,
    ( spl6_190
  <=> r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_190])])).

fof(f1457,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(k2_pre_topc(sK0,sK2)))
    | ~ spl6_190 ),
    inference(unit_resulting_resolution,[],[f1258,f118])).

fof(f1258,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK2))
    | ~ spl6_190 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f2564,plain,
    ( spl6_312
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_72
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1388,f1168,f536,f135,f128,f2562])).

fof(f2562,plain,
    ( spl6_312
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_312])])).

fof(f1388,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_72
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f129,f136,f537,f1169,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',fc3_tops_1)).

fof(f2541,plain,
    ( ~ spl6_311
    | spl6_63 ),
    inference(avatar_split_clause,[],[f493,f489,f2539])).

fof(f2539,plain,
    ( spl6_311
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_311])])).

fof(f489,plain,
    ( spl6_63
  <=> ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f493,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_63 ),
    inference(unit_resulting_resolution,[],[f103,f490,f121])).

fof(f490,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f489])).

fof(f2520,plain,
    ( ~ spl6_309
    | ~ spl6_304 ),
    inference(avatar_split_clause,[],[f2495,f2489,f2518])).

fof(f2518,plain,
    ( spl6_309
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_309])])).

fof(f2489,plain,
    ( spl6_304
  <=> r2_hidden(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_304])])).

fof(f2495,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(k1_tops_1(sK0,sK2)))
    | ~ spl6_304 ),
    inference(unit_resulting_resolution,[],[f2490,f104])).

fof(f2490,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_304 ),
    inference(avatar_component_clause,[],[f2489])).

fof(f2513,plain,
    ( spl6_306
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f573,f135,f2511])).

fof(f2511,plain,
    ( spl6_306
  <=> m1_subset_1(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_306])])).

fof(f573,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f136,f103,f114])).

fof(f2491,plain,
    ( spl6_304
    | spl6_87
    | ~ spl6_300 ),
    inference(avatar_split_clause,[],[f2483,f2170,f639,f2489])).

fof(f639,plain,
    ( spl6_87
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f2170,plain,
    ( spl6_300
  <=> m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_300])])).

fof(f2483,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_87
    | ~ spl6_300 ),
    inference(unit_resulting_resolution,[],[f640,f2171,f106])).

fof(f2171,plain,
    ( m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_300 ),
    inference(avatar_component_clause,[],[f2170])).

fof(f640,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f639])).

fof(f2482,plain,
    ( spl6_300
    | ~ spl6_8
    | ~ spl6_296 ),
    inference(avatar_split_clause,[],[f2140,f2137,f156,f2170])).

fof(f2137,plain,
    ( spl6_296
  <=> r2_hidden(sK4(k1_tops_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_296])])).

fof(f2140,plain,
    ( m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_296 ),
    inference(unit_resulting_resolution,[],[f157,f2138,f121])).

fof(f2138,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),sK2)
    | ~ spl6_296 ),
    inference(avatar_component_clause,[],[f2137])).

fof(f2481,plain,
    ( spl6_302
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f547,f135,f2479])).

fof(f2479,plain,
    ( spl6_302
  <=> m1_subset_1(k2_pre_topc(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_302])])).

fof(f547,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f136,f103,f113])).

fof(f2294,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_53
    | ~ spl6_204 ),
    inference(avatar_contradiction_clause,[],[f2293])).

fof(f2293,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_53
    | ~ spl6_204 ),
    inference(subsumption_resolution,[],[f2244,f422])).

fof(f422,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl6_53
  <=> ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f2244,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_204 ),
    inference(backward_demodulation,[],[f2196,f1502])).

fof(f2196,plain,
    ( k1_tops_1(sK0,sK2) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f235,f161])).

fof(f2289,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_51
    | ~ spl6_74 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_51
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f2221,f410])).

fof(f410,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl6_51
  <=> ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f2221,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_74 ),
    inference(backward_demodulation,[],[f2196,f544])).

fof(f2287,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_43
    | ~ spl6_72 ),
    inference(avatar_contradiction_clause,[],[f2286])).

fof(f2286,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_43
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f2220,f375])).

fof(f375,plain,
    ( ~ v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_43
  <=> ~ v3_pre_topc(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f2220,plain,
    ( v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_72 ),
    inference(backward_demodulation,[],[f2196,f537])).

fof(f2285,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | spl6_45
    | ~ spl6_66 ),
    inference(avatar_contradiction_clause,[],[f2284])).

fof(f2284,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_45
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f2218,f386])).

fof(f386,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK2)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl6_45
  <=> ~ r1_tarski(o_0_0_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f2218,plain,
    ( r1_tarski(o_0_0_xboole_0,sK2)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f2196,f511])).

fof(f2283,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_58
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f2282])).

fof(f2282,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_58
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f2217,f467])).

fof(f2217,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f2196,f501])).

fof(f501,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),o_0_0_xboole_0)
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl6_65
  <=> ~ r1_tarski(k1_tops_1(sK0,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f2281,plain,
    ( ~ spl6_4
    | ~ spl6_24
    | ~ spl6_60
    | spl6_63 ),
    inference(avatar_contradiction_clause,[],[f2280])).

fof(f2280,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_60
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f2215,f478])).

fof(f478,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl6_60
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f2215,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_24
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f2196,f490])).

fof(f2174,plain,
    ( ~ spl6_8
    | ~ spl6_296
    | spl6_301 ),
    inference(avatar_contradiction_clause,[],[f2173])).

fof(f2173,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_296
    | ~ spl6_301 ),
    inference(subsumption_resolution,[],[f2168,f2140])).

fof(f2168,plain,
    ( ~ m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_301 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f2167,plain,
    ( spl6_301
  <=> ~ m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_301])])).

fof(f2172,plain,
    ( spl6_300
    | ~ spl6_32
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f2109,f1168,f283,f2170])).

fof(f2109,plain,
    ( m1_subset_1(sK4(k1_tops_1(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl6_32
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f1169,f284,f121])).

fof(f2165,plain,
    ( ~ spl6_299
    | ~ spl6_296 ),
    inference(avatar_split_clause,[],[f2145,f2137,f2163])).

fof(f2163,plain,
    ( spl6_299
  <=> ~ r2_hidden(sK2,sK4(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_299])])).

fof(f2145,plain,
    ( ~ r2_hidden(sK2,sK4(k1_tops_1(sK0,sK2)))
    | ~ spl6_296 ),
    inference(unit_resulting_resolution,[],[f2138,f104])).

fof(f2139,plain,
    ( spl6_296
    | spl6_77
    | ~ spl6_294 ),
    inference(avatar_split_clause,[],[f2131,f2127,f559,f2137])).

fof(f559,plain,
    ( spl6_77
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2127,plain,
    ( spl6_294
  <=> m1_subset_1(sK4(k1_tops_1(sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_294])])).

fof(f2131,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),sK2)
    | ~ spl6_77
    | ~ spl6_294 ),
    inference(unit_resulting_resolution,[],[f560,f2128,f106])).

fof(f2128,plain,
    ( m1_subset_1(sK4(k1_tops_1(sK0,sK2)),sK2)
    | ~ spl6_294 ),
    inference(avatar_component_clause,[],[f2127])).

fof(f560,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f559])).

fof(f2129,plain,
    ( spl6_294
    | ~ spl6_32
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f2110,f543,f283,f2127])).

fof(f2110,plain,
    ( m1_subset_1(sK4(k1_tops_1(sK0,sK2)),sK2)
    | ~ spl6_32
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f544,f284,f121])).

fof(f2105,plain,
    ( ~ spl6_293
    | spl6_283 ),
    inference(avatar_split_clause,[],[f2044,f2038,f2103])).

fof(f2103,plain,
    ( spl6_293
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_293])])).

fof(f2038,plain,
    ( spl6_283
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_283])])).

fof(f2044,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_283 ),
    inference(unit_resulting_resolution,[],[f2039,f105])).

fof(f2039,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_283 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f2096,plain,
    ( spl6_290
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_186
    | ~ spl6_268 ),
    inference(avatar_split_clause,[],[f2081,f1922,f1232,f135,f128,f2094])).

fof(f2094,plain,
    ( spl6_290
  <=> v4_pre_topc(k2_pre_topc(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_290])])).

fof(f1232,plain,
    ( spl6_186
  <=> m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f1922,plain,
    ( spl6_268
  <=> k2_pre_topc(sK0,sK3) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_268])])).

fof(f2081,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK3),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_186
    | ~ spl6_268 ),
    inference(unit_resulting_resolution,[],[f136,f129,f1233,f1923,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1923,plain,
    ( k2_pre_topc(sK0,sK3) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK3))
    | ~ spl6_268 ),
    inference(avatar_component_clause,[],[f1922])).

fof(f1233,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_186 ),
    inference(avatar_component_clause,[],[f1232])).

fof(f2080,plain,
    ( ~ spl6_289
    | spl6_147 ),
    inference(avatar_split_clause,[],[f1050,f1025,f2078])).

fof(f2078,plain,
    ( spl6_289
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_289])])).

fof(f1025,plain,
    ( spl6_147
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f1050,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_147 ),
    inference(unit_resulting_resolution,[],[f103,f1026,f121])).

fof(f1026,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_147 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f2070,plain,
    ( ~ spl6_287
    | spl6_283 ),
    inference(avatar_split_clause,[],[f2041,f2038,f2068])).

fof(f2068,plain,
    ( spl6_287
  <=> ~ r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_287])])).

fof(f2041,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_tops_1(sK0,sK2))
    | ~ spl6_283 ),
    inference(unit_resulting_resolution,[],[f2039,f118])).

fof(f2061,plain,
    ( spl6_284
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_164
    | ~ spl6_258 ),
    inference(avatar_split_clause,[],[f2046,f1882,f1128,f135,f128,f2059])).

fof(f2059,plain,
    ( spl6_284
  <=> v4_pre_topc(k2_pre_topc(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_284])])).

fof(f1128,plain,
    ( spl6_164
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_164])])).

fof(f1882,plain,
    ( spl6_258
  <=> k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_258])])).

fof(f2046,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK2),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_164
    | ~ spl6_258 ),
    inference(unit_resulting_resolution,[],[f136,f129,f1129,f1883,f101])).

fof(f1883,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl6_258 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f1129,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_164 ),
    inference(avatar_component_clause,[],[f1128])).

fof(f2040,plain,
    ( ~ spl6_283
    | spl6_27
    | ~ spl6_120 ),
    inference(avatar_split_clause,[],[f907,f870,f241,f2038])).

fof(f241,plain,
    ( spl6_27
  <=> ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f870,plain,
    ( spl6_120
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f907,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_27
    | ~ spl6_120 ),
    inference(unit_resulting_resolution,[],[f871,f242,f121])).

fof(f242,plain,
    ( ~ m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f241])).

fof(f871,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_120 ),
    inference(avatar_component_clause,[],[f870])).

fof(f2012,plain,
    ( ~ spl6_281
    | spl6_133 ),
    inference(avatar_split_clause,[],[f946,f935,f2010])).

fof(f2010,plain,
    ( spl6_281
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_281])])).

fof(f935,plain,
    ( spl6_133
  <=> ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f946,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_133 ),
    inference(unit_resulting_resolution,[],[f103,f936,f121])).

fof(f936,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f935])).

fof(f1988,plain,
    ( spl6_278
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f1951,f1088,f1986])).

fof(f1951,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),sK4(k1_zfmisc_1(sK3)))
    | ~ spl6_158 ),
    inference(forward_demodulation,[],[f1948,f471])).

fof(f471,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,sK4(k1_zfmisc_1(X0)))) = sK4(k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f103,f108])).

fof(f1948,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,k3_subset_1(sK3,sK4(k1_zfmisc_1(sK3)))))
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f1089,f413,f1744,f109])).

fof(f1976,plain,
    ( spl6_276
    | ~ spl6_156
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f1095,f1088,f1077,f1974])).

fof(f1077,plain,
    ( spl6_156
  <=> r1_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f1095,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),k3_subset_1(sK3,sK3))
    | ~ spl6_156
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f1078,f1089,f1089,f109])).

fof(f1078,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl6_156 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f1969,plain,
    ( spl6_274
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f821,f618,f204,f156,f1967])).

fof(f204,plain,
    ( spl6_18
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f821,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f205,f619,f157,f109])).

fof(f205,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1962,plain,
    ( spl6_272
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f1093,f1088,f1960])).

fof(f1093,plain,
    ( k3_subset_1(sK3,k3_subset_1(sK3,sK3)) = sK3
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f1089,f108])).

fof(f1944,plain,
    ( spl6_270
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f755,f156,f135,f1942])).

fof(f1942,plain,
    ( spl6_270
  <=> k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_270])])).

fof(f755,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',projectivity_k1_tops_1)).

fof(f1924,plain,
    ( spl6_268
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f720,f618,f135,f1922])).

fof(f720,plain,
    ( k2_pre_topc(sK0,sK3) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK3))
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f136,f619,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',projectivity_k2_pre_topc)).

fof(f1912,plain,
    ( spl6_266
    | ~ spl6_214 ),
    inference(avatar_split_clause,[],[f1658,f1565,f1910])).

fof(f1910,plain,
    ( spl6_266
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_266])])).

fof(f1658,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK3),u1_struct_0(sK0))
    | ~ spl6_214 ),
    inference(unit_resulting_resolution,[],[f1566,f117])).

fof(f1905,plain,
    ( spl6_264
    | ~ spl6_202 ),
    inference(avatar_split_clause,[],[f1605,f1484,f1903])).

fof(f1903,plain,
    ( spl6_264
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_264])])).

fof(f1605,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ spl6_202 ),
    inference(unit_resulting_resolution,[],[f1485,f117])).

fof(f1898,plain,
    ( spl6_262
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f1418,f1232,f135,f128,f1896])).

fof(f1896,plain,
    ( spl6_262
  <=> v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_262])])).

fof(f1418,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK3)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_186 ),
    inference(unit_resulting_resolution,[],[f129,f136,f1233,f112])).

fof(f1891,plain,
    ( spl6_260
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1403,f1168,f156,f135,f1889])).

fof(f1403,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_174 ),
    inference(forward_demodulation,[],[f1385,f755])).

fof(f1385,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f136,f1169,f98])).

fof(f1884,plain,
    ( spl6_258
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f719,f156,f135,f1882])).

fof(f719,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f115])).

fof(f1877,plain,
    ( spl6_256
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_164 ),
    inference(avatar_split_clause,[],[f1353,f1128,f135,f128,f1875])).

fof(f1875,plain,
    ( spl6_256
  <=> v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_256])])).

fof(f1353,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_164 ),
    inference(unit_resulting_resolution,[],[f129,f136,f1129,f112])).

fof(f1870,plain,
    ( spl6_254
    | ~ spl6_20
    | ~ spl6_156 ),
    inference(avatar_split_clause,[],[f1082,f1077,f210,f1868])).

fof(f1082,plain,
    ( r1_tarski(k3_subset_1(sK2,sK3),k3_subset_1(sK2,sK3))
    | ~ spl6_20
    | ~ spl6_156 ),
    inference(unit_resulting_resolution,[],[f211,f211,f1078,f109])).

fof(f1863,plain,
    ( spl6_252
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_156 ),
    inference(avatar_split_clause,[],[f1080,f1077,f618,f135,f1861])).

fof(f1080,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_156 ),
    inference(unit_resulting_resolution,[],[f136,f619,f619,f1078,f102])).

fof(f1856,plain,
    ( ~ spl6_251
    | spl6_27 ),
    inference(avatar_split_clause,[],[f908,f241,f1854])).

fof(f1854,plain,
    ( spl6_251
  <=> ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_tops_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_251])])).

fof(f908,plain,
    ( ~ r2_hidden(sK1,sK4(k1_zfmisc_1(k1_tops_1(sK0,sK2))))
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f103,f242,f121])).

fof(f1849,plain,
    ( spl6_248
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f660,f210,f1847])).

fof(f1847,plain,
    ( spl6_248
  <=> k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).

fof(f660,plain,
    ( k3_subset_1(sK2,k3_subset_1(sK2,sK3)) = sK3
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f211,f108])).

fof(f1842,plain,
    ( spl6_246
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f655,f618,f1840])).

fof(f1840,plain,
    ( spl6_246
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_246])])).

fof(f655,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) = sK3
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f619,f108])).

fof(f1835,plain,
    ( ~ spl6_245
    | ~ spl6_234 ),
    inference(avatar_split_clause,[],[f1812,f1785,f1833])).

fof(f1833,plain,
    ( spl6_245
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_245])])).

fof(f1785,plain,
    ( spl6_234
  <=> r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_234])])).

fof(f1812,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(u1_struct_0(sK0)))
    | ~ spl6_234 ),
    inference(unit_resulting_resolution,[],[f1786,f104])).

fof(f1786,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_234 ),
    inference(avatar_component_clause,[],[f1785])).

fof(f1825,plain,
    ( spl6_242
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f470,f156,f1823])).

fof(f1823,plain,
    ( spl6_242
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_242])])).

fof(f470,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f157,f108])).

fof(f1808,plain,
    ( ~ spl6_241
    | spl6_25
    | spl6_221 ),
    inference(avatar_split_clause,[],[f1627,f1586,f237,f1806])).

fof(f1586,plain,
    ( spl6_221
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_221])])).

fof(f1627,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_25
    | ~ spl6_221 ),
    inference(unit_resulting_resolution,[],[f238,f1587,f106])).

fof(f1587,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_221 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f1801,plain,
    ( ~ spl6_239
    | spl6_213 ),
    inference(avatar_split_clause,[],[f1614,f1558,f1799])).

fof(f1799,plain,
    ( spl6_239
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_239])])).

fof(f1558,plain,
    ( spl6_213
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_213])])).

fof(f1614,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_213 ),
    inference(unit_resulting_resolution,[],[f1559,f105])).

fof(f1559,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_213 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f1794,plain,
    ( ~ spl6_237
    | spl6_113 ),
    inference(avatar_split_clause,[],[f850,f831,f1792])).

fof(f1792,plain,
    ( spl6_237
  <=> ~ r2_hidden(sK2,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_237])])).

fof(f831,plain,
    ( spl6_113
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_113])])).

fof(f850,plain,
    ( ~ r2_hidden(sK2,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_113 ),
    inference(unit_resulting_resolution,[],[f103,f832,f121])).

fof(f832,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_113 ),
    inference(avatar_component_clause,[],[f831])).

fof(f1787,plain,
    ( spl6_234
    | spl6_87 ),
    inference(avatar_split_clause,[],[f649,f639,f1785])).

fof(f649,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_87 ),
    inference(unit_resulting_resolution,[],[f103,f640,f106])).

fof(f1734,plain,
    ( spl6_232
    | ~ spl6_4
    | ~ spl6_230 ),
    inference(avatar_split_clause,[],[f1693,f1672,f142,f1732])).

fof(f1732,plain,
    ( spl6_232
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).

fof(f1674,plain,
    ( spl6_230
    | ~ spl6_4
    | ~ spl6_226 ),
    inference(avatar_split_clause,[],[f1667,f1632,f142,f1672])).

fof(f1632,plain,
    ( spl6_226
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_226])])).

fof(f1667,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_226 ),
    inference(unit_resulting_resolution,[],[f103,f1639,f106])).

fof(f1639,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_226 ),
    inference(unit_resulting_resolution,[],[f143,f1633,f122])).

fof(f1633,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_226 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f1647,plain,
    ( spl6_228
    | ~ spl6_226 ),
    inference(avatar_split_clause,[],[f1637,f1632,f1645])).

fof(f1645,plain,
    ( spl6_228
  <=> r1_tarski(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_228])])).

fof(f1637,plain,
    ( r1_tarski(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),o_0_0_xboole_0)
    | ~ spl6_226 ),
    inference(unit_resulting_resolution,[],[f1633,f117])).

fof(f1634,plain,
    ( spl6_226
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f482,f477,f1632])).

fof(f482,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_60 ),
    inference(unit_resulting_resolution,[],[f478,f107])).

fof(f1622,plain,
    ( ~ spl6_225
    | spl6_213 ),
    inference(avatar_split_clause,[],[f1612,f1558,f1620])).

fof(f1620,plain,
    ( spl6_225
  <=> ~ r1_tarski(sK2,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_225])])).

fof(f1612,plain,
    ( ~ r1_tarski(sK2,k1_tops_1(sK0,sK2))
    | ~ spl6_213 ),
    inference(unit_resulting_resolution,[],[f1559,f118])).

fof(f1595,plain,
    ( ~ spl6_223
    | ~ spl6_206 ),
    inference(avatar_split_clause,[],[f1532,f1508,f1593])).

fof(f1593,plain,
    ( spl6_223
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_223])])).

fof(f1532,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK2,sK3))
    | ~ spl6_206 ),
    inference(unit_resulting_resolution,[],[f1509,f104])).

fof(f1588,plain,
    ( ~ spl6_221
    | ~ spl6_204 ),
    inference(avatar_split_clause,[],[f1515,f1501,f1586])).

fof(f1515,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_tops_1(sK0,sK2))
    | ~ spl6_204 ),
    inference(unit_resulting_resolution,[],[f1502,f104])).

fof(f1581,plain,
    ( ~ spl6_219
    | ~ spl6_192 ),
    inference(avatar_split_clause,[],[f1490,f1264,f1579])).

fof(f1579,plain,
    ( spl6_219
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_219])])).

fof(f1490,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(sK2)))
    | ~ spl6_192 ),
    inference(unit_resulting_resolution,[],[f1265,f104])).

fof(f1574,plain,
    ( ~ spl6_217
    | spl6_107
    | ~ spl6_180 ),
    inference(avatar_split_clause,[],[f1241,f1207,f774,f1572])).

fof(f1572,plain,
    ( spl6_217
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_217])])).

fof(f1241,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k3_subset_1(sK3,sK3))
    | ~ spl6_107
    | ~ spl6_180 ),
    inference(unit_resulting_resolution,[],[f775,f1208,f121])).

fof(f1567,plain,
    ( spl6_214
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f657,f618,f1565])).

fof(f1560,plain,
    ( ~ spl6_213
    | spl6_27
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f906,f579,f241,f1558])).

fof(f906,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_27
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f580,f242,f121])).

fof(f1553,plain,
    ( ~ spl6_211
    | spl6_107 ),
    inference(avatar_split_clause,[],[f798,f774,f1551])).

fof(f798,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK4(k1_zfmisc_1(sK3)))
    | ~ spl6_107 ),
    inference(unit_resulting_resolution,[],[f103,f775,f121])).

fof(f1528,plain,
    ( spl6_208
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f531,f135,f128,f1526])).

fof(f1526,plain,
    ( spl6_208
  <=> v3_pre_topc(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).

fof(f531,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK4(k1_zfmisc_1(u1_struct_0(sK0)))),sK0)
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f129,f136,f103,f112])).

fof(f1510,plain,
    ( spl6_206
    | spl6_39
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f1431,f1135,f323,f1508])).

fof(f1135,plain,
    ( spl6_166
  <=> m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_166])])).

fof(f1431,plain,
    ( r2_hidden(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_39
    | ~ spl6_166 ),
    inference(unit_resulting_resolution,[],[f324,f1136,f106])).

fof(f1136,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_166 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f1503,plain,
    ( spl6_204
    | spl6_39
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f1415,f543,f323,f1501])).

fof(f1415,plain,
    ( r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl6_39
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f324,f544,f106])).

fof(f1486,plain,
    ( spl6_202
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f412,f156,f1484])).

fof(f412,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f157,f107])).

fof(f1479,plain,
    ( ~ spl6_201
    | spl6_179 ),
    inference(avatar_split_clause,[],[f1219,f1200,f1477])).

fof(f1477,plain,
    ( spl6_201
  <=> ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_201])])).

fof(f1219,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_179 ),
    inference(unit_resulting_resolution,[],[f1201,f105])).

fof(f1453,plain,
    ( spl6_198
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f1425,f1232,f1451])).

fof(f1451,plain,
    ( spl6_198
  <=> r1_tarski(k2_pre_topc(sK0,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_198])])).

fof(f1425,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3),u1_struct_0(sK0))
    | ~ spl6_186 ),
    inference(unit_resulting_resolution,[],[f1233,f117])).

fof(f1446,plain,
    ( spl6_196
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1398,f1168,f1444])).

fof(f1444,plain,
    ( spl6_196
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_196])])).

fof(f1398,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl6_174 ),
    inference(unit_resulting_resolution,[],[f1169,f117])).

fof(f1439,plain,
    ( spl6_194
    | ~ spl6_164 ),
    inference(avatar_split_clause,[],[f1360,f1128,f1437])).

fof(f1437,plain,
    ( spl6_194
  <=> r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_194])])).

fof(f1360,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ spl6_164 ),
    inference(unit_resulting_resolution,[],[f1129,f117])).

fof(f1317,plain,
    ( ~ spl6_4
    | ~ spl6_38
    | ~ spl6_58
    | spl6_137 ),
    inference(avatar_contradiction_clause,[],[f1316])).

fof(f1316,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_58
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f1301,f467])).

fof(f1301,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_137 ),
    inference(backward_demodulation,[],[f1283,f954])).

fof(f954,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl6_137 ),
    inference(avatar_component_clause,[],[f953])).

fof(f953,plain,
    ( spl6_137
  <=> ~ r1_tarski(k1_zfmisc_1(sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f1283,plain,
    ( k1_zfmisc_1(sK2) = o_0_0_xboole_0
    | ~ spl6_4
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f327,f161])).

fof(f1315,plain,
    ( ~ spl6_4
    | ~ spl6_38
    | ~ spl6_60
    | spl6_133 ),
    inference(avatar_contradiction_clause,[],[f1314])).

fof(f1314,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_60
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f1299,f478])).

fof(f1299,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_38
    | ~ spl6_133 ),
    inference(backward_demodulation,[],[f1283,f936])).

fof(f1268,plain,
    ( ~ spl6_22
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f1267])).

fof(f1267,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f327,f704])).

fof(f704,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_22 ),
    inference(resolution,[],[f221,f120])).

fof(f1266,plain,
    ( spl6_192
    | spl6_39 ),
    inference(avatar_split_clause,[],[f331,f323,f1264])).

fof(f331,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK2)),k1_zfmisc_1(sK2))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f103,f324,f106])).

fof(f1259,plain,
    ( spl6_190
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f959,f618,f204,f156,f135,f1257])).

fof(f959,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK3),k2_pre_topc(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f136,f205,f619,f157,f102])).

fof(f1249,plain,
    ( spl6_188
    | ~ spl6_180 ),
    inference(avatar_split_clause,[],[f1240,f1207,f1247])).

fof(f1240,plain,
    ( r1_tarski(k3_subset_1(sK3,sK3),sK3)
    | ~ spl6_180 ),
    inference(unit_resulting_resolution,[],[f1208,f117])).

fof(f1234,plain,
    ( spl6_186
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f652,f618,f135,f1232])).

fof(f652,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f136,f619,f113])).

fof(f1227,plain,
    ( ~ spl6_185
    | spl6_179 ),
    inference(avatar_split_clause,[],[f1217,f1200,f1225])).

fof(f1217,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_179 ),
    inference(unit_resulting_resolution,[],[f1201,f118])).

fof(f1216,plain,
    ( ~ spl6_183
    | spl6_171 ),
    inference(avatar_split_clause,[],[f1175,f1149,f1214])).

fof(f1214,plain,
    ( spl6_183
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).

fof(f1175,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_171 ),
    inference(unit_resulting_resolution,[],[f1150,f105])).

fof(f1209,plain,
    ( spl6_180
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f1092,f1088,f1207])).

fof(f1092,plain,
    ( m1_subset_1(k3_subset_1(sK3,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_158 ),
    inference(unit_resulting_resolution,[],[f1089,f107])).

fof(f1202,plain,
    ( ~ spl6_179
    | ~ spl6_22
    | spl6_91 ),
    inference(avatar_split_clause,[],[f694,f670,f220,f1200])).

fof(f694,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_22
    | ~ spl6_91 ),
    inference(unit_resulting_resolution,[],[f671,f221,f121])).

fof(f1183,plain,
    ( ~ spl6_177
    | spl6_171 ),
    inference(avatar_split_clause,[],[f1172,f1149,f1181])).

fof(f1172,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ spl6_171 ),
    inference(unit_resulting_resolution,[],[f1150,f118])).

fof(f1170,plain,
    ( spl6_174
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f572,f156,f135,f1168])).

fof(f572,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f114])).

fof(f1163,plain,
    ( spl6_172
    | ~ spl6_166 ),
    inference(avatar_split_clause,[],[f1154,f1135,f1161])).

fof(f1161,plain,
    ( spl6_172
  <=> r1_tarski(k3_subset_1(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).

fof(f1154,plain,
    ( r1_tarski(k3_subset_1(sK2,sK3),sK2)
    | ~ spl6_166 ),
    inference(unit_resulting_resolution,[],[f1136,f117])).

fof(f1151,plain,
    ( ~ spl6_171
    | spl6_27
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f905,f270,f241,f1149])).

fof(f905,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
    | ~ spl6_27
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f242,f121])).

fof(f1144,plain,
    ( ~ spl6_169
    | spl6_91 ),
    inference(avatar_split_clause,[],[f681,f670,f1142])).

fof(f1142,plain,
    ( spl6_169
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).

fof(f681,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_91 ),
    inference(unit_resulting_resolution,[],[f103,f671,f121])).

fof(f1137,plain,
    ( spl6_166
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f662,f210,f1135])).

fof(f662,plain,
    ( m1_subset_1(k3_subset_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f211,f107])).

fof(f1130,plain,
    ( spl6_164
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f546,f156,f135,f1128])).

fof(f546,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f113])).

fof(f1118,plain,
    ( ~ spl6_163
    | spl6_147 ),
    inference(avatar_split_clause,[],[f1051,f1025,f1116])).

fof(f1116,plain,
    ( spl6_163
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_163])])).

fof(f1051,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_147 ),
    inference(unit_resulting_resolution,[],[f1026,f105])).

fof(f1108,plain,
    ( spl6_160
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148 ),
    inference(avatar_split_clause,[],[f1067,f1032,f618,f135,f1106])).

fof(f1106,plain,
    ( spl6_160
  <=> k1_tops_1(sK0,sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_160])])).

fof(f1067,plain,
    ( k1_tops_1(sK0,sK3) = sK3
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148 ),
    inference(forward_demodulation,[],[f1066,f655])).

fof(f1066,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_148 ),
    inference(backward_demodulation,[],[f1065,f926])).

fof(f926,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f136,f619,f99])).

fof(f1090,plain,
    ( spl6_158
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_130
    | ~ spl6_148 ),
    inference(avatar_split_clause,[],[f1068,f1032,f921,f618,f135,f1088])).

fof(f921,plain,
    ( spl6_130
  <=> r1_tarski(k1_tops_1(sK0,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f1068,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_130
    | ~ spl6_148 ),
    inference(backward_demodulation,[],[f1067,f924])).

fof(f924,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(sK3))
    | ~ spl6_130 ),
    inference(unit_resulting_resolution,[],[f922,f118])).

fof(f922,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ spl6_130 ),
    inference(avatar_component_clause,[],[f921])).

fof(f1079,plain,
    ( spl6_156
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_130
    | ~ spl6_148 ),
    inference(avatar_split_clause,[],[f1069,f1032,f921,f618,f135,f1077])).

fof(f1069,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_130
    | ~ spl6_148 ),
    inference(backward_demodulation,[],[f1067,f922])).

fof(f1059,plain,
    ( ~ spl6_155
    | spl6_147 ),
    inference(avatar_split_clause,[],[f1049,f1025,f1057])).

fof(f1057,plain,
    ( spl6_155
  <=> ~ r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f1049,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),o_0_0_xboole_0)
    | ~ spl6_147 ),
    inference(unit_resulting_resolution,[],[f1026,f118])).

fof(f1048,plain,
    ( ~ spl6_153
    | ~ spl6_144 ),
    inference(avatar_split_clause,[],[f1014,f998,f1046])).

fof(f1046,plain,
    ( spl6_153
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).

fof(f998,plain,
    ( spl6_144
  <=> r2_hidden(sK4(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f1014,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(sK2))
    | ~ spl6_144 ),
    inference(unit_resulting_resolution,[],[f999,f104])).

fof(f999,plain,
    ( r2_hidden(sK4(sK2),u1_struct_0(sK0))
    | ~ spl6_144 ),
    inference(avatar_component_clause,[],[f998])).

fof(f1041,plain,
    ( ~ spl6_151
    | ~ spl6_142 ),
    inference(avatar_split_clause,[],[f1004,f991,f1039])).

fof(f1039,plain,
    ( spl6_151
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_151])])).

fof(f991,plain,
    ( spl6_142
  <=> r2_hidden(sK4(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f1004,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(sK3))
    | ~ spl6_142 ),
    inference(unit_resulting_resolution,[],[f992,f104])).

fof(f992,plain,
    ( r2_hidden(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f991])).

fof(f1034,plain,
    ( spl6_148
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f873,f618,f197,f135,f128,f1032])).

fof(f197,plain,
    ( spl6_16
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f873,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f129,f136,f198,f619,f111])).

fof(f198,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1027,plain,
    ( ~ spl6_147
    | ~ spl6_4
    | ~ spl6_120 ),
    inference(avatar_split_clause,[],[f884,f870,f142,f1025])).

fof(f884,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_120 ),
    inference(unit_resulting_resolution,[],[f143,f871,f122])).

fof(f1000,plain,
    ( spl6_144
    | spl6_87
    | ~ spl6_140 ),
    inference(avatar_split_clause,[],[f981,f978,f639,f998])).

fof(f978,plain,
    ( spl6_140
  <=> m1_subset_1(sK4(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f981,plain,
    ( r2_hidden(sK4(sK2),u1_struct_0(sK0))
    | ~ spl6_87
    | ~ spl6_140 ),
    inference(unit_resulting_resolution,[],[f640,f979,f106])).

fof(f979,plain,
    ( m1_subset_1(sK4(sK2),u1_struct_0(sK0))
    | ~ spl6_140 ),
    inference(avatar_component_clause,[],[f978])).

fof(f993,plain,
    ( spl6_142
    | spl6_87
    | ~ spl6_134 ),
    inference(avatar_split_clause,[],[f966,f942,f639,f991])).

fof(f942,plain,
    ( spl6_134
  <=> m1_subset_1(sK4(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_134])])).

fof(f966,plain,
    ( r2_hidden(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_87
    | ~ spl6_134 ),
    inference(unit_resulting_resolution,[],[f640,f943,f106])).

fof(f943,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_134 ),
    inference(avatar_component_clause,[],[f942])).

fof(f980,plain,
    ( spl6_140
    | ~ spl6_8
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f786,f767,f156,f978])).

fof(f767,plain,
    ( spl6_104
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f786,plain,
    ( m1_subset_1(sK4(sK2),u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_104 ),
    inference(unit_resulting_resolution,[],[f157,f768,f121])).

fof(f768,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f767])).

fof(f973,plain,
    ( ~ spl6_139
    | spl6_133 ),
    inference(avatar_split_clause,[],[f947,f935,f971])).

fof(f947,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_133 ),
    inference(unit_resulting_resolution,[],[f936,f105])).

fof(f955,plain,
    ( ~ spl6_137
    | spl6_133 ),
    inference(avatar_split_clause,[],[f945,f935,f953])).

fof(f945,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK2),o_0_0_xboole_0)
    | ~ spl6_133 ),
    inference(unit_resulting_resolution,[],[f936,f118])).

fof(f944,plain,
    ( spl6_134
    | ~ spl6_40
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f705,f618,f347,f942])).

fof(f705,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl6_40
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f619,f348,f121])).

fof(f937,plain,
    ( ~ spl6_133
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f695,f220,f142,f935])).

fof(f695,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f143,f221,f122])).

fof(f923,plain,
    ( spl6_130
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f654,f618,f135,f921])).

fof(f654,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),sK3)
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f136,f619,f98])).

fof(f916,plain,
    ( spl6_128
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f653,f618,f135,f128,f914])).

fof(f914,plain,
    ( spl6_128
  <=> v3_pre_topc(k1_tops_1(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f653,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f129,f136,f619,f112])).

fof(f904,plain,
    ( ~ spl6_15
    | spl6_126 ),
    inference(avatar_split_clause,[],[f93,f902,f188])).

fof(f93,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f75,f78,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK1,X3)
              | ~ r1_tarski(X3,sK2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & ( ? [X4] :
              ( r2_hidden(sK1,X4)
              & r1_tarski(X4,sK2)
              & v3_pre_topc(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK1,k1_tops_1(X0,sK2)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3)
        & r1_tarski(sK3,X2)
        & v3_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',t54_tops_1)).

fof(f900,plain,
    ( ~ spl6_125
    | ~ spl6_120 ),
    inference(avatar_split_clause,[],[f887,f870,f898])).

fof(f898,plain,
    ( spl6_125
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_125])])).

fof(f887,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_120 ),
    inference(unit_resulting_resolution,[],[f871,f104])).

fof(f882,plain,
    ( ~ spl6_123
    | spl6_113 ),
    inference(avatar_split_clause,[],[f851,f831,f880])).

fof(f880,plain,
    ( spl6_123
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f851,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_113 ),
    inference(unit_resulting_resolution,[],[f832,f105])).

fof(f872,plain,
    ( spl6_120
    | spl6_87
    | ~ spl6_110 ),
    inference(avatar_split_clause,[],[f848,f816,f639,f870])).

fof(f816,plain,
    ( spl6_110
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f848,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_87
    | ~ spl6_110 ),
    inference(unit_resulting_resolution,[],[f640,f817,f106])).

fof(f817,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f816])).

fof(f862,plain,
    ( ~ spl6_119
    | spl6_113 ),
    inference(avatar_split_clause,[],[f849,f831,f860])).

fof(f860,plain,
    ( spl6_119
  <=> ~ r1_tarski(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f849,plain,
    ( ~ r1_tarski(sK2,o_0_0_xboole_0)
    | ~ spl6_113 ),
    inference(unit_resulting_resolution,[],[f832,f118])).

fof(f847,plain,
    ( ~ spl6_117
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f805,f783,f845])).

fof(f845,plain,
    ( spl6_117
  <=> ~ r2_hidden(sK2,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f805,plain,
    ( ~ r2_hidden(sK2,sK4(sK3))
    | ~ spl6_108 ),
    inference(unit_resulting_resolution,[],[f784,f104])).

fof(f840,plain,
    ( ~ spl6_115
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f791,f767,f838])).

fof(f838,plain,
    ( spl6_115
  <=> ~ r2_hidden(sK2,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f791,plain,
    ( ~ r2_hidden(sK2,sK4(sK2))
    | ~ spl6_104 ),
    inference(unit_resulting_resolution,[],[f768,f104])).

fof(f833,plain,
    ( ~ spl6_113
    | ~ spl6_4
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f624,f579,f142,f831])).

fof(f624,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f143,f580,f122])).

fof(f818,plain,
    ( spl6_110
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f623,f579,f156,f816])).

fof(f623,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f157,f580,f121])).

fof(f785,plain,
    ( spl6_108
    | spl6_77
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f762,f745,f559,f783])).

fof(f745,plain,
    ( spl6_100
  <=> m1_subset_1(sK4(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f762,plain,
    ( r2_hidden(sK4(sK3),sK2)
    | ~ spl6_77
    | ~ spl6_100 ),
    inference(unit_resulting_resolution,[],[f560,f746,f106])).

fof(f746,plain,
    ( m1_subset_1(sK4(sK3),sK2)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f745])).

fof(f776,plain,
    ( ~ spl6_107
    | spl6_35
    | spl6_99 ),
    inference(avatar_split_clause,[],[f761,f738,f298,f774])).

fof(f298,plain,
    ( spl6_35
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f761,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_35
    | ~ spl6_99 ),
    inference(unit_resulting_resolution,[],[f299,f739,f106])).

fof(f299,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f298])).

fof(f769,plain,
    ( spl6_104
    | spl6_77 ),
    inference(avatar_split_clause,[],[f562,f559,f767])).

fof(f562,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl6_77 ),
    inference(unit_resulting_resolution,[],[f103,f560,f106])).

fof(f754,plain,
    ( ~ spl6_103
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f712,f347,f752])).

fof(f752,plain,
    ( spl6_103
  <=> ~ r2_hidden(sK3,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f712,plain,
    ( ~ r2_hidden(sK3,sK4(sK3))
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f348,f104])).

fof(f747,plain,
    ( spl6_100
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f706,f347,f210,f745])).

fof(f706,plain,
    ( m1_subset_1(sK4(sK3),sK2)
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f211,f348,f121])).

fof(f740,plain,
    ( ~ spl6_99
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f698,f220,f738])).

fof(f698,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK2),sK3)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f221,f104])).

fof(f733,plain,
    ( ~ spl6_97
    | spl6_91 ),
    inference(avatar_split_clause,[],[f682,f670,f731])).

fof(f731,plain,
    ( spl6_97
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f682,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_91 ),
    inference(unit_resulting_resolution,[],[f671,f105])).

fof(f690,plain,
    ( ~ spl6_95
    | spl6_91 ),
    inference(avatar_split_clause,[],[f680,f670,f688])).

fof(f680,plain,
    ( ~ r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl6_91 ),
    inference(unit_resulting_resolution,[],[f671,f118])).

fof(f679,plain,
    ( spl6_92
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f659,f618,f677])).

fof(f677,plain,
    ( spl6_92
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f659,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_84 ),
    inference(unit_resulting_resolution,[],[f619,f117])).

fof(f672,plain,
    ( ~ spl6_91
    | ~ spl6_4
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f586,f270,f142,f670])).

fof(f586,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f143,f271,f122])).

fof(f648,plain,
    ( ~ spl6_89
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f628,f579,f646])).

fof(f646,plain,
    ( spl6_89
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f628,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f580,f104])).

fof(f641,plain,
    ( ~ spl6_87
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f625,f579,f156,f639])).

fof(f625,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f157,f580,f122])).

fof(f620,plain,
    ( spl6_14
    | spl6_84 ),
    inference(avatar_split_clause,[],[f89,f618,f191])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f613,plain,
    ( ~ spl6_20
    | ~ spl6_30
    | spl6_79 ),
    inference(avatar_contradiction_clause,[],[f612])).

fof(f612,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_30
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f608,f211])).

fof(f608,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_30
    | ~ spl6_79 ),
    inference(unit_resulting_resolution,[],[f271,f566,f121])).

fof(f566,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl6_79
  <=> ~ m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f604,plain,
    ( ~ spl6_83
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f589,f270,f602])).

fof(f602,plain,
    ( spl6_83
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f589,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f104])).

fof(f581,plain,
    ( spl6_80
    | spl6_77
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f571,f568,f559,f579])).

fof(f568,plain,
    ( spl6_78
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f571,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl6_77
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f560,f569,f106])).

fof(f569,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f568])).

fof(f570,plain,
    ( spl6_78
    | ~ spl6_14
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f550,f543,f191,f568])).

fof(f550,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl6_14
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f192,f544,f121])).

fof(f561,plain,
    ( ~ spl6_77
    | ~ spl6_14
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f552,f543,f191,f559])).

fof(f552,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_14
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f192,f544,f122])).

fof(f545,plain,
    ( spl6_74
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f513,f510,f543])).

fof(f513,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(sK2))
    | ~ spl6_66 ),
    inference(unit_resulting_resolution,[],[f511,f118])).

fof(f538,plain,
    ( spl6_72
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f530,f156,f135,f128,f536])).

fof(f530,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f129,f136,f157,f112])).

fof(f529,plain,
    ( ~ spl6_71
    | spl6_63 ),
    inference(avatar_split_clause,[],[f494,f489,f527])).

fof(f527,plain,
    ( spl6_71
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f494,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_63 ),
    inference(unit_resulting_resolution,[],[f490,f105])).

fof(f522,plain,
    ( ~ spl6_69
    | spl6_51 ),
    inference(avatar_split_clause,[],[f435,f409,f520])).

fof(f520,plain,
    ( spl6_69
  <=> ~ r2_hidden(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f435,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f410,f103,f121])).

fof(f512,plain,
    ( spl6_66
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f503,f156,f135,f510])).

fof(f503,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f136,f157,f98])).

fof(f502,plain,
    ( ~ spl6_65
    | spl6_63 ),
    inference(avatar_split_clause,[],[f492,f489,f500])).

fof(f492,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),o_0_0_xboole_0)
    | ~ spl6_63 ),
    inference(unit_resulting_resolution,[],[f490,f118])).

fof(f491,plain,
    ( ~ spl6_63
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f340,f191,f142,f489])).

fof(f340,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f143,f192,f122])).

fof(f479,plain,
    ( spl6_60
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f461,f457,f477])).

fof(f461,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_56 ),
    inference(superposition,[],[f103,f458])).

fof(f468,plain,
    ( spl6_58
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f460,f457,f466])).

fof(f460,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl6_56 ),
    inference(superposition,[],[f174,f458])).

fof(f459,plain,
    ( spl6_56
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f443,f430,f142,f457])).

fof(f430,plain,
    ( spl6_54
  <=> v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f443,plain,
    ( o_0_0_xboole_0 = sK4(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f431,f161])).

fof(f431,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f430])).

fof(f432,plain,
    ( spl6_54
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f425,f142,f430])).

fof(f425,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f103,f341,f106])).

fof(f341,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f143,f103,f122])).

fof(f423,plain,
    ( ~ spl6_53
    | ~ spl6_4
    | spl6_23
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f364,f295,f223,f142,f421])).

fof(f223,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f295,plain,
    ( spl6_34
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f364,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_4
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f356,f224])).

fof(f224,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f223])).

fof(f356,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f296,f161])).

fof(f296,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f411,plain,
    ( ~ spl6_51
    | ~ spl6_4
    | spl6_21
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f363,f295,f213,f142,f409])).

fof(f213,plain,
    ( spl6_21
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f363,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl6_4
    | ~ spl6_21
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f356,f214])).

fof(f214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f213])).

fof(f404,plain,
    ( spl6_48
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f356,f295,f142,f402])).

fof(f402,plain,
    ( spl6_48
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f396,plain,
    ( ~ spl6_47
    | ~ spl6_4
    | ~ spl6_34
    | spl6_37 ),
    inference(avatar_split_clause,[],[f367,f305,f295,f142,f394])).

fof(f367,plain,
    ( ~ m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f356,f306])).

fof(f387,plain,
    ( ~ spl6_45
    | ~ spl6_4
    | spl6_19
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f362,f295,f201,f142,f385])).

fof(f201,plain,
    ( spl6_19
  <=> ~ r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f362,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK2)
    | ~ spl6_4
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f356,f202])).

fof(f202,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f201])).

fof(f379,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f361,f295,f197,f142,f377])).

fof(f377,plain,
    ( spl6_42
  <=> v3_pre_topc(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f361,plain,
    ( v3_pre_topc(o_0_0_xboole_0,sK0)
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f356,f198])).

fof(f349,plain,
    ( spl6_40
    | spl6_35 ),
    inference(avatar_split_clause,[],[f302,f298,f347])).

fof(f302,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl6_35 ),
    inference(unit_resulting_resolution,[],[f103,f299,f106])).

fof(f328,plain,
    ( spl6_38
    | ~ spl6_20
    | spl6_23 ),
    inference(avatar_split_clause,[],[f314,f223,f210,f326])).

fof(f314,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl6_20
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f224,f211,f106])).

fof(f310,plain,
    ( spl6_36
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f287,f270,f308])).

fof(f308,plain,
    ( spl6_36
  <=> m1_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f287,plain,
    ( m1_subset_1(sK1,sK3)
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f105])).

fof(f300,plain,
    ( ~ spl6_35
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f290,f270,f298])).

fof(f290,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl6_30 ),
    inference(unit_resulting_resolution,[],[f271,f120])).

fof(f285,plain,
    ( spl6_32
    | spl6_25 ),
    inference(avatar_split_clause,[],[f274,f237,f283])).

fof(f274,plain,
    ( r2_hidden(sK4(k1_tops_1(sK0,sK2)),k1_tops_1(sK0,sK2))
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f103,f238,f106])).

fof(f272,plain,
    ( spl6_14
    | spl6_30 ),
    inference(avatar_split_clause,[],[f92,f270,f191])).

fof(f92,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f265,plain,
    ( ~ spl6_29
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f254,f191,f263])).

fof(f263,plain,
    ( spl6_29
  <=> ~ r2_hidden(k1_tops_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f254,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK2),sK1)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f192,f104])).

fof(f249,plain,
    ( ~ spl6_19
    | spl6_21 ),
    inference(avatar_split_clause,[],[f218,f213,f201])).

fof(f218,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl6_21 ),
    inference(resolution,[],[f214,f118])).

fof(f248,plain,
    ( ~ spl6_18
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f205,f218])).

fof(f246,plain,
    ( spl6_26
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f226,f191,f244])).

fof(f226,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f192,f105])).

fof(f239,plain,
    ( ~ spl6_25
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f229,f191,f237])).

fof(f229,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK2))
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f192,f120])).

fof(f225,plain,
    ( ~ spl6_23
    | spl6_21 ),
    inference(avatar_split_clause,[],[f217,f213,f223])).

fof(f217,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f214,f105])).

fof(f215,plain,
    ( ~ spl6_21
    | spl6_19 ),
    inference(avatar_split_clause,[],[f207,f201,f213])).

fof(f207,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f202,f117])).

fof(f206,plain,
    ( spl6_14
    | spl6_18 ),
    inference(avatar_split_clause,[],[f91,f204,f191])).

fof(f91,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f199,plain,
    ( spl6_14
    | spl6_16 ),
    inference(avatar_split_clause,[],[f90,f197,f191])).

fof(f90,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f182,plain,
    ( spl6_12
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f175,f156,f180])).

fof(f180,plain,
    ( spl6_12
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f175,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f157,f117])).

fof(f170,plain,
    ( spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f159,f142,f168])).

fof(f168,plain,
    ( spl6_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f158,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f88,f156])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

fof(f151,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f123,f149])).

fof(f123,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f84])).

fof(f84,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',existence_l1_pre_topc)).

fof(f144,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f94,f142])).

fof(f94,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t54_tops_1.p',dt_o_0_0_xboole_0)).

fof(f137,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f87,f135])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

fof(f130,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f86,f128])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).
%------------------------------------------------------------------------------

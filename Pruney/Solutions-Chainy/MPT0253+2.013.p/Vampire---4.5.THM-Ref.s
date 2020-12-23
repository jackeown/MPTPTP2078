%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:07 EST 2020

% Result     : Theorem 6.13s
% Output     : Refutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :  680 (7902 expanded)
%              Number of leaves         :  132 (2717 expanded)
%              Depth                    :   16
%              Number of atoms          : 1572 (14146 expanded)
%              Number of equality atoms :  135 (5183 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f97,f146,f155,f156,f163,f168,f204,f754,f805,f963,f964,f969,f1213,f1214,f1460,f1466,f1470,f1475,f1498,f1507,f1522,f1531,f1546,f1555,f1564,f1569,f1578,f1583,f1597,f1600,f1605,f1606,f1626,f1631,f1649,f1662,f1667,f1693,f1698,f1699,f1706,f1711,f1773,f1778,f1779,f1781,f1790,f1795,f1805,f1827,f1828,f1874,f2041,f2178,f2181,f2184,f2186,f2187,f2188,f2189,f2233,f2238,f2239,f2240,f2241,f2242,f2245,f2278,f2279,f2280,f2281,f2286,f2289,f2851,f2856,f2861,f2862,f2864,f2866,f2896,f2902,f2905,f2907,f2913,f2914,f2921,f2926,f2935,f2940,f2949,f2969,f2974,f2984,f3005,f3006,f3023,f3211,f3243,f3247,f3261,f3266,f3268,f3323,f3328,f3333,f3338,f3343,f3348,f3353,f3354,f3355,f3360,f3362,f3367,f3369,f3374,f3375,f3376,f3377,f3378,f3387,f3433,f3503,f3549,f3554,f3561,f3562,f3564,f3603,f3625,f3630,f3632,f3637,f3649,f3654,f3668,f3673,f3675,f3676,f3677,f3678,f3679,f3708,f3713,f3719,f3720,f3721,f3891,f3896,f3902,f3903,f3904,f3992,f4000,f4005,f4006,f4008,f4010,f4013,f4014,f4015,f4016,f4017,f4018,f4019,f4023,f4028,f4029,f4114,f4146,f4151,f4152,f4180,f4182,f4188,f4193,f4195,f4202])).

fof(f4202,plain,
    ( spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f4201])).

fof(f4201,plain,
    ( $false
    | spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f4179,f1465])).

fof(f1465,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f1463])).

fof(f1463,plain,
    ( spl5_16
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f4179,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f4178])).

fof(f4178,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl5_4 ),
    inference(superposition,[],[f96,f1983])).

fof(f1983,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f1715,f1912])).

fof(f1912,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[],[f1733,f195])).

fof(f195,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(unit_resulting_resolution,[],[f186,f186,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f177,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f177,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k5_xboole_0(X3,X3)) ),
    inference(subsumption_resolution,[],[f173,f135])).

fof(f135,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f75,f98])).

fof(f98,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f173,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f76,f98])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f32])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1733,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f1714,f98])).

fof(f1714,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f56,f32])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1715,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X0,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f61,f35])).

fof(f96,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_4
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f4195,plain,
    ( spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f4194])).

fof(f4194,plain,
    ( $false
    | spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f4161,f96])).

fof(f4161,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f1465,f1983])).

fof(f4193,plain,
    ( spl5_115
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f4162,f1457,f4190])).

fof(f4190,plain,
    ( spl5_115
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1457,plain,
    ( spl5_15
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f4162,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f1459,f1983])).

fof(f1459,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f1457])).

fof(f4188,plain,
    ( spl5_114
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f4183,f3236,f4185])).

fof(f4185,plain,
    ( spl5_114
  <=> sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f3236,plain,
    ( spl5_72
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f4183,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_72 ),
    inference(forward_demodulation,[],[f4163,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f55,f55])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4163,plain,
    ( sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f3237,f1983])).

fof(f3237,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f3236])).

fof(f4182,plain,
    ( spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f4181])).

fof(f4181,plain,
    ( $false
    | spl5_4
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f4164,f1465])).

fof(f4164,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f96,f1983])).

fof(f4180,plain,
    ( spl5_4
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f4165])).

fof(f4165,plain,
    ( $false
    | spl5_4
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f1465,f96,f1983])).

fof(f4152,plain,
    ( spl5_113
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f4127,f3320,f4148])).

fof(f4148,plain,
    ( spl5_113
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f3320,plain,
    ( spl5_77
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f4127,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | ~ spl5_77 ),
    inference(unit_resulting_resolution,[],[f3322,f3322,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3322,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f3320])).

fof(f4151,plain,
    ( spl5_113
    | ~ spl5_77 ),
    inference(avatar_split_clause,[],[f4128,f3320,f4148])).

fof(f4128,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)
    | ~ spl5_77 ),
    inference(unit_resulting_resolution,[],[f3322,f3322,f69])).

fof(f4146,plain,
    ( spl5_112
    | ~ spl5_77
    | spl5_85 ),
    inference(avatar_split_clause,[],[f4133,f3364,f3320,f4143])).

fof(f4143,plain,
    ( spl5_112
  <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f3364,plain,
    ( spl5_85
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f4133,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | ~ spl5_77
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f3365,f3322,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f49,f32])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3365,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl5_85 ),
    inference(avatar_component_clause,[],[f3364])).

fof(f4114,plain,
    ( spl5_111
    | ~ spl5_72
    | spl5_91 ),
    inference(avatar_split_clause,[],[f4101,f3546,f3236,f4111])).

fof(f4111,plain,
    ( spl5_111
  <=> r2_hidden(sK3(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f3546,plain,
    ( spl5_91
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f4101,plain,
    ( r2_hidden(sK3(sK1,sK0),sK2)
    | ~ spl5_72
    | spl5_91 ),
    inference(unit_resulting_resolution,[],[f3548,f3237,f107])).

fof(f107,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK3(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f39,f40])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3548,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_91 ),
    inference(avatar_component_clause,[],[f3546])).

fof(f4029,plain,
    ( spl5_110
    | spl5_6
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3304,f3236,f152,f4025])).

fof(f4025,plain,
    ( spl5_110
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f152,plain,
    ( spl5_6
  <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3304,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2)
    | spl5_6
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f154,f3237,f107])).

fof(f154,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f4028,plain,
    ( spl5_110
    | ~ spl5_7
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3298,f3236,f160,f4025])).

fof(f160,plain,
    ( spl5_7
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f3298,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2)
    | ~ spl5_7
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f162,f3237,f39])).

fof(f162,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f4023,plain,
    ( ~ spl5_84
    | ~ spl5_89 ),
    inference(avatar_contradiction_clause,[],[f4022])).

fof(f4022,plain,
    ( $false
    | ~ spl5_84
    | ~ spl5_89 ),
    inference(subsumption_resolution,[],[f4021,f177])).

fof(f4021,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl5_84
    | ~ spl5_89 ),
    inference(backward_demodulation,[],[f3432,f3359])).

fof(f3359,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f3357])).

fof(f3357,plain,
    ( spl5_84
  <=> sK1 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f3432,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f3430])).

fof(f3430,plain,
    ( spl5_89
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f4019,plain,
    ( ~ spl5_78
    | ~ spl5_68
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3575,f3371,f2981,f3325])).

fof(f3325,plain,
    ( spl5_78
  <=> r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f2981,plain,
    ( spl5_68
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f3371,plain,
    ( spl5_86
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f3575,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl5_68
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f3372,f3212])).

fof(f3212,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK0) )
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f3201,f177])).

fof(f3201,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k5_xboole_0(sK2,sK2))
        | r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl5_68 ),
    inference(superposition,[],[f74,f2983])).

fof(f2983,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f3372,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl5_86 ),
    inference(avatar_component_clause,[],[f3371])).

fof(f4018,plain,
    ( ~ spl5_78
    | ~ spl5_68
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3916,f3371,f2981,f3325])).

fof(f3916,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl5_68
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f3372,f3212])).

fof(f4017,plain,
    ( ~ spl5_77
    | ~ spl5_68
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3521,f3364,f2981,f3320])).

fof(f3521,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_68
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f3365,f3212])).

fof(f4016,plain,
    ( ~ spl5_77
    | ~ spl5_68
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3827,f3364,f2981,f3320])).

fof(f3827,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_68
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f3365,f3212])).

fof(f4015,plain,
    ( ~ spl5_66
    | spl5_67
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f3230,f2981,f2971,f2966])).

fof(f2966,plain,
    ( spl5_66
  <=> r2_hidden(sK3(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f2971,plain,
    ( spl5_67
  <=> r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f3230,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK2)
    | spl5_67
    | ~ spl5_68 ),
    inference(unit_resulting_resolution,[],[f2973,f3212])).

fof(f2973,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK0)
    | spl5_67 ),
    inference(avatar_component_clause,[],[f2971])).

fof(f4014,plain,
    ( spl5_65
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f3213,f2981,f2946])).

fof(f2946,plain,
    ( spl5_65
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f3213,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_68 ),
    inference(forward_demodulation,[],[f3204,f1912])).

fof(f3204,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)))
    | ~ spl5_68 ),
    inference(superposition,[],[f1720,f2983])).

fof(f1720,plain,(
    ! [X2,X1] : r1_tarski(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f674,f61])).

fof(f674,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(superposition,[],[f59,f60])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f4013,plain,
    ( spl5_25
    | ~ spl5_26
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f2314,f1472,f1552,f1548])).

fof(f1548,plain,
    ( spl5_25
  <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1552,plain,
    ( spl5_26
  <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1472,plain,
    ( spl5_17
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f2314,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f1474,f38])).

fof(f1474,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f1472])).

fof(f4010,plain,
    ( spl5_109
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f4009,f3258,f83,f4002])).

fof(f4002,plain,
    ( spl5_109
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).

fof(f83,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3258,plain,
    ( spl5_75
  <=> r2_hidden(sK3(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f4009,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1)
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f3964,f60])).

fof(f3964,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1)
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f85,f3260,f69])).

fof(f3260,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f3258])).

fof(f85,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f4008,plain,
    ( spl5_108
    | ~ spl5_3
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f4007,f3258,f88,f3997])).

fof(f3997,plain,
    ( spl5_108
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f88,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f4007,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1)
    | ~ spl5_3
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f3965,f60])).

fof(f3965,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1)
    | ~ spl5_3
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f90,f3260,f69])).

fof(f90,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f4006,plain,
    ( spl5_107
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f3969,f3258,f3989])).

fof(f3989,plain,
    ( spl5_107
  <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f3969,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f3260,f3260,f69])).

fof(f4005,plain,
    ( spl5_109
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f3970,f3258,f83,f4002])).

fof(f3970,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1)
    | ~ spl5_2
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f85,f3260,f69])).

fof(f4000,plain,
    ( spl5_108
    | ~ spl5_3
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f3971,f3258,f88,f3997])).

fof(f3971,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1)
    | ~ spl5_3
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f90,f3260,f69])).

fof(f3992,plain,
    ( spl5_107
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f3975,f3258,f3989])).

fof(f3975,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f3260,f3260,f69])).

fof(f3904,plain,
    ( spl5_106
    | ~ spl5_60
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f3869,f3371,f2918,f3899])).

fof(f3899,plain,
    ( spl5_106
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f2918,plain,
    ( spl5_60
  <=> r2_hidden(sK3(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f3869,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0)
    | ~ spl5_60
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f2920,f3373,f69])).

fof(f3373,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f3371])).

fof(f2920,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f2918])).

fof(f3903,plain,
    ( spl5_105
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f3870,f3371,f3893])).

fof(f3893,plain,
    ( spl5_105
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f3870,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0)
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f3373,f3373,f69])).

fof(f3902,plain,
    ( spl5_106
    | ~ spl5_60
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f3897,f3371,f2918,f3899])).

fof(f3897,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0)
    | ~ spl5_60
    | ~ spl5_86 ),
    inference(forward_demodulation,[],[f3871,f60])).

fof(f3871,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK2),sK0)
    | ~ spl5_60
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f2920,f3373,f69])).

fof(f3896,plain,
    ( spl5_105
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f3872,f3371,f3893])).

fof(f3872,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0)
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f3373,f3373,f69])).

fof(f3891,plain,
    ( spl5_104
    | spl5_78
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f3878,f3371,f3325,f3888])).

fof(f3888,plain,
    ( spl5_104
  <=> r2_hidden(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f3878,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))
    | spl5_78
    | ~ spl5_86 ),
    inference(unit_resulting_resolution,[],[f3326,f3373,f74])).

fof(f3326,plain,
    ( ~ r2_hidden(sK2,sK2)
    | spl5_78 ),
    inference(avatar_component_clause,[],[f3325])).

fof(f3721,plain,
    ( spl5_103
    | ~ spl5_60
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f3680,f3364,f2918,f3716])).

fof(f3716,plain,
    ( spl5_103
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f3680,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0)
    | ~ spl5_60
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f2920,f3366,f69])).

fof(f3366,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f3364])).

fof(f3720,plain,
    ( spl5_102
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f3681,f3364,f3710])).

fof(f3710,plain,
    ( spl5_102
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f3681,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f3366,f3366,f69])).

fof(f3719,plain,
    ( spl5_103
    | ~ spl5_60
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f3714,f3364,f2918,f3716])).

fof(f3714,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0)
    | ~ spl5_60
    | ~ spl5_85 ),
    inference(forward_demodulation,[],[f3682,f60])).

fof(f3682,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK0),sK0)
    | ~ spl5_60
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f2920,f3366,f69])).

fof(f3713,plain,
    ( spl5_102
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f3683,f3364,f3710])).

fof(f3683,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f3366,f3366,f69])).

fof(f3708,plain,
    ( spl5_101
    | spl5_77
    | ~ spl5_85 ),
    inference(avatar_split_clause,[],[f3688,f3364,f3320,f3705])).

fof(f3705,plain,
    ( spl5_101
  <=> r2_hidden(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f3688,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))
    | spl5_77
    | ~ spl5_85 ),
    inference(unit_resulting_resolution,[],[f3321,f3366,f74])).

fof(f3321,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_77 ),
    inference(avatar_component_clause,[],[f3320])).

fof(f3679,plain,
    ( ~ spl5_91
    | ~ spl5_2
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3598,f3371,f83,f3546])).

fof(f3598,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_2
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f85,f3372,f39])).

fof(f3678,plain,
    ( ~ spl5_91
    | ~ spl5_2
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3574,f3371,f83,f3546])).

fof(f3574,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_2
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f3372,f105])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f39,f85])).

fof(f3677,plain,
    ( ~ spl5_91
    | ~ spl5_2
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3570,f3371,f83,f3546])).

fof(f3570,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_2
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f72,f3372,f1976])).

fof(f1976,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(sK1,X6)
        | ~ r1_tarski(X6,X7)
        | r2_hidden(sK2,X7) )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f1197,f1912])).

fof(f1197,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_tarski(sK1,X6)
        | r2_hidden(sK2,X7)
        | ~ r1_tarski(k5_xboole_0(X6,k5_xboole_0(X8,X8)),X7) )
    | ~ spl5_2 ),
    inference(resolution,[],[f1134,f39])).

fof(f1134,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2,k5_xboole_0(X1,k5_xboole_0(X0,X0)))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl5_2 ),
    inference(superposition,[],[f747,f195])).

fof(f747,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,sK1)))
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_2 ),
    inference(superposition,[],[f693,f35])).

fof(f693,plain,
    ( ! [X18] : r2_hidden(sK2,k5_xboole_0(X18,k5_xboole_0(sK1,k3_xboole_0(sK1,X18))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f681,f61])).

fof(f681,plain,
    ( ! [X18] : r2_hidden(sK2,k3_tarski(k3_enumset1(X18,X18,X18,X18,sK1)))
    | ~ spl5_2 ),
    inference(superposition,[],[f116,f60])).

fof(f116,plain,
    ( ! [X0] : r2_hidden(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f59,f105])).

fof(f3676,plain,
    ( ~ spl5_91
    | ~ spl5_2
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3565,f3371,f83,f3546])).

fof(f3565,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_2
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f72,f3372,f1976])).

fof(f3675,plain,
    ( spl5_99
    | spl5_91 ),
    inference(avatar_split_clause,[],[f3655,f3546,f3665])).

fof(f3665,plain,
    ( spl5_99
  <=> r2_hidden(sK3(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f3655,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl5_91 ),
    inference(unit_resulting_resolution,[],[f72,f3548,f107])).

fof(f3673,plain,
    ( ~ spl5_100
    | spl5_91 ),
    inference(avatar_split_clause,[],[f3662,f3546,f3670])).

fof(f3670,plain,
    ( spl5_100
  <=> r2_hidden(sK3(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f3662,plain,
    ( ~ r2_hidden(sK3(sK1,sK0),sK0)
    | spl5_91 ),
    inference(unit_resulting_resolution,[],[f3548,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3668,plain,
    ( spl5_99
    | spl5_91 ),
    inference(avatar_split_clause,[],[f3663,f3546,f3665])).

fof(f3663,plain,
    ( r2_hidden(sK3(sK1,sK0),sK1)
    | spl5_91 ),
    inference(unit_resulting_resolution,[],[f3548,f40])).

fof(f3654,plain,
    ( spl5_98
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f3639,f3384,f3651])).

fof(f3651,plain,
    ( spl5_98
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f3384,plain,
    ( spl5_88
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f3639,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f3385,f35])).

fof(f3385,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f3384])).

fof(f3649,plain,
    ( ~ spl5_97
    | spl5_31
    | ~ spl5_88 ),
    inference(avatar_split_clause,[],[f3642,f3384,f1602,f3646])).

fof(f3646,plain,
    ( spl5_97
  <=> r2_hidden(sK3(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1602,plain,
    ( spl5_31
  <=> r2_hidden(sK3(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f3642,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK2)
    | spl5_31
    | ~ spl5_88 ),
    inference(unit_resulting_resolution,[],[f1604,f3385,f39])).

fof(f1604,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f3637,plain,
    ( spl5_96
    | ~ spl5_65
    | spl5_88 ),
    inference(avatar_split_clause,[],[f3611,f3384,f2946,f3634])).

fof(f3634,plain,
    ( spl5_96
  <=> r2_hidden(sK3(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f3611,plain,
    ( r2_hidden(sK3(sK2,sK1),sK0)
    | ~ spl5_65
    | spl5_88 ),
    inference(unit_resulting_resolution,[],[f2947,f3386,f107])).

fof(f3386,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_88 ),
    inference(avatar_component_clause,[],[f3384])).

fof(f2947,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f2946])).

fof(f3632,plain,
    ( spl5_94
    | spl5_88 ),
    inference(avatar_split_clause,[],[f3612,f3384,f3622])).

fof(f3622,plain,
    ( spl5_94
  <=> r2_hidden(sK3(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f3612,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_88 ),
    inference(unit_resulting_resolution,[],[f72,f3386,f107])).

fof(f3630,plain,
    ( ~ spl5_95
    | spl5_88 ),
    inference(avatar_split_clause,[],[f3619,f3384,f3627])).

fof(f3627,plain,
    ( spl5_95
  <=> r2_hidden(sK3(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f3619,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK1)
    | spl5_88 ),
    inference(unit_resulting_resolution,[],[f3386,f41])).

fof(f3625,plain,
    ( spl5_94
    | spl5_88 ),
    inference(avatar_split_clause,[],[f3620,f3384,f3622])).

fof(f3620,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_88 ),
    inference(unit_resulting_resolution,[],[f3386,f40])).

fof(f3603,plain,
    ( spl5_93
    | ~ spl5_2
    | spl5_86 ),
    inference(avatar_split_clause,[],[f3583,f3371,f83,f3600])).

fof(f3600,plain,
    ( spl5_93
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f3583,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_2
    | spl5_86 ),
    inference(unit_resulting_resolution,[],[f85,f3372,f74])).

fof(f3564,plain,
    ( ~ spl5_91
    | ~ spl5_3
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3511,f3364,f88,f3546])).

fof(f3511,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_3
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f72,f3365,f1978])).

fof(f1978,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(sK1,X5)
        | ~ r1_tarski(X5,X6)
        | r2_hidden(sK0,X6) )
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f1224,f1912])).

fof(f1224,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_tarski(sK1,X5)
        | r2_hidden(sK0,X6)
        | ~ r1_tarski(k5_xboole_0(X5,k5_xboole_0(X7,X7)),X6) )
    | ~ spl5_3 ),
    inference(resolution,[],[f1150,f39])).

fof(f1150,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k5_xboole_0(X1,k5_xboole_0(X0,X0)))
        | ~ r1_tarski(sK1,X1) )
    | ~ spl5_3 ),
    inference(superposition,[],[f798,f195])).

fof(f798,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,sK1)))
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_3 ),
    inference(superposition,[],[f694,f35])).

fof(f694,plain,
    ( ! [X19] : r2_hidden(sK0,k5_xboole_0(X19,k5_xboole_0(sK1,k3_xboole_0(sK1,X19))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f682,f61])).

fof(f682,plain,
    ( ! [X19] : r2_hidden(sK0,k3_tarski(k3_enumset1(X19,X19,X19,X19,sK1)))
    | ~ spl5_3 ),
    inference(superposition,[],[f115,f60])).

fof(f115,plain,
    ( ! [X0] : r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f59,f106])).

fof(f106,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK1,X1)
        | r2_hidden(sK0,X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f39,f90])).

fof(f3562,plain,
    ( ~ spl5_91
    | ~ spl5_3
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3516,f3364,f88,f3546])).

fof(f3516,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_3
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f72,f3365,f1978])).

fof(f3561,plain,
    ( ~ spl5_91
    | ~ spl5_3
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3520,f3364,f88,f3546])).

fof(f3520,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_3
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f3365,f106])).

fof(f3554,plain,
    ( spl5_92
    | ~ spl5_3
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3529,f3364,f88,f3551])).

fof(f3551,plain,
    ( spl5_92
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f3529,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_3
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f90,f3365,f74])).

fof(f3549,plain,
    ( ~ spl5_91
    | ~ spl5_3
    | spl5_85 ),
    inference(avatar_split_clause,[],[f3544,f3364,f88,f3546])).

fof(f3544,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_3
    | spl5_85 ),
    inference(unit_resulting_resolution,[],[f90,f3365,f39])).

fof(f3503,plain,
    ( spl5_90
    | ~ spl5_2
    | spl5_78 ),
    inference(avatar_split_clause,[],[f3484,f3325,f83,f3500])).

fof(f3500,plain,
    ( spl5_90
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f3484,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_2
    | spl5_78 ),
    inference(unit_resulting_resolution,[],[f85,f3326,f74])).

fof(f3433,plain,
    ( spl5_89
    | ~ spl5_3
    | spl5_77 ),
    inference(avatar_split_clause,[],[f3414,f3320,f88,f3430])).

fof(f3414,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_3
    | spl5_77 ),
    inference(unit_resulting_resolution,[],[f90,f3321,f74])).

fof(f3387,plain,
    ( spl5_87
    | ~ spl5_88
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3318,f3236,f3384,f3380])).

fof(f3380,plain,
    ( spl5_87
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f3318,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | ~ spl5_72 ),
    inference(resolution,[],[f3237,f38])).

fof(f3378,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3317,f3236,f83,f3325])).

fof(f3317,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(resolution,[],[f3237,f105])).

fof(f3377,plain,
    ( spl5_77
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3316,f3236,f88,f3320])).

fof(f3316,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(resolution,[],[f3237,f106])).

fof(f3376,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3269,f3236,f83,f3325])).

fof(f3269,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f3237,f105])).

fof(f3375,plain,
    ( spl5_77
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3270,f3236,f88,f3320])).

fof(f3270,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f3237,f106])).

fof(f3374,plain,
    ( spl5_86
    | ~ spl5_2
    | ~ spl5_65
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3278,f3236,f2946,f83,f3371])).

fof(f3278,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2
    | ~ spl5_65
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f2947,f3237,f1976])).

fof(f3369,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3279,f3236,f83,f3325])).

fof(f3279,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f72,f3237,f1976])).

fof(f3367,plain,
    ( spl5_85
    | ~ spl5_3
    | ~ spl5_65
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3288,f3236,f2946,f88,f3364])).

fof(f3288,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl5_3
    | ~ spl5_65
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f2947,f3237,f1978])).

fof(f3362,plain,
    ( spl5_77
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3289,f3236,f88,f3320])).

fof(f3289,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f72,f3237,f1978])).

fof(f3360,plain,
    ( spl5_84
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3295,f3236,f3357])).

fof(f3295,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f3237,f35])).

fof(f3355,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3296,f3236,f83,f3325])).

fof(f3296,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f85,f3237,f39])).

fof(f3354,plain,
    ( spl5_77
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3297,f3236,f88,f3320])).

fof(f3297,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f90,f3237,f39])).

fof(f3353,plain,
    ( ~ spl5_83
    | spl5_52
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3301,f3236,f2275,f3350])).

fof(f3350,plain,
    ( spl5_83
  <=> r2_hidden(sK3(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f2275,plain,
    ( spl5_52
  <=> r2_hidden(sK3(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f3301,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK1)
    | spl5_52
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f2277,f3237,f39])).

fof(f2277,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | spl5_52 ),
    inference(avatar_component_clause,[],[f2275])).

fof(f3348,plain,
    ( ~ spl5_82
    | spl5_61
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3302,f3236,f2923,f3345])).

fof(f3345,plain,
    ( spl5_82
  <=> r2_hidden(sK3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f2923,plain,
    ( spl5_61
  <=> r2_hidden(sK3(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f3302,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK1)
    | spl5_61
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f2925,f3237,f39])).

fof(f2925,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK2)
    | spl5_61 ),
    inference(avatar_component_clause,[],[f2923])).

fof(f3343,plain,
    ( ~ spl5_81
    | spl5_66
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3303,f3236,f2966,f3340])).

fof(f3340,plain,
    ( spl5_81
  <=> r2_hidden(sK3(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f3303,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK1)
    | spl5_66
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f2967,f3237,f39])).

fof(f2967,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK2)
    | spl5_66 ),
    inference(avatar_component_clause,[],[f2966])).

fof(f3338,plain,
    ( spl5_80
    | spl5_23
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3309,f3236,f1528,f3335])).

fof(f3335,plain,
    ( spl5_80
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f1528,plain,
    ( spl5_23
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f3309,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2)
    | spl5_23
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f1530,f3237,f107])).

fof(f1530,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f3333,plain,
    ( spl5_79
    | spl5_26
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3310,f3236,f1552,f3330])).

fof(f3330,plain,
    ( spl5_79
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f3310,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2)
    | spl5_26
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f1554,f3237,f107])).

fof(f1554,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f3328,plain,
    ( spl5_78
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3312,f3236,f83,f3325])).

fof(f3312,plain,
    ( r2_hidden(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f72,f3237,f1976])).

fof(f3323,plain,
    ( spl5_77
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f3313,f3236,f88,f3320])).

fof(f3313,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_72 ),
    inference(unit_resulting_resolution,[],[f72,f3237,f1978])).

fof(f3268,plain,
    ( spl5_75
    | spl5_72 ),
    inference(avatar_split_clause,[],[f3248,f3236,f3258])).

fof(f3248,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_72 ),
    inference(unit_resulting_resolution,[],[f72,f3238,f107])).

fof(f3238,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_72 ),
    inference(avatar_component_clause,[],[f3236])).

fof(f3266,plain,
    ( ~ spl5_76
    | spl5_72 ),
    inference(avatar_split_clause,[],[f3255,f3236,f3263])).

fof(f3263,plain,
    ( spl5_76
  <=> r2_hidden(sK3(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f3255,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl5_72 ),
    inference(unit_resulting_resolution,[],[f3238,f41])).

fof(f3261,plain,
    ( spl5_75
    | spl5_72 ),
    inference(avatar_split_clause,[],[f3256,f3236,f3258])).

fof(f3256,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_72 ),
    inference(unit_resulting_resolution,[],[f3238,f40])).

fof(f3247,plain,
    ( ~ spl5_72
    | spl5_74
    | ~ spl5_2
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f3233,f2981,f83,f3245,f3236])).

fof(f3245,plain,
    ( spl5_74
  <=> ! [X1] : r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f3233,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0)
        | ~ r1_tarski(sK1,sK2) )
    | ~ spl5_2
    | ~ spl5_68 ),
    inference(resolution,[],[f3212,f245])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),X1)
        | ~ r1_tarski(sK1,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f206,f39])).

fof(f206,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f185,f40])).

fof(f185,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k5_xboole_0(X0,X0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f177,f105])).

fof(f3243,plain,
    ( ~ spl5_72
    | spl5_73
    | ~ spl5_7
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f3232,f2981,f160,f3240,f3236])).

fof(f3240,plain,
    ( spl5_73
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f3232,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_7
    | ~ spl5_68 ),
    inference(resolution,[],[f3212,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f162,f39])).

fof(f3211,plain,
    ( spl5_71
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f3206,f2981,f3208])).

fof(f3208,plain,
    ( spl5_71
  <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f3206,plain,
    ( sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_68 ),
    inference(forward_demodulation,[],[f3197,f1984])).

fof(f1984,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = X4 ),
    inference(backward_demodulation,[],[f1755,f1912])).

fof(f1755,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f1754,f1733])).

fof(f1754,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,X3)))) ),
    inference(forward_demodulation,[],[f1716,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1716,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X3,X3))) ),
    inference(superposition,[],[f61,f196])).

fof(f196,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f186,f35])).

fof(f3197,plain,
    ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k5_xboole_0(sK2,sK2)))
    | ~ spl5_68 ),
    inference(superposition,[],[f62,f2983])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f56,f32,f56])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3023,plain,
    ( spl5_70
    | ~ spl5_60
    | spl5_61 ),
    inference(avatar_split_clause,[],[f3009,f2923,f2918,f3020])).

fof(f3020,plain,
    ( spl5_70
  <=> r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f3009,plain,
    ( r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))
    | ~ spl5_60
    | spl5_61 ),
    inference(unit_resulting_resolution,[],[f2920,f2925,f74])).

fof(f3006,plain,
    ( spl5_69
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2986,f2918,f3002])).

fof(f3002,plain,
    ( spl5_69
  <=> r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f2986,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f2920,f2920,f69])).

fof(f3005,plain,
    ( spl5_69
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f2987,f2918,f3002])).

fof(f2987,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)
    | ~ spl5_60 ),
    inference(unit_resulting_resolution,[],[f2920,f2920,f69])).

fof(f2984,plain,
    ( spl5_68
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f2975,f2946,f2981])).

fof(f2975,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl5_65 ),
    inference(unit_resulting_resolution,[],[f2947,f35])).

fof(f2974,plain,
    ( ~ spl5_67
    | spl5_65 ),
    inference(avatar_split_clause,[],[f2963,f2946,f2971])).

fof(f2963,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK0)
    | spl5_65 ),
    inference(unit_resulting_resolution,[],[f2948,f41])).

fof(f2948,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl5_65 ),
    inference(avatar_component_clause,[],[f2946])).

fof(f2969,plain,
    ( spl5_66
    | spl5_65 ),
    inference(avatar_split_clause,[],[f2964,f2946,f2966])).

fof(f2964,plain,
    ( r2_hidden(sK3(sK2,sK0),sK2)
    | spl5_65 ),
    inference(unit_resulting_resolution,[],[f2948,f40])).

fof(f2949,plain,
    ( spl5_64
    | ~ spl5_65
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f2930,f2899,f2946,f2942])).

fof(f2942,plain,
    ( spl5_64
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2899,plain,
    ( spl5_58
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2930,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2
    | ~ spl5_58 ),
    inference(resolution,[],[f2901,f38])).

fof(f2901,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f2899])).

fof(f2940,plain,
    ( spl5_63
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f2927,f2899,f2937])).

fof(f2937,plain,
    ( spl5_63
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f2927,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f2901,f35])).

fof(f2935,plain,
    ( ~ spl5_62
    | spl5_52
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f2928,f2899,f2275,f2932])).

fof(f2932,plain,
    ( spl5_62
  <=> r2_hidden(sK3(sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2928,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK0)
    | spl5_52
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f2277,f2901,f39])).

fof(f2926,plain,
    ( ~ spl5_61
    | spl5_58 ),
    inference(avatar_split_clause,[],[f2915,f2899,f2923])).

fof(f2915,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK2)
    | spl5_58 ),
    inference(unit_resulting_resolution,[],[f2900,f41])).

fof(f2900,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl5_58 ),
    inference(avatar_component_clause,[],[f2899])).

fof(f2921,plain,
    ( spl5_60
    | spl5_58 ),
    inference(avatar_split_clause,[],[f2916,f2899,f2918])).

fof(f2916,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | spl5_58 ),
    inference(unit_resulting_resolution,[],[f2900,f40])).

fof(f2914,plain,
    ( spl5_59
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2830,f1561,f160,f2910])).

fof(f2910,plain,
    ( spl5_59
  <=> r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f1561,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f2830,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f162,f1563,f69])).

fof(f1563,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f1561])).

fof(f2913,plain,
    ( spl5_59
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2908,f1561,f160,f2910])).

fof(f2908,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f2824,f60])).

fof(f2824,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k5_xboole_0(sK1,sK1))),sK1)
    | ~ spl5_7
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f162,f1563,f69])).

fof(f2907,plain,
    ( spl5_58
    | ~ spl5_19
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f2906,f1690,f1500,f2899])).

fof(f1500,plain,
    ( spl5_19
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1690,plain,
    ( spl5_37
  <=> sK2 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f2906,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_19
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f2890,f1692])).

fof(f1692,plain,
    ( sK2 = k3_tarski(sK1)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f2890,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl5_19 ),
    inference(superposition,[],[f674,f1502])).

fof(f1502,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f2905,plain,
    ( spl5_57
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f2904,f1500,f2893])).

fof(f2893,plain,
    ( spl5_57
  <=> sK0 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f2904,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2903,f1912])).

fof(f2903,plain,
    ( k3_tarski(sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0))
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f2883,f98])).

fof(f2883,plain,
    ( k3_tarski(sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)))
    | ~ spl5_19 ),
    inference(superposition,[],[f61,f1502])).

fof(f2902,plain,
    ( spl5_58
    | ~ spl5_19
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f2897,f1690,f1500,f2899])).

fof(f2897,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_19
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f2882,f1692])).

fof(f2882,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl5_19 ),
    inference(superposition,[],[f59,f1502])).

fof(f2896,plain,
    ( spl5_57
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f2881,f1500,f2893])).

fof(f2881,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl5_19 ),
    inference(superposition,[],[f58,f1502])).

fof(f2866,plain,
    ( spl5_56
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2865,f1561,f83,f2858])).

fof(f2858,plain,
    ( spl5_56
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f2865,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f2822,f60])).

fof(f2822,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2),sK1)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f85,f1563,f69])).

fof(f2864,plain,
    ( spl5_55
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2863,f1561,f88,f2853])).

fof(f2853,plain,
    ( spl5_55
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f2863,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f2823,f60])).

fof(f2823,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK0),sK1)
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f90,f1563,f69])).

fof(f2862,plain,
    ( spl5_54
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2827,f1561,f2848])).

fof(f2848,plain,
    ( spl5_54
  <=> r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f2827,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f1563,f1563,f69])).

fof(f2861,plain,
    ( spl5_56
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2828,f1561,f83,f2858])).

fof(f2828,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f85,f1563,f69])).

fof(f2856,plain,
    ( spl5_55
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2829,f1561,f88,f2853])).

fof(f2829,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_3
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f90,f1563,f69])).

fof(f2851,plain,
    ( spl5_54
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f2833,f1561,f2848])).

fof(f2833,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f1563,f1563,f69])).

fof(f2289,plain,
    ( ~ spl5_37
    | spl5_39
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | ~ spl5_37
    | spl5_39
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f2273,f2259])).

fof(f2259,plain,
    ( ! [X0] : ~ r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),X0),sK2)
    | ~ spl5_37
    | spl5_39 ),
    inference(backward_demodulation,[],[f1845,f1692])).

fof(f1845,plain,
    ( ! [X0] : ~ r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),X0),sK2)
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f525,f1704,f39])).

fof(f1704,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f1703,plain,
    ( spl5_39
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f525,plain,(
    ! [X0,X1] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f72,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2273,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)
    | ~ spl5_37
    | ~ spl5_51 ),
    inference(backward_demodulation,[],[f2237,f1692])).

fof(f2237,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f2235])).

fof(f2235,plain,
    ( spl5_51
  <=> r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f2286,plain,
    ( spl5_53
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f2254,f1824,f1690,f2283])).

fof(f2283,plain,
    ( spl5_53
  <=> r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1824,plain,
    ( spl5_46
  <=> r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f2254,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(backward_demodulation,[],[f1826,f1692])).

fof(f1826,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1824])).

fof(f2281,plain,
    ( ~ spl5_52
    | ~ spl5_37
    | spl5_44 ),
    inference(avatar_split_clause,[],[f2252,f1792,f1690,f2275])).

fof(f1792,plain,
    ( spl5_44
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f2252,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_37
    | spl5_44 ),
    inference(backward_demodulation,[],[f1794,f1692])).

fof(f1794,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)
    | spl5_44 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f2280,plain,
    ( ~ spl5_52
    | ~ spl5_37
    | spl5_43 ),
    inference(avatar_split_clause,[],[f2251,f1787,f1690,f2275])).

fof(f1787,plain,
    ( spl5_43
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f2251,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_37
    | spl5_43 ),
    inference(backward_demodulation,[],[f1788,f1692])).

fof(f1788,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f1787])).

fof(f2279,plain,
    ( ~ spl5_52
    | ~ spl5_37
    | spl5_40 ),
    inference(avatar_split_clause,[],[f2248,f1708,f1690,f2275])).

fof(f1708,plain,
    ( spl5_40
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f2248,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_37
    | spl5_40 ),
    inference(backward_demodulation,[],[f1710,f1692])).

fof(f1710,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | spl5_40 ),
    inference(avatar_component_clause,[],[f1708])).

fof(f2278,plain,
    ( ~ spl5_52
    | ~ spl5_37
    | spl5_39 ),
    inference(avatar_split_clause,[],[f2247,f1703,f1690,f2275])).

fof(f2247,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_37
    | spl5_39 ),
    inference(backward_demodulation,[],[f1704,f1692])).

fof(f2245,plain,
    ( spl5_37
    | ~ spl5_38
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f2244,f1775,f1695,f1690])).

fof(f1695,plain,
    ( spl5_38
  <=> r1_tarski(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1775,plain,
    ( spl5_42
  <=> r1_tarski(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f2244,plain,
    ( sK2 = k3_tarski(sK1)
    | ~ spl5_38
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f1800,f1697])).

fof(f1697,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f1800,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK1))
    | sK2 = k3_tarski(sK1)
    | ~ spl5_42 ),
    inference(resolution,[],[f1776,f38])).

fof(f1776,plain,
    ( r1_tarski(k3_tarski(sK1),sK2)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f1775])).

fof(f2242,plain,
    ( spl5_37
    | ~ spl5_42
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1833,f1695,f1775,f1690])).

fof(f1833,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_38 ),
    inference(resolution,[],[f1697,f38])).

fof(f2241,plain,
    ( spl5_37
    | ~ spl5_42
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1768,f1695,f1775,f1690])).

fof(f1768,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_38 ),
    inference(resolution,[],[f1697,f38])).

fof(f2240,plain,
    ( spl5_37
    | ~ spl5_42
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f2195,f1695,f1775,f1690])).

fof(f2195,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_38 ),
    inference(resolution,[],[f1697,f38])).

fof(f2239,plain,
    ( spl5_51
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f2215,f1787,f2235])).

fof(f2215,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f1789,f1789,f69])).

fof(f1789,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f1787])).

fof(f2238,plain,
    ( spl5_51
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f2216,f1787,f2235])).

fof(f2216,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_43 ),
    inference(unit_resulting_resolution,[],[f1789,f1789,f69])).

fof(f2233,plain,
    ( spl5_50
    | ~ spl5_43
    | spl5_44 ),
    inference(avatar_split_clause,[],[f2219,f1792,f1787,f2230])).

fof(f2230,plain,
    ( spl5_50
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f2219,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2)))
    | ~ spl5_43
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f1794,f1789,f74])).

fof(f2189,plain,
    ( spl5_48
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f2179,f1871,f2038])).

fof(f2038,plain,
    ( spl5_48
  <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1871,plain,
    ( spl5_47
  <=> k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f2179,plain,
    ( k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | ~ spl5_47 ),
    inference(forward_demodulation,[],[f1873,f1912])).

fof(f1873,plain,
    ( k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f2188,plain,
    ( spl5_48
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f2182,f1770,f2038])).

fof(f1770,plain,
    ( spl5_41
  <=> sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f2182,plain,
    ( k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1869,f1912])).

fof(f1869,plain,
    ( k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1868,f60])).

fof(f1868,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2))
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1864,f1755])).

fof(f1864,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k5_xboole_0(sK2,sK2)))
    | ~ spl5_41 ),
    inference(superposition,[],[f62,f1772])).

fof(f1772,plain,
    ( sK2 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f1770])).

fof(f2187,plain,
    ( spl5_38
    | spl5_39 ),
    inference(avatar_split_clause,[],[f1834,f1703,f1695])).

fof(f1834,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | spl5_39 ),
    inference(unit_resulting_resolution,[],[f1704,f40])).

fof(f2186,plain,
    ( spl5_38
    | spl5_39 ),
    inference(avatar_split_clause,[],[f1846,f1703,f1695])).

fof(f1846,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | spl5_39 ),
    inference(resolution,[],[f1704,f40])).

fof(f2184,plain,
    ( ~ spl5_41
    | spl5_48 ),
    inference(avatar_contradiction_clause,[],[f2183])).

fof(f2183,plain,
    ( $false
    | ~ spl5_41
    | spl5_48 ),
    inference(subsumption_resolution,[],[f2182,f2040])).

fof(f2040,plain,
    ( k3_tarski(sK1) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f2181,plain,
    ( ~ spl5_47
    | spl5_48 ),
    inference(avatar_contradiction_clause,[],[f2180])).

fof(f2180,plain,
    ( $false
    | ~ spl5_47
    | spl5_48 ),
    inference(subsumption_resolution,[],[f2179,f2040])).

fof(f2178,plain,
    ( spl5_49
    | ~ spl5_39
    | spl5_40 ),
    inference(avatar_split_clause,[],[f2164,f1708,f1703,f2175])).

fof(f2175,plain,
    ( spl5_49
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2164,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1))))
    | ~ spl5_39
    | spl5_40 ),
    inference(unit_resulting_resolution,[],[f1705,f1710,f74])).

fof(f1705,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f2041,plain,
    ( ~ spl5_48
    | spl5_47 ),
    inference(avatar_split_clause,[],[f2002,f1871,f2038])).

fof(f2002,plain,
    ( k3_tarski(sK1) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | spl5_47 ),
    inference(backward_demodulation,[],[f1872,f1912])).

fof(f1872,plain,
    ( k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))
    | spl5_47 ),
    inference(avatar_component_clause,[],[f1871])).

fof(f1874,plain,
    ( spl5_47
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1869,f1770,f1871])).

fof(f1828,plain,
    ( spl5_46
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f1808,f1703,f1824])).

fof(f1808,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f1705,f1705,f69])).

fof(f1827,plain,
    ( spl5_46
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f1809,f1703,f1824])).

fof(f1809,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_39 ),
    inference(unit_resulting_resolution,[],[f1705,f1705,f69])).

fof(f1805,plain,
    ( spl5_45
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1799,f1775,f1802])).

fof(f1802,plain,
    ( spl5_45
  <=> k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1799,plain,
    ( k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f1776,f35])).

fof(f1795,plain,
    ( ~ spl5_44
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1784,f1775,f1792])).

fof(f1784,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f1777,f41])).

fof(f1777,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f1775])).

fof(f1790,plain,
    ( spl5_43
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1785,f1775,f1787])).

fof(f1785,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f1777,f40])).

fof(f1781,plain,
    ( ~ spl5_42
    | spl5_37
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1780,f1695,f1690,f1775])).

fof(f1780,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | spl5_37
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1768,f1691])).

fof(f1691,plain,
    ( sK2 != k3_tarski(sK1)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f1779,plain,
    ( ~ spl5_42
    | spl5_37
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1765,f1695,f1690,f1775])).

fof(f1765,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | spl5_37
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f1691,f1697,f38])).

fof(f1778,plain,
    ( ~ spl5_42
    | spl5_37
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1766,f1695,f1690,f1775])).

fof(f1766,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | spl5_37
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f1691,f1697,f38])).

fof(f1773,plain,
    ( spl5_41
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1767,f1695,f1770])).

fof(f1767,plain,
    ( sK2 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f1697,f35])).

fof(f1711,plain,
    ( ~ spl5_40
    | spl5_38 ),
    inference(avatar_split_clause,[],[f1700,f1695,f1708])).

fof(f1700,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f1696,f41])).

fof(f1696,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK1))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f1706,plain,
    ( spl5_39
    | spl5_38 ),
    inference(avatar_split_clause,[],[f1701,f1695,f1703])).

fof(f1701,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f1696,f40])).

fof(f1699,plain,
    ( spl5_38
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f1687,f1548,f1695])).

fof(f1687,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl5_25 ),
    inference(superposition,[],[f674,f1550])).

fof(f1550,plain,
    ( sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f1548])).

fof(f1698,plain,
    ( spl5_38
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f1680,f1548,f1695])).

fof(f1680,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl5_25 ),
    inference(superposition,[],[f59,f1550])).

fof(f1693,plain,
    ( spl5_37
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f1679,f1548,f1690])).

fof(f1679,plain,
    ( sK2 = k3_tarski(sK1)
    | ~ spl5_25 ),
    inference(superposition,[],[f58,f1550])).

fof(f1667,plain,
    ( ~ spl5_36
    | spl5_26 ),
    inference(avatar_split_clause,[],[f1656,f1552,f1664])).

fof(f1664,plain,
    ( spl5_36
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f1656,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f1554,f41])).

fof(f1662,plain,
    ( spl5_35
    | spl5_26 ),
    inference(avatar_split_clause,[],[f1657,f1552,f1659])).

fof(f1659,plain,
    ( spl5_35
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1657,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1)
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f1554,f40])).

fof(f1649,plain,
    ( ~ spl5_34
    | ~ spl5_16
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1638,f1602,f1463,f1646])).

fof(f1646,plain,
    ( spl5_34
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1638,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_16
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1604,f1465,f39])).

fof(f1631,plain,
    ( ~ spl5_33
    | ~ spl5_15
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1617,f1602,f1457,f1628])).

fof(f1628,plain,
    ( spl5_33
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1617,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_15
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1459,f1604,f39])).

fof(f1626,plain,
    ( ~ spl5_32
    | ~ spl5_17
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1618,f1602,f1472,f1623])).

fof(f1623,plain,
    ( spl5_32
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1618,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_17
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1474,f1604,f39])).

fof(f1606,plain,
    ( ~ spl5_31
    | ~ spl5_22
    | spl5_30 ),
    inference(avatar_split_clause,[],[f1595,f1580,f1524,f1602])).

fof(f1524,plain,
    ( spl5_22
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1580,plain,
    ( spl5_30
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1595,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_22
    | spl5_30 ),
    inference(backward_demodulation,[],[f1582,f1526])).

fof(f1526,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f1582,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1605,plain,
    ( ~ spl5_31
    | ~ spl5_22
    | spl5_29 ),
    inference(avatar_split_clause,[],[f1594,f1575,f1524,f1602])).

fof(f1575,plain,
    ( spl5_29
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f1594,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_22
    | spl5_29 ),
    inference(backward_demodulation,[],[f1576,f1526])).

fof(f1576,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1600,plain,
    ( spl5_14
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f1599])).

fof(f1599,plain,
    ( $false
    | spl5_14
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1598,f72])).

fof(f1598,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl5_14
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f1585,f58])).

fof(f1585,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1)),sK1)
    | spl5_14
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f1212,f1526])).

fof(f1212,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1210,plain,
    ( spl5_14
  <=> r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1597,plain,
    ( spl5_4
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | spl5_4
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f1584,f58])).

fof(f1584,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl5_4
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f96,f1526])).

fof(f1583,plain,
    ( ~ spl5_30
    | spl5_23 ),
    inference(avatar_split_clause,[],[f1572,f1528,f1580])).

fof(f1572,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f1530,f41])).

fof(f1578,plain,
    ( spl5_29
    | spl5_23 ),
    inference(avatar_split_clause,[],[f1573,f1528,f1575])).

fof(f1573,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f1530,f40])).

fof(f1569,plain,
    ( ~ spl5_28
    | spl5_20 ),
    inference(avatar_split_clause,[],[f1558,f1504,f1566])).

fof(f1566,plain,
    ( spl5_28
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1504,plain,
    ( spl5_20
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1558,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f1506,f41])).

fof(f1506,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f1564,plain,
    ( spl5_27
    | spl5_20 ),
    inference(avatar_split_clause,[],[f1559,f1504,f1561])).

fof(f1559,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f1506,f40])).

fof(f1555,plain,
    ( spl5_25
    | ~ spl5_26
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1541,f1472,f1552,f1548])).

fof(f1541,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_17 ),
    inference(resolution,[],[f1474,f38])).

fof(f1546,plain,
    ( spl5_24
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1538,f1472,f1543])).

fof(f1543,plain,
    ( spl5_24
  <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1538,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f1474,f35])).

fof(f1531,plain,
    ( spl5_22
    | ~ spl5_23
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1517,f1463,f1528,f1524])).

fof(f1517,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2)
    | ~ spl5_16 ),
    inference(resolution,[],[f1465,f38])).

fof(f1522,plain,
    ( spl5_21
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1514,f1463,f1519])).

fof(f1519,plain,
    ( spl5_21
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1514,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f1465,f35])).

fof(f1507,plain,
    ( spl5_19
    | ~ spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1493,f1457,f1504,f1500])).

fof(f1493,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f1459,f38])).

fof(f1498,plain,
    ( spl5_18
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f1490,f1457,f1495])).

fof(f1495,plain,
    ( spl5_18
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1490,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f1459,f35])).

fof(f1475,plain,
    ( spl5_17
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1421,f83,f1472])).

fof(f1421,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f85,f85,f69])).

fof(f1470,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1422,f88,f83,f1463])).

fof(f1422,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f90,f85,f69])).

fof(f1466,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1461,f88,f83,f1463])).

fof(f1461,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f1426,f60])).

fof(f1426,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f85,f90,f69])).

fof(f1460,plain,
    ( spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1427,f88,f1457])).

fof(f1427,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f90,f90,f69])).

fof(f1214,plain,
    ( ~ spl5_14
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1207,f94,f1210])).

fof(f1207,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f59,f96,f38])).

fof(f1213,plain,
    ( ~ spl5_14
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1208,f94,f1210])).

fof(f1208,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f59,f96,f38])).

fof(f969,plain,
    ( spl5_13
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f936,f143,f83,f966])).

fof(f966,plain,
    ( spl5_13
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f143,plain,
    ( spl5_5
  <=> r2_hidden(sK2,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f936,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f85,f145,f74])).

fof(f145,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f964,plain,
    ( spl5_12
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f939,f165,f160,f960])).

fof(f960,plain,
    ( spl5_12
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f165,plain,
    ( spl5_8
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f939,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f162,f167,f74])).

fof(f167,plain,
    ( ~ r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f963,plain,
    ( spl5_12
    | ~ spl5_2
    | spl5_8 ),
    inference(avatar_split_clause,[],[f940,f165,f83,f960])).

fof(f940,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_2
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f206,f167,f74])).

fof(f805,plain,
    ( spl5_11
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f799,f88,f802])).

fof(f802,plain,
    ( spl5_11
  <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f799,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))
    | ~ spl5_3 ),
    inference(superposition,[],[f694,f98])).

fof(f754,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f748,f83,f751])).

fof(f751,plain,
    ( spl5_10
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f748,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))
    | ~ spl5_2 ),
    inference(superposition,[],[f693,f98])).

fof(f204,plain,
    ( ~ spl5_9
    | spl5_5 ),
    inference(avatar_split_clause,[],[f198,f143,f201])).

fof(f201,plain,
    ( spl5_9
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f198,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | spl5_5 ),
    inference(backward_demodulation,[],[f174,f196])).

fof(f174,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))
    | spl5_5 ),
    inference(forward_demodulation,[],[f170,f43])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f145,f76])).

fof(f168,plain,
    ( ~ spl5_8
    | spl5_6 ),
    inference(avatar_split_clause,[],[f157,f152,f165])).

fof(f157,plain,
    ( ~ r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f154,f41])).

fof(f163,plain,
    ( spl5_7
    | spl5_6 ),
    inference(avatar_split_clause,[],[f158,f152,f160])).

fof(f158,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f154,f40])).

fof(f156,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f147,f143,f83,f152])).

fof(f147,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f145,f105])).

fof(f155,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f148,f143,f83,f152])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f85,f145,f39])).

fof(f146,plain,
    ( ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f141,f83,f143])).

fof(f141,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f129,f98])).

fof(f129,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f85,f75])).

fof(f97,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f92,f78,f94])).

fof(f78,plain,
    ( spl5_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f92,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl5_1 ),
    inference(forward_demodulation,[],[f80,f60])).

fof(f80,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f91,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f88])).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f83])).

fof(f25,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f57,f78])).

fof(f57,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f26,f56,f55])).

fof(f26,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:42:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (29361)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.52  % (29354)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.52  % (29347)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (29343)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.53  % (29369)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.53  % (29342)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (29344)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (29346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (29348)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (29365)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (29357)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (29370)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (29349)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.54  % (29360)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.54  % (29362)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (29371)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.55  % (29362)Refutation not found, incomplete strategy% (29362)------------------------------
% 1.41/0.55  % (29362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (29362)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (29362)Memory used [KB]: 10746
% 1.41/0.55  % (29362)Time elapsed: 0.140 s
% 1.41/0.55  % (29362)------------------------------
% 1.41/0.55  % (29362)------------------------------
% 1.41/0.55  % (29345)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.55  % (29350)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (29364)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (29355)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (29353)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (29363)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (29352)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.56  % (29356)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.56  % (29359)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (29367)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.56  % (29368)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.57  % (29364)Refutation not found, incomplete strategy% (29364)------------------------------
% 1.41/0.57  % (29364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (29364)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (29364)Memory used [KB]: 10746
% 1.41/0.57  % (29364)Time elapsed: 0.160 s
% 1.41/0.57  % (29364)------------------------------
% 1.41/0.57  % (29364)------------------------------
% 1.41/0.59  % (29366)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.59  % (29358)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.60  % (29351)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.48/0.74  % (29376)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.08/0.77  % (29386)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.40/0.83  % (29347)Time limit reached!
% 3.40/0.83  % (29347)------------------------------
% 3.40/0.83  % (29347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.83  % (29347)Termination reason: Time limit
% 3.40/0.83  
% 3.40/0.83  % (29347)Memory used [KB]: 9210
% 3.40/0.83  % (29347)Time elapsed: 0.408 s
% 3.40/0.83  % (29347)------------------------------
% 3.40/0.83  % (29347)------------------------------
% 4.26/0.92  % (29354)Time limit reached!
% 4.26/0.92  % (29354)------------------------------
% 4.26/0.92  % (29354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.92  % (29354)Termination reason: Time limit
% 4.26/0.92  
% 4.26/0.92  % (29354)Memory used [KB]: 9210
% 4.26/0.92  % (29354)Time elapsed: 0.519 s
% 4.26/0.92  % (29354)------------------------------
% 4.26/0.92  % (29354)------------------------------
% 4.26/0.93  % (29359)Time limit reached!
% 4.26/0.93  % (29359)------------------------------
% 4.26/0.93  % (29359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (29359)Termination reason: Time limit
% 4.26/0.93  % (29359)Termination phase: Saturation
% 4.26/0.93  
% 4.26/0.93  % (29359)Memory used [KB]: 14328
% 4.26/0.93  % (29359)Time elapsed: 0.500 s
% 4.26/0.93  % (29359)------------------------------
% 4.26/0.93  % (29359)------------------------------
% 4.26/0.93  % (29342)Time limit reached!
% 4.26/0.93  % (29342)------------------------------
% 4.26/0.93  % (29342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (29342)Termination reason: Time limit
% 4.26/0.93  % (29342)Termination phase: Saturation
% 4.26/0.93  
% 4.26/0.93  % (29342)Memory used [KB]: 3070
% 4.26/0.93  % (29342)Time elapsed: 0.500 s
% 4.26/0.93  % (29342)------------------------------
% 4.26/0.93  % (29342)------------------------------
% 4.26/0.93  % (29352)Time limit reached!
% 4.26/0.93  % (29352)------------------------------
% 4.26/0.93  % (29352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (29352)Termination reason: Time limit
% 4.26/0.93  % (29352)Termination phase: Saturation
% 4.26/0.93  
% 4.26/0.93  % (29352)Memory used [KB]: 14072
% 4.26/0.93  % (29352)Time elapsed: 0.500 s
% 4.26/0.93  % (29352)------------------------------
% 4.26/0.93  % (29352)------------------------------
% 4.26/0.96  % (29343)Time limit reached!
% 4.26/0.96  % (29343)------------------------------
% 4.26/0.96  % (29343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.96  % (29343)Termination reason: Time limit
% 4.26/0.96  
% 4.26/0.96  % (29343)Memory used [KB]: 8315
% 4.26/0.96  % (29343)Time elapsed: 0.515 s
% 4.26/0.96  % (29343)------------------------------
% 4.26/0.96  % (29343)------------------------------
% 4.26/0.97  % (29407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.63/1.02  % (29349)Time limit reached!
% 4.63/1.02  % (29349)------------------------------
% 4.63/1.02  % (29349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.02  % (29349)Termination reason: Time limit
% 4.63/1.02  % (29349)Termination phase: Saturation
% 4.63/1.02  
% 4.63/1.02  % (29349)Memory used [KB]: 10490
% 4.63/1.02  % (29349)Time elapsed: 0.600 s
% 4.63/1.02  % (29349)------------------------------
% 4.63/1.02  % (29349)------------------------------
% 4.63/1.03  % (29370)Time limit reached!
% 4.63/1.03  % (29370)------------------------------
% 4.63/1.03  % (29370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/1.03  % (29370)Termination reason: Time limit
% 4.63/1.03  
% 4.63/1.03  % (29370)Memory used [KB]: 9210
% 4.63/1.03  % (29370)Time elapsed: 0.623 s
% 4.63/1.03  % (29370)------------------------------
% 4.63/1.03  % (29370)------------------------------
% 5.11/1.06  % (29409)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.11/1.06  % (29408)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.11/1.07  % (29411)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.11/1.07  % (29358)Time limit reached!
% 5.11/1.07  % (29358)------------------------------
% 5.11/1.07  % (29358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.11/1.07  % (29358)Termination reason: Time limit
% 5.11/1.07  % (29358)Termination phase: Saturation
% 5.11/1.07  
% 5.11/1.07  % (29358)Memory used [KB]: 17782
% 5.11/1.07  % (29358)Time elapsed: 0.600 s
% 5.11/1.07  % (29358)------------------------------
% 5.11/1.07  % (29358)------------------------------
% 5.62/1.09  % (29410)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.94/1.14  % (29412)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.13/1.17  % (29413)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.13/1.18  % (29414)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.13/1.20  % (29415)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.13/1.21  % (29356)Refutation found. Thanks to Tanya!
% 6.13/1.21  % SZS status Theorem for theBenchmark
% 6.13/1.21  % SZS output start Proof for theBenchmark
% 6.13/1.21  fof(f4203,plain,(
% 6.13/1.21    $false),
% 6.13/1.21    inference(avatar_sat_refutation,[],[f81,f86,f91,f97,f146,f155,f156,f163,f168,f204,f754,f805,f963,f964,f969,f1213,f1214,f1460,f1466,f1470,f1475,f1498,f1507,f1522,f1531,f1546,f1555,f1564,f1569,f1578,f1583,f1597,f1600,f1605,f1606,f1626,f1631,f1649,f1662,f1667,f1693,f1698,f1699,f1706,f1711,f1773,f1778,f1779,f1781,f1790,f1795,f1805,f1827,f1828,f1874,f2041,f2178,f2181,f2184,f2186,f2187,f2188,f2189,f2233,f2238,f2239,f2240,f2241,f2242,f2245,f2278,f2279,f2280,f2281,f2286,f2289,f2851,f2856,f2861,f2862,f2864,f2866,f2896,f2902,f2905,f2907,f2913,f2914,f2921,f2926,f2935,f2940,f2949,f2969,f2974,f2984,f3005,f3006,f3023,f3211,f3243,f3247,f3261,f3266,f3268,f3323,f3328,f3333,f3338,f3343,f3348,f3353,f3354,f3355,f3360,f3362,f3367,f3369,f3374,f3375,f3376,f3377,f3378,f3387,f3433,f3503,f3549,f3554,f3561,f3562,f3564,f3603,f3625,f3630,f3632,f3637,f3649,f3654,f3668,f3673,f3675,f3676,f3677,f3678,f3679,f3708,f3713,f3719,f3720,f3721,f3891,f3896,f3902,f3903,f3904,f3992,f4000,f4005,f4006,f4008,f4010,f4013,f4014,f4015,f4016,f4017,f4018,f4019,f4023,f4028,f4029,f4114,f4146,f4151,f4152,f4180,f4182,f4188,f4193,f4195,f4202])).
% 6.13/1.21  fof(f4202,plain,(
% 6.13/1.21    spl5_4 | ~spl5_16),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f4201])).
% 6.13/1.21  fof(f4201,plain,(
% 6.13/1.21    $false | (spl5_4 | ~spl5_16)),
% 6.13/1.21    inference(subsumption_resolution,[],[f4179,f1465])).
% 6.13/1.21  fof(f1465,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_16),
% 6.13/1.21    inference(avatar_component_clause,[],[f1463])).
% 6.13/1.21  fof(f1463,plain,(
% 6.13/1.21    spl5_16 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 6.13/1.21  fof(f4179,plain,(
% 6.13/1.21    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl5_4),
% 6.13/1.21    inference(trivial_inequality_removal,[],[f4178])).
% 6.13/1.21  fof(f4178,plain,(
% 6.13/1.21    sK1 != sK1 | ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl5_4),
% 6.13/1.21    inference(superposition,[],[f96,f1983])).
% 6.13/1.21  fof(f1983,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(backward_demodulation,[],[f1715,f1912])).
% 6.13/1.21  fof(f1912,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0) )),
% 6.13/1.21    inference(superposition,[],[f1733,f195])).
% 6.13/1.21  fof(f195,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1)) )),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f186,f186,f38])).
% 6.13/1.21  fof(f38,plain,(
% 6.13/1.21    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.13/1.21    inference(cnf_transformation,[],[f4])).
% 6.13/1.21  fof(f4,axiom,(
% 6.13/1.21    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.13/1.21  fof(f186,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f177,f40])).
% 6.13/1.21  fof(f40,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f23])).
% 6.13/1.21  fof(f23,plain,(
% 6.13/1.21    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.13/1.21    inference(ennf_transformation,[],[f1])).
% 6.13/1.21  fof(f1,axiom,(
% 6.13/1.21    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 6.13/1.21  fof(f177,plain,(
% 6.13/1.21    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3))) )),
% 6.13/1.21    inference(subsumption_resolution,[],[f173,f135])).
% 6.13/1.21  fof(f135,plain,(
% 6.13/1.21    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | ~r2_hidden(X4,X3)) )),
% 6.13/1.21    inference(superposition,[],[f75,f98])).
% 6.13/1.21  fof(f98,plain,(
% 6.13/1.21    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f35])).
% 6.13/1.21  fof(f35,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f22])).
% 6.13/1.21  fof(f22,plain,(
% 6.13/1.21    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.13/1.21    inference(ennf_transformation,[],[f6])).
% 6.13/1.21  fof(f6,axiom,(
% 6.13/1.21    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.13/1.21  fof(f72,plain,(
% 6.13/1.21    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.13/1.21    inference(equality_resolution,[],[f37])).
% 6.13/1.21  fof(f37,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.13/1.21    inference(cnf_transformation,[],[f4])).
% 6.13/1.21  fof(f75,plain,(
% 6.13/1.21    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 6.13/1.21    inference(equality_resolution,[],[f64])).
% 6.13/1.21  fof(f64,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 6.13/1.21    inference(definition_unfolding,[],[f48,f32])).
% 6.13/1.21  fof(f32,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.13/1.21    inference(cnf_transformation,[],[f5])).
% 6.13/1.21  fof(f5,axiom,(
% 6.13/1.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.13/1.21  fof(f48,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.13/1.21    inference(cnf_transformation,[],[f2])).
% 6.13/1.21  fof(f2,axiom,(
% 6.13/1.21    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.13/1.21  fof(f173,plain,(
% 6.13/1.21    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | r2_hidden(X4,X3)) )),
% 6.13/1.21    inference(superposition,[],[f76,f98])).
% 6.13/1.21  fof(f76,plain,(
% 6.13/1.21    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 6.13/1.21    inference(equality_resolution,[],[f65])).
% 6.13/1.21  fof(f65,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 6.13/1.21    inference(definition_unfolding,[],[f47,f32])).
% 6.13/1.21  fof(f47,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.13/1.21    inference(cnf_transformation,[],[f2])).
% 6.13/1.21  fof(f1733,plain,(
% 6.13/1.21    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 6.13/1.21    inference(forward_demodulation,[],[f1714,f98])).
% 6.13/1.21  fof(f1714,plain,(
% 6.13/1.21    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 6.13/1.21    inference(superposition,[],[f61,f58])).
% 6.13/1.21  fof(f58,plain,(
% 6.13/1.21    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 6.13/1.21    inference(definition_unfolding,[],[f27,f56])).
% 6.13/1.21  fof(f56,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.13/1.21    inference(definition_unfolding,[],[f31,f55])).
% 6.13/1.21  fof(f55,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.13/1.21    inference(definition_unfolding,[],[f30,f54])).
% 6.13/1.21  fof(f54,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.13/1.21    inference(definition_unfolding,[],[f42,f53])).
% 6.13/1.21  fof(f53,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f14])).
% 6.13/1.21  fof(f14,axiom,(
% 6.13/1.21    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.13/1.21  fof(f42,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f13])).
% 6.13/1.21  fof(f13,axiom,(
% 6.13/1.21    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.13/1.21  fof(f30,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f12])).
% 6.13/1.21  fof(f12,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.13/1.21  fof(f31,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.13/1.21    inference(cnf_transformation,[],[f15])).
% 6.13/1.21  fof(f15,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.13/1.21  fof(f27,plain,(
% 6.13/1.21    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.13/1.21    inference(cnf_transformation,[],[f19])).
% 6.13/1.21  fof(f19,plain,(
% 6.13/1.21    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.13/1.21    inference(rectify,[],[f3])).
% 6.13/1.21  fof(f3,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 6.13/1.21  fof(f61,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 6.13/1.21    inference(definition_unfolding,[],[f33,f56,f32])).
% 6.13/1.21  fof(f33,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.13/1.21    inference(cnf_transformation,[],[f10])).
% 6.13/1.21  fof(f10,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.13/1.21  fof(f1715,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X0,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) | ~r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(superposition,[],[f61,f35])).
% 6.13/1.21  fof(f96,plain,(
% 6.13/1.21    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl5_4),
% 6.13/1.21    inference(avatar_component_clause,[],[f94])).
% 6.13/1.21  fof(f94,plain,(
% 6.13/1.21    spl5_4 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 6.13/1.21  fof(f4195,plain,(
% 6.13/1.21    spl5_4 | ~spl5_16),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f4194])).
% 6.13/1.21  fof(f4194,plain,(
% 6.13/1.21    $false | (spl5_4 | ~spl5_16)),
% 6.13/1.21    inference(subsumption_resolution,[],[f4161,f96])).
% 6.13/1.21  fof(f4161,plain,(
% 6.13/1.21    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | ~spl5_16),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1465,f1983])).
% 6.13/1.21  fof(f4193,plain,(
% 6.13/1.21    spl5_115 | ~spl5_15),
% 6.13/1.21    inference(avatar_split_clause,[],[f4162,f1457,f4190])).
% 6.13/1.21  fof(f4190,plain,(
% 6.13/1.21    spl5_115 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 6.13/1.21  fof(f1457,plain,(
% 6.13/1.21    spl5_15 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 6.13/1.21  fof(f4162,plain,(
% 6.13/1.21    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl5_15),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1459,f1983])).
% 6.13/1.21  fof(f1459,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_15),
% 6.13/1.21    inference(avatar_component_clause,[],[f1457])).
% 6.13/1.21  fof(f4188,plain,(
% 6.13/1.21    spl5_114 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f4183,f3236,f4185])).
% 6.13/1.21  fof(f4185,plain,(
% 6.13/1.21    spl5_114 <=> sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 6.13/1.21  fof(f3236,plain,(
% 6.13/1.21    spl5_72 <=> r1_tarski(sK1,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 6.13/1.21  fof(f4183,plain,(
% 6.13/1.21    sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl5_72),
% 6.13/1.21    inference(forward_demodulation,[],[f4163,f60])).
% 6.13/1.21  fof(f60,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 6.13/1.21    inference(definition_unfolding,[],[f29,f55,f55])).
% 6.13/1.21  fof(f29,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f11])).
% 6.13/1.21  fof(f11,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.13/1.21  fof(f4163,plain,(
% 6.13/1.21    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK1)) | ~spl5_72),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3237,f1983])).
% 6.13/1.21  fof(f3237,plain,(
% 6.13/1.21    r1_tarski(sK1,sK2) | ~spl5_72),
% 6.13/1.21    inference(avatar_component_clause,[],[f3236])).
% 6.13/1.21  fof(f4182,plain,(
% 6.13/1.21    spl5_4 | ~spl5_16),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f4181])).
% 6.13/1.21  fof(f4181,plain,(
% 6.13/1.21    $false | (spl5_4 | ~spl5_16)),
% 6.13/1.21    inference(subsumption_resolution,[],[f4164,f1465])).
% 6.13/1.21  fof(f4164,plain,(
% 6.13/1.21    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | spl5_4),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f96,f1983])).
% 6.13/1.21  fof(f4180,plain,(
% 6.13/1.21    spl5_4 | ~spl5_16),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f4165])).
% 6.13/1.21  fof(f4165,plain,(
% 6.13/1.21    $false | (spl5_4 | ~spl5_16)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1465,f96,f1983])).
% 6.13/1.21  fof(f4152,plain,(
% 6.13/1.21    spl5_113 | ~spl5_77),
% 6.13/1.21    inference(avatar_split_clause,[],[f4127,f3320,f4148])).
% 6.13/1.21  fof(f4148,plain,(
% 6.13/1.21    spl5_113 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 6.13/1.21  fof(f3320,plain,(
% 6.13/1.21    spl5_77 <=> r2_hidden(sK0,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 6.13/1.21  fof(f4127,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | ~spl5_77),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3322,f3322,f69])).
% 6.13/1.21  fof(f69,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 6.13/1.21    inference(definition_unfolding,[],[f52,f55])).
% 6.13/1.21  fof(f52,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f16])).
% 6.13/1.21  fof(f16,axiom,(
% 6.13/1.21    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 6.13/1.21  fof(f3322,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | ~spl5_77),
% 6.13/1.21    inference(avatar_component_clause,[],[f3320])).
% 6.13/1.21  fof(f4151,plain,(
% 6.13/1.21    spl5_113 | ~spl5_77),
% 6.13/1.21    inference(avatar_split_clause,[],[f4128,f3320,f4148])).
% 6.13/1.21  fof(f4128,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2) | ~spl5_77),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3322,f3322,f69])).
% 6.13/1.21  fof(f4146,plain,(
% 6.13/1.21    spl5_112 | ~spl5_77 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f4133,f3364,f3320,f4143])).
% 6.13/1.21  fof(f4143,plain,(
% 6.13/1.21    spl5_112 <=> r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 6.13/1.21  fof(f3364,plain,(
% 6.13/1.21    spl5_85 <=> r2_hidden(sK0,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 6.13/1.21  fof(f4133,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | (~spl5_77 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3365,f3322,f74])).
% 6.13/1.21  fof(f74,plain,(
% 6.13/1.21    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 6.13/1.21    inference(equality_resolution,[],[f63])).
% 6.13/1.21  fof(f63,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 6.13/1.21    inference(definition_unfolding,[],[f49,f32])).
% 6.13/1.21  fof(f49,plain,(
% 6.13/1.21    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.13/1.21    inference(cnf_transformation,[],[f2])).
% 6.13/1.21  fof(f3365,plain,(
% 6.13/1.21    ~r2_hidden(sK0,sK0) | spl5_85),
% 6.13/1.21    inference(avatar_component_clause,[],[f3364])).
% 6.13/1.21  fof(f4114,plain,(
% 6.13/1.21    spl5_111 | ~spl5_72 | spl5_91),
% 6.13/1.21    inference(avatar_split_clause,[],[f4101,f3546,f3236,f4111])).
% 6.13/1.21  fof(f4111,plain,(
% 6.13/1.21    spl5_111 <=> r2_hidden(sK3(sK1,sK0),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 6.13/1.21  fof(f3546,plain,(
% 6.13/1.21    spl5_91 <=> r1_tarski(sK1,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 6.13/1.21  fof(f4101,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK0),sK2) | (~spl5_72 | spl5_91)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3548,f3237,f107])).
% 6.13/1.21  fof(f107,plain,(
% 6.13/1.21    ( ! [X4,X2,X3] : (r2_hidden(sK3(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 6.13/1.21    inference(resolution,[],[f39,f40])).
% 6.13/1.21  fof(f39,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f23])).
% 6.13/1.21  fof(f3548,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | spl5_91),
% 6.13/1.21    inference(avatar_component_clause,[],[f3546])).
% 6.13/1.21  fof(f4029,plain,(
% 6.13/1.21    spl5_110 | spl5_6 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3304,f3236,f152,f4025])).
% 6.13/1.21  fof(f4025,plain,(
% 6.13/1.21    spl5_110 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 6.13/1.21  fof(f152,plain,(
% 6.13/1.21    spl5_6 <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.13/1.21  fof(f3304,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2) | (spl5_6 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f154,f3237,f107])).
% 6.13/1.21  fof(f154,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | spl5_6),
% 6.13/1.21    inference(avatar_component_clause,[],[f152])).
% 6.13/1.21  fof(f4028,plain,(
% 6.13/1.21    spl5_110 | ~spl5_7 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3298,f3236,f160,f4025])).
% 6.13/1.21  fof(f160,plain,(
% 6.13/1.21    spl5_7 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.13/1.21  fof(f3298,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK2) | (~spl5_7 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f162,f3237,f39])).
% 6.13/1.21  fof(f162,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) | ~spl5_7),
% 6.13/1.21    inference(avatar_component_clause,[],[f160])).
% 6.13/1.21  fof(f4023,plain,(
% 6.13/1.21    ~spl5_84 | ~spl5_89),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f4022])).
% 6.13/1.21  fof(f4022,plain,(
% 6.13/1.21    $false | (~spl5_84 | ~spl5_89)),
% 6.13/1.21    inference(subsumption_resolution,[],[f4021,f177])).
% 6.13/1.21  fof(f4021,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK1,sK1)) | (~spl5_84 | ~spl5_89)),
% 6.13/1.21    inference(backward_demodulation,[],[f3432,f3359])).
% 6.13/1.21  fof(f3359,plain,(
% 6.13/1.21    sK1 = k3_xboole_0(sK1,sK2) | ~spl5_84),
% 6.13/1.21    inference(avatar_component_clause,[],[f3357])).
% 6.13/1.21  fof(f3357,plain,(
% 6.13/1.21    spl5_84 <=> sK1 = k3_xboole_0(sK1,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 6.13/1.21  fof(f3432,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl5_89),
% 6.13/1.21    inference(avatar_component_clause,[],[f3430])).
% 6.13/1.21  fof(f3430,plain,(
% 6.13/1.21    spl5_89 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 6.13/1.21  fof(f4019,plain,(
% 6.13/1.21    ~spl5_78 | ~spl5_68 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3575,f3371,f2981,f3325])).
% 6.13/1.21  fof(f3325,plain,(
% 6.13/1.21    spl5_78 <=> r2_hidden(sK2,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 6.13/1.21  fof(f2981,plain,(
% 6.13/1.21    spl5_68 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 6.13/1.21  fof(f3371,plain,(
% 6.13/1.21    spl5_86 <=> r2_hidden(sK2,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 6.13/1.21  fof(f3575,plain,(
% 6.13/1.21    ~r2_hidden(sK2,sK2) | (~spl5_68 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3372,f3212])).
% 6.13/1.21  fof(f3212,plain,(
% 6.13/1.21    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,sK0)) ) | ~spl5_68),
% 6.13/1.21    inference(subsumption_resolution,[],[f3201,f177])).
% 6.13/1.21  fof(f3201,plain,(
% 6.13/1.21    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK2,sK2)) | r2_hidden(X3,sK0) | ~r2_hidden(X3,sK2)) ) | ~spl5_68),
% 6.13/1.21    inference(superposition,[],[f74,f2983])).
% 6.13/1.21  fof(f2983,plain,(
% 6.13/1.21    sK2 = k3_xboole_0(sK2,sK0) | ~spl5_68),
% 6.13/1.21    inference(avatar_component_clause,[],[f2981])).
% 6.13/1.21  fof(f3372,plain,(
% 6.13/1.21    ~r2_hidden(sK2,sK0) | spl5_86),
% 6.13/1.21    inference(avatar_component_clause,[],[f3371])).
% 6.13/1.21  fof(f4018,plain,(
% 6.13/1.21    ~spl5_78 | ~spl5_68 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3916,f3371,f2981,f3325])).
% 6.13/1.21  fof(f3916,plain,(
% 6.13/1.21    ~r2_hidden(sK2,sK2) | (~spl5_68 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3372,f3212])).
% 6.13/1.21  fof(f4017,plain,(
% 6.13/1.21    ~spl5_77 | ~spl5_68 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3521,f3364,f2981,f3320])).
% 6.13/1.21  fof(f3521,plain,(
% 6.13/1.21    ~r2_hidden(sK0,sK2) | (~spl5_68 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3365,f3212])).
% 6.13/1.21  fof(f4016,plain,(
% 6.13/1.21    ~spl5_77 | ~spl5_68 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3827,f3364,f2981,f3320])).
% 6.13/1.21  fof(f3827,plain,(
% 6.13/1.21    ~r2_hidden(sK0,sK2) | (~spl5_68 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3365,f3212])).
% 6.13/1.21  fof(f4015,plain,(
% 6.13/1.21    ~spl5_66 | spl5_67 | ~spl5_68),
% 6.13/1.21    inference(avatar_split_clause,[],[f3230,f2981,f2971,f2966])).
% 6.13/1.21  fof(f2966,plain,(
% 6.13/1.21    spl5_66 <=> r2_hidden(sK3(sK2,sK0),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 6.13/1.21  fof(f2971,plain,(
% 6.13/1.21    spl5_67 <=> r2_hidden(sK3(sK2,sK0),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 6.13/1.21  fof(f3230,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK0),sK2) | (spl5_67 | ~spl5_68)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2973,f3212])).
% 6.13/1.21  fof(f2973,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK0),sK0) | spl5_67),
% 6.13/1.21    inference(avatar_component_clause,[],[f2971])).
% 6.13/1.21  fof(f4014,plain,(
% 6.13/1.21    spl5_65 | ~spl5_68),
% 6.13/1.21    inference(avatar_split_clause,[],[f3213,f2981,f2946])).
% 6.13/1.21  fof(f2946,plain,(
% 6.13/1.21    spl5_65 <=> r1_tarski(sK2,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 6.13/1.21  fof(f3213,plain,(
% 6.13/1.21    r1_tarski(sK2,sK0) | ~spl5_68),
% 6.13/1.21    inference(forward_demodulation,[],[f3204,f1912])).
% 6.13/1.21  fof(f3204,plain,(
% 6.13/1.21    r1_tarski(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))) | ~spl5_68),
% 6.13/1.21    inference(superposition,[],[f1720,f2983])).
% 6.13/1.21  fof(f1720,plain,(
% 6.13/1.21    ( ! [X2,X1] : (r1_tarski(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 6.13/1.21    inference(superposition,[],[f674,f61])).
% 6.13/1.21  fof(f674,plain,(
% 6.13/1.21    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) )),
% 6.13/1.21    inference(superposition,[],[f59,f60])).
% 6.13/1.21  fof(f59,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 6.13/1.21    inference(definition_unfolding,[],[f28,f56])).
% 6.13/1.21  fof(f28,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.13/1.21    inference(cnf_transformation,[],[f8])).
% 6.13/1.21  fof(f8,axiom,(
% 6.13/1.21    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.13/1.21  fof(f4013,plain,(
% 6.13/1.21    spl5_25 | ~spl5_26 | ~spl5_17),
% 6.13/1.21    inference(avatar_split_clause,[],[f2314,f1472,f1552,f1548])).
% 6.13/1.21  fof(f1548,plain,(
% 6.13/1.21    spl5_25 <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 6.13/1.21  fof(f1552,plain,(
% 6.13/1.21    spl5_26 <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 6.13/1.21  fof(f1472,plain,(
% 6.13/1.21    spl5_17 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 6.13/1.21  fof(f2314,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_17),
% 6.13/1.21    inference(resolution,[],[f1474,f38])).
% 6.13/1.21  fof(f1474,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_17),
% 6.13/1.21    inference(avatar_component_clause,[],[f1472])).
% 6.13/1.21  fof(f4010,plain,(
% 6.13/1.21    spl5_109 | ~spl5_2 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f4009,f3258,f83,f4002])).
% 6.13/1.21  fof(f4002,plain,(
% 6.13/1.21    spl5_109 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_109])])).
% 6.13/1.21  fof(f83,plain,(
% 6.13/1.21    spl5_2 <=> r2_hidden(sK2,sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.13/1.21  fof(f3258,plain,(
% 6.13/1.21    spl5_75 <=> r2_hidden(sK3(sK1,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 6.13/1.21  fof(f4009,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1) | (~spl5_2 | ~spl5_75)),
% 6.13/1.21    inference(forward_demodulation,[],[f3964,f60])).
% 6.13/1.21  fof(f3964,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1) | (~spl5_2 | ~spl5_75)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3260,f69])).
% 6.13/1.21  fof(f3260,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK2),sK1) | ~spl5_75),
% 6.13/1.21    inference(avatar_component_clause,[],[f3258])).
% 6.13/1.21  fof(f85,plain,(
% 6.13/1.21    r2_hidden(sK2,sK1) | ~spl5_2),
% 6.13/1.21    inference(avatar_component_clause,[],[f83])).
% 6.13/1.21  fof(f4008,plain,(
% 6.13/1.21    spl5_108 | ~spl5_3 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f4007,f3258,f88,f3997])).
% 6.13/1.21  fof(f3997,plain,(
% 6.13/1.21    spl5_108 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 6.13/1.21  fof(f88,plain,(
% 6.13/1.21    spl5_3 <=> r2_hidden(sK0,sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 6.13/1.21  fof(f4007,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1) | (~spl5_3 | ~spl5_75)),
% 6.13/1.21    inference(forward_demodulation,[],[f3965,f60])).
% 6.13/1.21  fof(f3965,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1) | (~spl5_3 | ~spl5_75)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3260,f69])).
% 6.13/1.21  fof(f90,plain,(
% 6.13/1.21    r2_hidden(sK0,sK1) | ~spl5_3),
% 6.13/1.21    inference(avatar_component_clause,[],[f88])).
% 6.13/1.21  fof(f4006,plain,(
% 6.13/1.21    spl5_107 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f3969,f3258,f3989])).
% 6.13/1.21  fof(f3989,plain,(
% 6.13/1.21    spl5_107 <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 6.13/1.21  fof(f3969,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) | ~spl5_75),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3260,f3260,f69])).
% 6.13/1.21  fof(f4005,plain,(
% 6.13/1.21    spl5_109 | ~spl5_2 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f3970,f3258,f83,f4002])).
% 6.13/1.21  fof(f3970,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1) | (~spl5_2 | ~spl5_75)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3260,f69])).
% 6.13/1.21  fof(f4000,plain,(
% 6.13/1.21    spl5_108 | ~spl5_3 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f3971,f3258,f88,f3997])).
% 6.13/1.21  fof(f3971,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1) | (~spl5_3 | ~spl5_75)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3260,f69])).
% 6.13/1.21  fof(f3992,plain,(
% 6.13/1.21    spl5_107 | ~spl5_75),
% 6.13/1.21    inference(avatar_split_clause,[],[f3975,f3258,f3989])).
% 6.13/1.21  fof(f3975,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) | ~spl5_75),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3260,f3260,f69])).
% 6.13/1.21  fof(f3904,plain,(
% 6.13/1.21    spl5_106 | ~spl5_60 | ~spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3869,f3371,f2918,f3899])).
% 6.13/1.21  fof(f3899,plain,(
% 6.13/1.21    spl5_106 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 6.13/1.21  fof(f2918,plain,(
% 6.13/1.21    spl5_60 <=> r2_hidden(sK3(sK0,sK2),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 6.13/1.21  fof(f3869,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0) | (~spl5_60 | ~spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f3373,f69])).
% 6.13/1.21  fof(f3373,plain,(
% 6.13/1.21    r2_hidden(sK2,sK0) | ~spl5_86),
% 6.13/1.21    inference(avatar_component_clause,[],[f3371])).
% 6.13/1.21  fof(f2920,plain,(
% 6.13/1.21    r2_hidden(sK3(sK0,sK2),sK0) | ~spl5_60),
% 6.13/1.21    inference(avatar_component_clause,[],[f2918])).
% 6.13/1.21  fof(f3903,plain,(
% 6.13/1.21    spl5_105 | ~spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3870,f3371,f3893])).
% 6.13/1.21  fof(f3893,plain,(
% 6.13/1.21    spl5_105 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 6.13/1.21  fof(f3870,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0) | ~spl5_86),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3373,f3373,f69])).
% 6.13/1.21  fof(f3902,plain,(
% 6.13/1.21    spl5_106 | ~spl5_60 | ~spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3897,f3371,f2918,f3899])).
% 6.13/1.21  fof(f3897,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK0,sK2)),sK0) | (~spl5_60 | ~spl5_86)),
% 6.13/1.21    inference(forward_demodulation,[],[f3871,f60])).
% 6.13/1.21  fof(f3871,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK2),sK0) | (~spl5_60 | ~spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f3373,f69])).
% 6.13/1.21  fof(f3896,plain,(
% 6.13/1.21    spl5_105 | ~spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3872,f3371,f3893])).
% 6.13/1.21  fof(f3872,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK0) | ~spl5_86),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3373,f3373,f69])).
% 6.13/1.21  fof(f3891,plain,(
% 6.13/1.21    spl5_104 | spl5_78 | ~spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3878,f3371,f3325,f3888])).
% 6.13/1.21  fof(f3888,plain,(
% 6.13/1.21    spl5_104 <=> r2_hidden(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 6.13/1.21  fof(f3878,plain,(
% 6.13/1.21    r2_hidden(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) | (spl5_78 | ~spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3326,f3373,f74])).
% 6.13/1.21  fof(f3326,plain,(
% 6.13/1.21    ~r2_hidden(sK2,sK2) | spl5_78),
% 6.13/1.21    inference(avatar_component_clause,[],[f3325])).
% 6.13/1.21  fof(f3721,plain,(
% 6.13/1.21    spl5_103 | ~spl5_60 | ~spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3680,f3364,f2918,f3716])).
% 6.13/1.21  fof(f3716,plain,(
% 6.13/1.21    spl5_103 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 6.13/1.21  fof(f3680,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0) | (~spl5_60 | ~spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f3366,f69])).
% 6.13/1.21  fof(f3366,plain,(
% 6.13/1.21    r2_hidden(sK0,sK0) | ~spl5_85),
% 6.13/1.21    inference(avatar_component_clause,[],[f3364])).
% 6.13/1.21  fof(f3720,plain,(
% 6.13/1.21    spl5_102 | ~spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3681,f3364,f3710])).
% 6.13/1.21  fof(f3710,plain,(
% 6.13/1.21    spl5_102 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 6.13/1.21  fof(f3681,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0) | ~spl5_85),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3366,f3366,f69])).
% 6.13/1.21  fof(f3719,plain,(
% 6.13/1.21    spl5_103 | ~spl5_60 | ~spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3714,f3364,f2918,f3716])).
% 6.13/1.21  fof(f3714,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK0,sK2)),sK0) | (~spl5_60 | ~spl5_85)),
% 6.13/1.21    inference(forward_demodulation,[],[f3682,f60])).
% 6.13/1.21  fof(f3682,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK0),sK0) | (~spl5_60 | ~spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f3366,f69])).
% 6.13/1.21  fof(f3713,plain,(
% 6.13/1.21    spl5_102 | ~spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3683,f3364,f3710])).
% 6.13/1.21  fof(f3683,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK0) | ~spl5_85),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3366,f3366,f69])).
% 6.13/1.21  fof(f3708,plain,(
% 6.13/1.21    spl5_101 | spl5_77 | ~spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3688,f3364,f3320,f3705])).
% 6.13/1.21  fof(f3705,plain,(
% 6.13/1.21    spl5_101 <=> r2_hidden(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 6.13/1.21  fof(f3688,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) | (spl5_77 | ~spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3321,f3366,f74])).
% 6.13/1.21  fof(f3321,plain,(
% 6.13/1.21    ~r2_hidden(sK0,sK2) | spl5_77),
% 6.13/1.21    inference(avatar_component_clause,[],[f3320])).
% 6.13/1.21  fof(f3679,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_2 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3598,f3371,f83,f3546])).
% 6.13/1.21  fof(f3598,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_2 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3372,f39])).
% 6.13/1.21  fof(f3678,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_2 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3574,f3371,f83,f3546])).
% 6.13/1.21  fof(f3574,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_2 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3372,f105])).
% 6.13/1.21  fof(f105,plain,(
% 6.13/1.21    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2,X0)) ) | ~spl5_2),
% 6.13/1.21    inference(resolution,[],[f39,f85])).
% 6.13/1.21  fof(f3677,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_2 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3570,f3371,f83,f3546])).
% 6.13/1.21  fof(f3570,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_2 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3372,f1976])).
% 6.13/1.21  fof(f1976,plain,(
% 6.13/1.21    ( ! [X6,X7] : (~r1_tarski(sK1,X6) | ~r1_tarski(X6,X7) | r2_hidden(sK2,X7)) ) | ~spl5_2),
% 6.13/1.21    inference(backward_demodulation,[],[f1197,f1912])).
% 6.13/1.21  fof(f1197,plain,(
% 6.13/1.21    ( ! [X6,X8,X7] : (~r1_tarski(sK1,X6) | r2_hidden(sK2,X7) | ~r1_tarski(k5_xboole_0(X6,k5_xboole_0(X8,X8)),X7)) ) | ~spl5_2),
% 6.13/1.21    inference(resolution,[],[f1134,f39])).
% 6.13/1.21  fof(f1134,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r2_hidden(sK2,k5_xboole_0(X1,k5_xboole_0(X0,X0))) | ~r1_tarski(sK1,X1)) ) | ~spl5_2),
% 6.13/1.21    inference(superposition,[],[f747,f195])).
% 6.13/1.21  fof(f747,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,sK1))) | ~r1_tarski(sK1,X0)) ) | ~spl5_2),
% 6.13/1.21    inference(superposition,[],[f693,f35])).
% 6.13/1.21  fof(f693,plain,(
% 6.13/1.21    ( ! [X18] : (r2_hidden(sK2,k5_xboole_0(X18,k5_xboole_0(sK1,k3_xboole_0(sK1,X18))))) ) | ~spl5_2),
% 6.13/1.21    inference(forward_demodulation,[],[f681,f61])).
% 6.13/1.21  fof(f681,plain,(
% 6.13/1.21    ( ! [X18] : (r2_hidden(sK2,k3_tarski(k3_enumset1(X18,X18,X18,X18,sK1)))) ) | ~spl5_2),
% 6.13/1.21    inference(superposition,[],[f116,f60])).
% 6.13/1.21  fof(f116,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)))) ) | ~spl5_2),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f59,f105])).
% 6.13/1.21  fof(f3676,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_2 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3565,f3371,f83,f3546])).
% 6.13/1.21  fof(f3565,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_2 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3372,f1976])).
% 6.13/1.21  fof(f3675,plain,(
% 6.13/1.21    spl5_99 | spl5_91),
% 6.13/1.21    inference(avatar_split_clause,[],[f3655,f3546,f3665])).
% 6.13/1.21  fof(f3665,plain,(
% 6.13/1.21    spl5_99 <=> r2_hidden(sK3(sK1,sK0),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 6.13/1.21  fof(f3655,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK0),sK1) | spl5_91),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3548,f107])).
% 6.13/1.21  fof(f3673,plain,(
% 6.13/1.21    ~spl5_100 | spl5_91),
% 6.13/1.21    inference(avatar_split_clause,[],[f3662,f3546,f3670])).
% 6.13/1.21  fof(f3670,plain,(
% 6.13/1.21    spl5_100 <=> r2_hidden(sK3(sK1,sK0),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 6.13/1.21  fof(f3662,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK0),sK0) | spl5_91),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3548,f41])).
% 6.13/1.21  fof(f41,plain,(
% 6.13/1.21    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f23])).
% 6.13/1.21  fof(f3668,plain,(
% 6.13/1.21    spl5_99 | spl5_91),
% 6.13/1.21    inference(avatar_split_clause,[],[f3663,f3546,f3665])).
% 6.13/1.21  fof(f3663,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK0),sK1) | spl5_91),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3548,f40])).
% 6.13/1.21  fof(f3654,plain,(
% 6.13/1.21    spl5_98 | ~spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3639,f3384,f3651])).
% 6.13/1.21  fof(f3651,plain,(
% 6.13/1.21    spl5_98 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 6.13/1.21  fof(f3384,plain,(
% 6.13/1.21    spl5_88 <=> r1_tarski(sK2,sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 6.13/1.21  fof(f3639,plain,(
% 6.13/1.21    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_88),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3385,f35])).
% 6.13/1.21  fof(f3385,plain,(
% 6.13/1.21    r1_tarski(sK2,sK1) | ~spl5_88),
% 6.13/1.21    inference(avatar_component_clause,[],[f3384])).
% 6.13/1.21  fof(f3649,plain,(
% 6.13/1.21    ~spl5_97 | spl5_31 | ~spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3642,f3384,f1602,f3646])).
% 6.13/1.21  fof(f3646,plain,(
% 6.13/1.21    spl5_97 <=> r2_hidden(sK3(sK1,sK1),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 6.13/1.21  fof(f1602,plain,(
% 6.13/1.21    spl5_31 <=> r2_hidden(sK3(sK1,sK1),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 6.13/1.21  fof(f3642,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),sK2) | (spl5_31 | ~spl5_88)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1604,f3385,f39])).
% 6.13/1.21  fof(f1604,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),sK1) | spl5_31),
% 6.13/1.21    inference(avatar_component_clause,[],[f1602])).
% 6.13/1.21  fof(f3637,plain,(
% 6.13/1.21    spl5_96 | ~spl5_65 | spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3611,f3384,f2946,f3634])).
% 6.13/1.21  fof(f3634,plain,(
% 6.13/1.21    spl5_96 <=> r2_hidden(sK3(sK2,sK1),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 6.13/1.21  fof(f3611,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,sK1),sK0) | (~spl5_65 | spl5_88)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2947,f3386,f107])).
% 6.13/1.21  fof(f3386,plain,(
% 6.13/1.21    ~r1_tarski(sK2,sK1) | spl5_88),
% 6.13/1.21    inference(avatar_component_clause,[],[f3384])).
% 6.13/1.21  fof(f2947,plain,(
% 6.13/1.21    r1_tarski(sK2,sK0) | ~spl5_65),
% 6.13/1.21    inference(avatar_component_clause,[],[f2946])).
% 6.13/1.21  fof(f3632,plain,(
% 6.13/1.21    spl5_94 | spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3612,f3384,f3622])).
% 6.13/1.21  fof(f3622,plain,(
% 6.13/1.21    spl5_94 <=> r2_hidden(sK3(sK2,sK1),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 6.13/1.21  fof(f3612,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,sK1),sK2) | spl5_88),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3386,f107])).
% 6.13/1.21  fof(f3630,plain,(
% 6.13/1.21    ~spl5_95 | spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3619,f3384,f3627])).
% 6.13/1.21  fof(f3627,plain,(
% 6.13/1.21    spl5_95 <=> r2_hidden(sK3(sK2,sK1),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 6.13/1.21  fof(f3619,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK1),sK1) | spl5_88),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3386,f41])).
% 6.13/1.21  fof(f3625,plain,(
% 6.13/1.21    spl5_94 | spl5_88),
% 6.13/1.21    inference(avatar_split_clause,[],[f3620,f3384,f3622])).
% 6.13/1.21  fof(f3620,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,sK1),sK2) | spl5_88),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3386,f40])).
% 6.13/1.21  fof(f3603,plain,(
% 6.13/1.21    spl5_93 | ~spl5_2 | spl5_86),
% 6.13/1.21    inference(avatar_split_clause,[],[f3583,f3371,f83,f3600])).
% 6.13/1.21  fof(f3600,plain,(
% 6.13/1.21    spl5_93 <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 6.13/1.21  fof(f3583,plain,(
% 6.13/1.21    r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | (~spl5_2 | spl5_86)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3372,f74])).
% 6.13/1.21  fof(f3564,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_3 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3511,f3364,f88,f3546])).
% 6.13/1.21  fof(f3511,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_3 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3365,f1978])).
% 6.13/1.21  fof(f1978,plain,(
% 6.13/1.21    ( ! [X6,X5] : (~r1_tarski(sK1,X5) | ~r1_tarski(X5,X6) | r2_hidden(sK0,X6)) ) | ~spl5_3),
% 6.13/1.21    inference(backward_demodulation,[],[f1224,f1912])).
% 6.13/1.21  fof(f1224,plain,(
% 6.13/1.21    ( ! [X6,X7,X5] : (~r1_tarski(sK1,X5) | r2_hidden(sK0,X6) | ~r1_tarski(k5_xboole_0(X5,k5_xboole_0(X7,X7)),X6)) ) | ~spl5_3),
% 6.13/1.21    inference(resolution,[],[f1150,f39])).
% 6.13/1.21  fof(f1150,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(X1,k5_xboole_0(X0,X0))) | ~r1_tarski(sK1,X1)) ) | ~spl5_3),
% 6.13/1.21    inference(superposition,[],[f798,f195])).
% 6.13/1.21  fof(f798,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,sK1))) | ~r1_tarski(sK1,X0)) ) | ~spl5_3),
% 6.13/1.21    inference(superposition,[],[f694,f35])).
% 6.13/1.21  fof(f694,plain,(
% 6.13/1.21    ( ! [X19] : (r2_hidden(sK0,k5_xboole_0(X19,k5_xboole_0(sK1,k3_xboole_0(sK1,X19))))) ) | ~spl5_3),
% 6.13/1.21    inference(forward_demodulation,[],[f682,f61])).
% 6.13/1.21  fof(f682,plain,(
% 6.13/1.21    ( ! [X19] : (r2_hidden(sK0,k3_tarski(k3_enumset1(X19,X19,X19,X19,sK1)))) ) | ~spl5_3),
% 6.13/1.21    inference(superposition,[],[f115,f60])).
% 6.13/1.21  fof(f115,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)))) ) | ~spl5_3),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f59,f106])).
% 6.13/1.21  fof(f106,plain,(
% 6.13/1.21    ( ! [X1] : (~r1_tarski(sK1,X1) | r2_hidden(sK0,X1)) ) | ~spl5_3),
% 6.13/1.21    inference(resolution,[],[f39,f90])).
% 6.13/1.21  fof(f3562,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_3 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3516,f3364,f88,f3546])).
% 6.13/1.21  fof(f3516,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_3 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3365,f1978])).
% 6.13/1.21  fof(f3561,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_3 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3520,f3364,f88,f3546])).
% 6.13/1.21  fof(f3520,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_3 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3365,f106])).
% 6.13/1.21  fof(f3554,plain,(
% 6.13/1.21    spl5_92 | ~spl5_3 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3529,f3364,f88,f3551])).
% 6.13/1.21  fof(f3551,plain,(
% 6.13/1.21    spl5_92 <=> r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 6.13/1.21  fof(f3529,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | (~spl5_3 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3365,f74])).
% 6.13/1.21  fof(f3549,plain,(
% 6.13/1.21    ~spl5_91 | ~spl5_3 | spl5_85),
% 6.13/1.21    inference(avatar_split_clause,[],[f3544,f3364,f88,f3546])).
% 6.13/1.21  fof(f3544,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK0) | (~spl5_3 | spl5_85)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3365,f39])).
% 6.13/1.21  fof(f3503,plain,(
% 6.13/1.21    spl5_90 | ~spl5_2 | spl5_78),
% 6.13/1.21    inference(avatar_split_clause,[],[f3484,f3325,f83,f3500])).
% 6.13/1.21  fof(f3500,plain,(
% 6.13/1.21    spl5_90 <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 6.13/1.21  fof(f3484,plain,(
% 6.13/1.21    r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl5_2 | spl5_78)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3326,f74])).
% 6.13/1.21  fof(f3433,plain,(
% 6.13/1.21    spl5_89 | ~spl5_3 | spl5_77),
% 6.13/1.21    inference(avatar_split_clause,[],[f3414,f3320,f88,f3430])).
% 6.13/1.21  fof(f3414,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl5_3 | spl5_77)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3321,f74])).
% 6.13/1.21  fof(f3387,plain,(
% 6.13/1.21    spl5_87 | ~spl5_88 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3318,f3236,f3384,f3380])).
% 6.13/1.21  fof(f3380,plain,(
% 6.13/1.21    spl5_87 <=> sK1 = sK2),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 6.13/1.21  fof(f3318,plain,(
% 6.13/1.21    ~r1_tarski(sK2,sK1) | sK1 = sK2 | ~spl5_72),
% 6.13/1.21    inference(resolution,[],[f3237,f38])).
% 6.13/1.21  fof(f3378,plain,(
% 6.13/1.21    spl5_78 | ~spl5_2 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3317,f3236,f83,f3325])).
% 6.13/1.21  fof(f3317,plain,(
% 6.13/1.21    r2_hidden(sK2,sK2) | (~spl5_2 | ~spl5_72)),
% 6.13/1.21    inference(resolution,[],[f3237,f105])).
% 6.13/1.21  fof(f3377,plain,(
% 6.13/1.21    spl5_77 | ~spl5_3 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3316,f3236,f88,f3320])).
% 6.13/1.21  fof(f3316,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | (~spl5_3 | ~spl5_72)),
% 6.13/1.21    inference(resolution,[],[f3237,f106])).
% 6.13/1.21  fof(f3376,plain,(
% 6.13/1.21    spl5_78 | ~spl5_2 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3269,f3236,f83,f3325])).
% 6.13/1.21  fof(f3269,plain,(
% 6.13/1.21    r2_hidden(sK2,sK2) | (~spl5_2 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3237,f105])).
% 6.13/1.21  fof(f3375,plain,(
% 6.13/1.21    spl5_77 | ~spl5_3 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3270,f3236,f88,f3320])).
% 6.13/1.21  fof(f3270,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | (~spl5_3 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3237,f106])).
% 6.13/1.21  fof(f3374,plain,(
% 6.13/1.21    spl5_86 | ~spl5_2 | ~spl5_65 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3278,f3236,f2946,f83,f3371])).
% 6.13/1.21  fof(f3278,plain,(
% 6.13/1.21    r2_hidden(sK2,sK0) | (~spl5_2 | ~spl5_65 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2947,f3237,f1976])).
% 6.13/1.21  fof(f3369,plain,(
% 6.13/1.21    spl5_78 | ~spl5_2 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3279,f3236,f83,f3325])).
% 6.13/1.21  fof(f3279,plain,(
% 6.13/1.21    r2_hidden(sK2,sK2) | (~spl5_2 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3237,f1976])).
% 6.13/1.21  fof(f3367,plain,(
% 6.13/1.21    spl5_85 | ~spl5_3 | ~spl5_65 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3288,f3236,f2946,f88,f3364])).
% 6.13/1.21  fof(f3288,plain,(
% 6.13/1.21    r2_hidden(sK0,sK0) | (~spl5_3 | ~spl5_65 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2947,f3237,f1978])).
% 6.13/1.21  fof(f3362,plain,(
% 6.13/1.21    spl5_77 | ~spl5_3 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3289,f3236,f88,f3320])).
% 6.13/1.21  fof(f3289,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | (~spl5_3 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3237,f1978])).
% 6.13/1.21  fof(f3360,plain,(
% 6.13/1.21    spl5_84 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3295,f3236,f3357])).
% 6.13/1.21  fof(f3295,plain,(
% 6.13/1.21    sK1 = k3_xboole_0(sK1,sK2) | ~spl5_72),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3237,f35])).
% 6.13/1.21  fof(f3355,plain,(
% 6.13/1.21    spl5_78 | ~spl5_2 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3296,f3236,f83,f3325])).
% 6.13/1.21  fof(f3296,plain,(
% 6.13/1.21    r2_hidden(sK2,sK2) | (~spl5_2 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f3237,f39])).
% 6.13/1.21  fof(f3354,plain,(
% 6.13/1.21    spl5_77 | ~spl5_3 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3297,f3236,f88,f3320])).
% 6.13/1.21  fof(f3297,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | (~spl5_3 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f3237,f39])).
% 6.13/1.21  fof(f3353,plain,(
% 6.13/1.21    ~spl5_83 | spl5_52 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3301,f3236,f2275,f3350])).
% 6.13/1.21  fof(f3350,plain,(
% 6.13/1.21    spl5_83 <=> r2_hidden(sK3(sK2,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 6.13/1.21  fof(f2275,plain,(
% 6.13/1.21    spl5_52 <=> r2_hidden(sK3(sK2,sK2),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 6.13/1.21  fof(f3301,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK1) | (spl5_52 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2277,f3237,f39])).
% 6.13/1.21  fof(f2277,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK2) | spl5_52),
% 6.13/1.21    inference(avatar_component_clause,[],[f2275])).
% 6.13/1.21  fof(f3348,plain,(
% 6.13/1.21    ~spl5_82 | spl5_61 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3302,f3236,f2923,f3345])).
% 6.13/1.21  fof(f3345,plain,(
% 6.13/1.21    spl5_82 <=> r2_hidden(sK3(sK0,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 6.13/1.21  fof(f2923,plain,(
% 6.13/1.21    spl5_61 <=> r2_hidden(sK3(sK0,sK2),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 6.13/1.21  fof(f3302,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK0,sK2),sK1) | (spl5_61 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2925,f3237,f39])).
% 6.13/1.21  fof(f2925,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK0,sK2),sK2) | spl5_61),
% 6.13/1.21    inference(avatar_component_clause,[],[f2923])).
% 6.13/1.21  fof(f3343,plain,(
% 6.13/1.21    ~spl5_81 | spl5_66 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3303,f3236,f2966,f3340])).
% 6.13/1.21  fof(f3340,plain,(
% 6.13/1.21    spl5_81 <=> r2_hidden(sK3(sK2,sK0),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 6.13/1.21  fof(f3303,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK0),sK1) | (spl5_66 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2967,f3237,f39])).
% 6.13/1.21  fof(f2967,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK0),sK2) | spl5_66),
% 6.13/1.21    inference(avatar_component_clause,[],[f2966])).
% 6.13/1.21  fof(f3338,plain,(
% 6.13/1.21    spl5_80 | spl5_23 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3309,f3236,f1528,f3335])).
% 6.13/1.21  fof(f3335,plain,(
% 6.13/1.21    spl5_80 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 6.13/1.21  fof(f1528,plain,(
% 6.13/1.21    spl5_23 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 6.13/1.21  fof(f3309,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2) | (spl5_23 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1530,f3237,f107])).
% 6.13/1.21  fof(f1530,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_23),
% 6.13/1.21    inference(avatar_component_clause,[],[f1528])).
% 6.13/1.21  fof(f3333,plain,(
% 6.13/1.21    spl5_79 | spl5_26 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3310,f3236,f1552,f3330])).
% 6.13/1.21  fof(f3330,plain,(
% 6.13/1.21    spl5_79 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 6.13/1.21  fof(f3310,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK2) | (spl5_26 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1554,f3237,f107])).
% 6.13/1.21  fof(f1554,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl5_26),
% 6.13/1.21    inference(avatar_component_clause,[],[f1552])).
% 6.13/1.21  fof(f3328,plain,(
% 6.13/1.21    spl5_78 | ~spl5_2 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3312,f3236,f83,f3325])).
% 6.13/1.21  fof(f3312,plain,(
% 6.13/1.21    r2_hidden(sK2,sK2) | (~spl5_2 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3237,f1976])).
% 6.13/1.21  fof(f3323,plain,(
% 6.13/1.21    spl5_77 | ~spl5_3 | ~spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3313,f3236,f88,f3320])).
% 6.13/1.21  fof(f3313,plain,(
% 6.13/1.21    r2_hidden(sK0,sK2) | (~spl5_3 | ~spl5_72)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3237,f1978])).
% 6.13/1.21  fof(f3268,plain,(
% 6.13/1.21    spl5_75 | spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3248,f3236,f3258])).
% 6.13/1.21  fof(f3248,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK2),sK1) | spl5_72),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f3238,f107])).
% 6.13/1.21  fof(f3238,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK2) | spl5_72),
% 6.13/1.21    inference(avatar_component_clause,[],[f3236])).
% 6.13/1.21  fof(f3266,plain,(
% 6.13/1.21    ~spl5_76 | spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3255,f3236,f3263])).
% 6.13/1.21  fof(f3263,plain,(
% 6.13/1.21    spl5_76 <=> r2_hidden(sK3(sK1,sK2),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 6.13/1.21  fof(f3255,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK2),sK2) | spl5_72),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3238,f41])).
% 6.13/1.21  fof(f3261,plain,(
% 6.13/1.21    spl5_75 | spl5_72),
% 6.13/1.21    inference(avatar_split_clause,[],[f3256,f3236,f3258])).
% 6.13/1.21  fof(f3256,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,sK2),sK1) | spl5_72),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f3238,f40])).
% 6.13/1.21  fof(f3247,plain,(
% 6.13/1.21    ~spl5_72 | spl5_74 | ~spl5_2 | ~spl5_68),
% 6.13/1.21    inference(avatar_split_clause,[],[f3233,f2981,f83,f3245,f3236])).
% 6.13/1.21  fof(f3245,plain,(
% 6.13/1.21    spl5_74 <=> ! [X1] : r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 6.13/1.21  fof(f3233,plain,(
% 6.13/1.21    ( ! [X1] : (r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0) | ~r1_tarski(sK1,sK2)) ) | (~spl5_2 | ~spl5_68)),
% 6.13/1.21    inference(resolution,[],[f3212,f245])).
% 6.13/1.21  fof(f245,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),X1) | ~r1_tarski(sK1,X1)) ) | ~spl5_2),
% 6.13/1.21    inference(resolution,[],[f206,f39])).
% 6.13/1.21  fof(f206,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),sK1)) ) | ~spl5_2),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f185,f40])).
% 6.13/1.21  fof(f185,plain,(
% 6.13/1.21    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,X0))) ) | ~spl5_2),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f177,f105])).
% 6.13/1.21  fof(f3243,plain,(
% 6.13/1.21    ~spl5_72 | spl5_73 | ~spl5_7 | ~spl5_68),
% 6.13/1.21    inference(avatar_split_clause,[],[f3232,f2981,f160,f3240,f3236])).
% 6.13/1.21  fof(f3240,plain,(
% 6.13/1.21    spl5_73 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 6.13/1.21  fof(f3232,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0) | ~r1_tarski(sK1,sK2) | (~spl5_7 | ~spl5_68)),
% 6.13/1.21    inference(resolution,[],[f3212,f238])).
% 6.13/1.21  fof(f238,plain,(
% 6.13/1.21    ( ! [X0] : (r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),X0) | ~r1_tarski(sK1,X0)) ) | ~spl5_7),
% 6.13/1.21    inference(resolution,[],[f162,f39])).
% 6.13/1.21  fof(f3211,plain,(
% 6.13/1.21    spl5_71 | ~spl5_68),
% 6.13/1.21    inference(avatar_split_clause,[],[f3206,f2981,f3208])).
% 6.13/1.21  fof(f3208,plain,(
% 6.13/1.21    spl5_71 <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 6.13/1.21  fof(f3206,plain,(
% 6.13/1.21    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | ~spl5_68),
% 6.13/1.21    inference(forward_demodulation,[],[f3197,f1984])).
% 6.13/1.21  fof(f1984,plain,(
% 6.13/1.21    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = X4) )),
% 6.13/1.21    inference(backward_demodulation,[],[f1755,f1912])).
% 6.13/1.21  fof(f1755,plain,(
% 6.13/1.21    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,X3))) )),
% 6.13/1.21    inference(forward_demodulation,[],[f1754,f1733])).
% 6.13/1.21  fof(f1754,plain,(
% 6.13/1.21    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,X3))))) )),
% 6.13/1.21    inference(forward_demodulation,[],[f1716,f43])).
% 6.13/1.21  fof(f43,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.13/1.21    inference(cnf_transformation,[],[f9])).
% 6.13/1.21  fof(f9,axiom,(
% 6.13/1.21    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.13/1.21  fof(f1716,plain,(
% 6.13/1.21    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X3,X3)))) )),
% 6.13/1.21    inference(superposition,[],[f61,f196])).
% 6.13/1.21  fof(f196,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1)) )),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f186,f35])).
% 6.13/1.21  fof(f3197,plain,(
% 6.13/1.21    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k5_xboole_0(sK2,sK2))) | ~spl5_68),
% 6.13/1.21    inference(superposition,[],[f62,f2983])).
% 6.13/1.21  fof(f62,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 6.13/1.21    inference(definition_unfolding,[],[f34,f56,f32,f56])).
% 6.13/1.21  fof(f34,plain,(
% 6.13/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f7])).
% 6.13/1.21  fof(f7,axiom,(
% 6.13/1.21    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.13/1.21  fof(f3023,plain,(
% 6.13/1.21    spl5_70 | ~spl5_60 | spl5_61),
% 6.13/1.21    inference(avatar_split_clause,[],[f3009,f2923,f2918,f3020])).
% 6.13/1.21  fof(f3020,plain,(
% 6.13/1.21    spl5_70 <=> r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 6.13/1.21  fof(f3009,plain,(
% 6.13/1.21    r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) | (~spl5_60 | spl5_61)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f2925,f74])).
% 6.13/1.21  fof(f3006,plain,(
% 6.13/1.21    spl5_69 | ~spl5_60),
% 6.13/1.21    inference(avatar_split_clause,[],[f2986,f2918,f3002])).
% 6.13/1.21  fof(f3002,plain,(
% 6.13/1.21    spl5_69 <=> r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 6.13/1.21  fof(f2986,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) | ~spl5_60),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f2920,f69])).
% 6.13/1.21  fof(f3005,plain,(
% 6.13/1.21    spl5_69 | ~spl5_60),
% 6.13/1.21    inference(avatar_split_clause,[],[f2987,f2918,f3002])).
% 6.13/1.21  fof(f2987,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) | ~spl5_60),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2920,f2920,f69])).
% 6.13/1.21  fof(f2984,plain,(
% 6.13/1.21    spl5_68 | ~spl5_65),
% 6.13/1.21    inference(avatar_split_clause,[],[f2975,f2946,f2981])).
% 6.13/1.21  fof(f2975,plain,(
% 6.13/1.21    sK2 = k3_xboole_0(sK2,sK0) | ~spl5_65),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2947,f35])).
% 6.13/1.21  fof(f2974,plain,(
% 6.13/1.21    ~spl5_67 | spl5_65),
% 6.13/1.21    inference(avatar_split_clause,[],[f2963,f2946,f2971])).
% 6.13/1.21  fof(f2963,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK0),sK0) | spl5_65),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2948,f41])).
% 6.13/1.21  fof(f2948,plain,(
% 6.13/1.21    ~r1_tarski(sK2,sK0) | spl5_65),
% 6.13/1.21    inference(avatar_component_clause,[],[f2946])).
% 6.13/1.21  fof(f2969,plain,(
% 6.13/1.21    spl5_66 | spl5_65),
% 6.13/1.21    inference(avatar_split_clause,[],[f2964,f2946,f2966])).
% 6.13/1.21  fof(f2964,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,sK0),sK2) | spl5_65),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2948,f40])).
% 6.13/1.21  fof(f2949,plain,(
% 6.13/1.21    spl5_64 | ~spl5_65 | ~spl5_58),
% 6.13/1.21    inference(avatar_split_clause,[],[f2930,f2899,f2946,f2942])).
% 6.13/1.21  fof(f2942,plain,(
% 6.13/1.21    spl5_64 <=> sK0 = sK2),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 6.13/1.21  fof(f2899,plain,(
% 6.13/1.21    spl5_58 <=> r1_tarski(sK0,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 6.13/1.21  fof(f2930,plain,(
% 6.13/1.21    ~r1_tarski(sK2,sK0) | sK0 = sK2 | ~spl5_58),
% 6.13/1.21    inference(resolution,[],[f2901,f38])).
% 6.13/1.21  fof(f2901,plain,(
% 6.13/1.21    r1_tarski(sK0,sK2) | ~spl5_58),
% 6.13/1.21    inference(avatar_component_clause,[],[f2899])).
% 6.13/1.21  fof(f2940,plain,(
% 6.13/1.21    spl5_63 | ~spl5_58),
% 6.13/1.21    inference(avatar_split_clause,[],[f2927,f2899,f2937])).
% 6.13/1.21  fof(f2937,plain,(
% 6.13/1.21    spl5_63 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 6.13/1.21  fof(f2927,plain,(
% 6.13/1.21    sK0 = k3_xboole_0(sK0,sK2) | ~spl5_58),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2901,f35])).
% 6.13/1.21  fof(f2935,plain,(
% 6.13/1.21    ~spl5_62 | spl5_52 | ~spl5_58),
% 6.13/1.21    inference(avatar_split_clause,[],[f2928,f2899,f2275,f2932])).
% 6.13/1.21  fof(f2932,plain,(
% 6.13/1.21    spl5_62 <=> r2_hidden(sK3(sK2,sK2),sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 6.13/1.21  fof(f2928,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK0) | (spl5_52 | ~spl5_58)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2277,f2901,f39])).
% 6.13/1.21  fof(f2926,plain,(
% 6.13/1.21    ~spl5_61 | spl5_58),
% 6.13/1.21    inference(avatar_split_clause,[],[f2915,f2899,f2923])).
% 6.13/1.21  fof(f2915,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK0,sK2),sK2) | spl5_58),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2900,f41])).
% 6.13/1.21  fof(f2900,plain,(
% 6.13/1.21    ~r1_tarski(sK0,sK2) | spl5_58),
% 6.13/1.21    inference(avatar_component_clause,[],[f2899])).
% 6.13/1.21  fof(f2921,plain,(
% 6.13/1.21    spl5_60 | spl5_58),
% 6.13/1.21    inference(avatar_split_clause,[],[f2916,f2899,f2918])).
% 6.13/1.21  fof(f2916,plain,(
% 6.13/1.21    r2_hidden(sK3(sK0,sK2),sK0) | spl5_58),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f2900,f40])).
% 6.13/1.21  fof(f2914,plain,(
% 6.13/1.21    spl5_59 | ~spl5_7 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2830,f1561,f160,f2910])).
% 6.13/1.21  fof(f2910,plain,(
% 6.13/1.21    spl5_59 <=> r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 6.13/1.21  fof(f1561,plain,(
% 6.13/1.21    spl5_27 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 6.13/1.21  fof(f2830,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_7 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f162,f1563,f69])).
% 6.13/1.21  fof(f1563,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | ~spl5_27),
% 6.13/1.21    inference(avatar_component_clause,[],[f1561])).
% 6.13/1.21  fof(f2913,plain,(
% 6.13/1.21    spl5_59 | ~spl5_7 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2908,f1561,f160,f2910])).
% 6.13/1.21  fof(f2908,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k5_xboole_0(sK1,sK1)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_7 | ~spl5_27)),
% 6.13/1.21    inference(forward_demodulation,[],[f2824,f60])).
% 6.13/1.21  fof(f2824,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k5_xboole_0(sK1,sK1))),sK1) | (~spl5_7 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f162,f1563,f69])).
% 6.13/1.21  fof(f2907,plain,(
% 6.13/1.21    spl5_58 | ~spl5_19 | ~spl5_37),
% 6.13/1.21    inference(avatar_split_clause,[],[f2906,f1690,f1500,f2899])).
% 6.13/1.21  fof(f1500,plain,(
% 6.13/1.21    spl5_19 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 6.13/1.21  fof(f1690,plain,(
% 6.13/1.21    spl5_37 <=> sK2 = k3_tarski(sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 6.13/1.21  fof(f2906,plain,(
% 6.13/1.21    r1_tarski(sK0,sK2) | (~spl5_19 | ~spl5_37)),
% 6.13/1.21    inference(forward_demodulation,[],[f2890,f1692])).
% 6.13/1.21  fof(f1692,plain,(
% 6.13/1.21    sK2 = k3_tarski(sK1) | ~spl5_37),
% 6.13/1.21    inference(avatar_component_clause,[],[f1690])).
% 6.13/1.21  fof(f2890,plain,(
% 6.13/1.21    r1_tarski(sK0,k3_tarski(sK1)) | ~spl5_19),
% 6.13/1.21    inference(superposition,[],[f674,f1502])).
% 6.13/1.21  fof(f1502,plain,(
% 6.13/1.21    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_19),
% 6.13/1.21    inference(avatar_component_clause,[],[f1500])).
% 6.13/1.21  fof(f2905,plain,(
% 6.13/1.21    spl5_57 | ~spl5_19),
% 6.13/1.21    inference(avatar_split_clause,[],[f2904,f1500,f2893])).
% 6.13/1.21  fof(f2893,plain,(
% 6.13/1.21    spl5_57 <=> sK0 = k3_tarski(sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 6.13/1.21  fof(f2904,plain,(
% 6.13/1.21    sK0 = k3_tarski(sK1) | ~spl5_19),
% 6.13/1.21    inference(forward_demodulation,[],[f2903,f1912])).
% 6.13/1.21  fof(f2903,plain,(
% 6.13/1.21    k3_tarski(sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) | ~spl5_19),
% 6.13/1.21    inference(forward_demodulation,[],[f2883,f98])).
% 6.13/1.21  fof(f2883,plain,(
% 6.13/1.21    k3_tarski(sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) | ~spl5_19),
% 6.13/1.21    inference(superposition,[],[f61,f1502])).
% 6.13/1.21  fof(f2902,plain,(
% 6.13/1.21    spl5_58 | ~spl5_19 | ~spl5_37),
% 6.13/1.21    inference(avatar_split_clause,[],[f2897,f1690,f1500,f2899])).
% 6.13/1.21  fof(f2897,plain,(
% 6.13/1.21    r1_tarski(sK0,sK2) | (~spl5_19 | ~spl5_37)),
% 6.13/1.21    inference(forward_demodulation,[],[f2882,f1692])).
% 6.13/1.21  fof(f2882,plain,(
% 6.13/1.21    r1_tarski(sK0,k3_tarski(sK1)) | ~spl5_19),
% 6.13/1.21    inference(superposition,[],[f59,f1502])).
% 6.13/1.21  fof(f2896,plain,(
% 6.13/1.21    spl5_57 | ~spl5_19),
% 6.13/1.21    inference(avatar_split_clause,[],[f2881,f1500,f2893])).
% 6.13/1.21  fof(f2881,plain,(
% 6.13/1.21    sK0 = k3_tarski(sK1) | ~spl5_19),
% 6.13/1.21    inference(superposition,[],[f58,f1502])).
% 6.13/1.21  fof(f2866,plain,(
% 6.13/1.21    spl5_56 | ~spl5_2 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2865,f1561,f83,f2858])).
% 6.13/1.21  fof(f2858,plain,(
% 6.13/1.21    spl5_56 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 6.13/1.21  fof(f2865,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_2 | ~spl5_27)),
% 6.13/1.21    inference(forward_demodulation,[],[f2822,f60])).
% 6.13/1.21  fof(f2822,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2),sK1) | (~spl5_2 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f1563,f69])).
% 6.13/1.21  fof(f2864,plain,(
% 6.13/1.21    spl5_55 | ~spl5_3 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2863,f1561,f88,f2853])).
% 6.13/1.21  fof(f2853,plain,(
% 6.13/1.21    spl5_55 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 6.13/1.21  fof(f2863,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_3 | ~spl5_27)),
% 6.13/1.21    inference(forward_demodulation,[],[f2823,f60])).
% 6.13/1.21  fof(f2823,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK0),sK1) | (~spl5_3 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f1563,f69])).
% 6.13/1.21  fof(f2862,plain,(
% 6.13/1.21    spl5_54 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2827,f1561,f2848])).
% 6.13/1.21  fof(f2848,plain,(
% 6.13/1.21    spl5_54 <=> r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 6.13/1.21  fof(f2827,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl5_27),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1563,f1563,f69])).
% 6.13/1.21  fof(f2861,plain,(
% 6.13/1.21    spl5_56 | ~spl5_2 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2828,f1561,f83,f2858])).
% 6.13/1.21  fof(f2828,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_2 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f1563,f69])).
% 6.13/1.21  fof(f2856,plain,(
% 6.13/1.21    spl5_55 | ~spl5_3 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2829,f1561,f88,f2853])).
% 6.13/1.21  fof(f2829,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | (~spl5_3 | ~spl5_27)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f1563,f69])).
% 6.13/1.21  fof(f2851,plain,(
% 6.13/1.21    spl5_54 | ~spl5_27),
% 6.13/1.21    inference(avatar_split_clause,[],[f2833,f1561,f2848])).
% 6.13/1.21  fof(f2833,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | ~spl5_27),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1563,f1563,f69])).
% 6.13/1.21  fof(f2289,plain,(
% 6.13/1.21    ~spl5_37 | spl5_39 | ~spl5_51),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f2288])).
% 6.13/1.21  fof(f2288,plain,(
% 6.13/1.21    $false | (~spl5_37 | spl5_39 | ~spl5_51)),
% 6.13/1.21    inference(subsumption_resolution,[],[f2273,f2259])).
% 6.13/1.21  fof(f2259,plain,(
% 6.13/1.21    ( ! [X0] : (~r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),X0),sK2)) ) | (~spl5_37 | spl5_39)),
% 6.13/1.21    inference(backward_demodulation,[],[f1845,f1692])).
% 6.13/1.21  fof(f1845,plain,(
% 6.13/1.21    ( ! [X0] : (~r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),X0),sK2)) ) | spl5_39),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f525,f1704,f39])).
% 6.13/1.21  fof(f1704,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | spl5_39),
% 6.13/1.21    inference(avatar_component_clause,[],[f1703])).
% 6.13/1.21  fof(f1703,plain,(
% 6.13/1.21    spl5_39 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 6.13/1.21  fof(f525,plain,(
% 6.13/1.21    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f72,f71])).
% 6.13/1.21  fof(f71,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 6.13/1.21    inference(definition_unfolding,[],[f50,f55])).
% 6.13/1.21  fof(f50,plain,(
% 6.13/1.21    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 6.13/1.21    inference(cnf_transformation,[],[f16])).
% 6.13/1.21  fof(f2273,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) | (~spl5_37 | ~spl5_51)),
% 6.13/1.21    inference(backward_demodulation,[],[f2237,f1692])).
% 6.13/1.21  fof(f2237,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_51),
% 6.13/1.21    inference(avatar_component_clause,[],[f2235])).
% 6.13/1.21  fof(f2235,plain,(
% 6.13/1.21    spl5_51 <=> r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 6.13/1.21  fof(f2286,plain,(
% 6.13/1.21    spl5_53 | ~spl5_37 | ~spl5_46),
% 6.13/1.21    inference(avatar_split_clause,[],[f2254,f1824,f1690,f2283])).
% 6.13/1.21  fof(f2283,plain,(
% 6.13/1.21    spl5_53 <=> r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 6.13/1.21  fof(f1824,plain,(
% 6.13/1.21    spl5_46 <=> r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 6.13/1.21  fof(f2254,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) | (~spl5_37 | ~spl5_46)),
% 6.13/1.21    inference(backward_demodulation,[],[f1826,f1692])).
% 6.13/1.21  fof(f1826,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_46),
% 6.13/1.21    inference(avatar_component_clause,[],[f1824])).
% 6.13/1.21  fof(f2281,plain,(
% 6.13/1.21    ~spl5_52 | ~spl5_37 | spl5_44),
% 6.13/1.21    inference(avatar_split_clause,[],[f2252,f1792,f1690,f2275])).
% 6.13/1.21  fof(f1792,plain,(
% 6.13/1.21    spl5_44 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 6.13/1.21  fof(f2252,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_37 | spl5_44)),
% 6.13/1.21    inference(backward_demodulation,[],[f1794,f1692])).
% 6.13/1.21  fof(f1794,plain,(
% 6.13/1.21    ~r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) | spl5_44),
% 6.13/1.21    inference(avatar_component_clause,[],[f1792])).
% 6.13/1.21  fof(f2280,plain,(
% 6.13/1.21    ~spl5_52 | ~spl5_37 | spl5_43),
% 6.13/1.21    inference(avatar_split_clause,[],[f2251,f1787,f1690,f2275])).
% 6.13/1.21  fof(f1787,plain,(
% 6.13/1.21    spl5_43 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 6.13/1.21  fof(f2251,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_37 | spl5_43)),
% 6.13/1.21    inference(backward_demodulation,[],[f1788,f1692])).
% 6.13/1.21  fof(f1788,plain,(
% 6.13/1.21    ~r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | spl5_43),
% 6.13/1.21    inference(avatar_component_clause,[],[f1787])).
% 6.13/1.21  fof(f2279,plain,(
% 6.13/1.21    ~spl5_52 | ~spl5_37 | spl5_40),
% 6.13/1.21    inference(avatar_split_clause,[],[f2248,f1708,f1690,f2275])).
% 6.13/1.21  fof(f1708,plain,(
% 6.13/1.21    spl5_40 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 6.13/1.21  fof(f2248,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_37 | spl5_40)),
% 6.13/1.21    inference(backward_demodulation,[],[f1710,f1692])).
% 6.13/1.21  fof(f1710,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) | spl5_40),
% 6.13/1.21    inference(avatar_component_clause,[],[f1708])).
% 6.13/1.21  fof(f2278,plain,(
% 6.13/1.21    ~spl5_52 | ~spl5_37 | spl5_39),
% 6.13/1.21    inference(avatar_split_clause,[],[f2247,f1703,f1690,f2275])).
% 6.13/1.21  fof(f2247,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_37 | spl5_39)),
% 6.13/1.21    inference(backward_demodulation,[],[f1704,f1692])).
% 6.13/1.21  fof(f2245,plain,(
% 6.13/1.21    spl5_37 | ~spl5_38 | ~spl5_42),
% 6.13/1.21    inference(avatar_split_clause,[],[f2244,f1775,f1695,f1690])).
% 6.13/1.21  fof(f1695,plain,(
% 6.13/1.21    spl5_38 <=> r1_tarski(sK2,k3_tarski(sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 6.13/1.21  fof(f1775,plain,(
% 6.13/1.21    spl5_42 <=> r1_tarski(k3_tarski(sK1),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 6.13/1.21  fof(f2244,plain,(
% 6.13/1.21    sK2 = k3_tarski(sK1) | (~spl5_38 | ~spl5_42)),
% 6.13/1.21    inference(subsumption_resolution,[],[f1800,f1697])).
% 6.13/1.21  fof(f1697,plain,(
% 6.13/1.21    r1_tarski(sK2,k3_tarski(sK1)) | ~spl5_38),
% 6.13/1.21    inference(avatar_component_clause,[],[f1695])).
% 6.13/1.21  fof(f1800,plain,(
% 6.13/1.21    ~r1_tarski(sK2,k3_tarski(sK1)) | sK2 = k3_tarski(sK1) | ~spl5_42),
% 6.13/1.21    inference(resolution,[],[f1776,f38])).
% 6.13/1.21  fof(f1776,plain,(
% 6.13/1.21    r1_tarski(k3_tarski(sK1),sK2) | ~spl5_42),
% 6.13/1.21    inference(avatar_component_clause,[],[f1775])).
% 6.13/1.21  fof(f2242,plain,(
% 6.13/1.21    spl5_37 | ~spl5_42 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1833,f1695,f1775,f1690])).
% 6.13/1.21  fof(f1833,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_38),
% 6.13/1.21    inference(resolution,[],[f1697,f38])).
% 6.13/1.21  fof(f2241,plain,(
% 6.13/1.21    spl5_37 | ~spl5_42 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1768,f1695,f1775,f1690])).
% 6.13/1.21  fof(f1768,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_38),
% 6.13/1.21    inference(resolution,[],[f1697,f38])).
% 6.13/1.21  fof(f2240,plain,(
% 6.13/1.21    spl5_37 | ~spl5_42 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f2195,f1695,f1775,f1690])).
% 6.13/1.21  fof(f2195,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_38),
% 6.13/1.21    inference(resolution,[],[f1697,f38])).
% 6.13/1.21  fof(f2239,plain,(
% 6.13/1.21    spl5_51 | ~spl5_43),
% 6.13/1.21    inference(avatar_split_clause,[],[f2215,f1787,f2235])).
% 6.13/1.21  fof(f2215,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_43),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1789,f1789,f69])).
% 6.13/1.21  fof(f1789,plain,(
% 6.13/1.21    r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | ~spl5_43),
% 6.13/1.21    inference(avatar_component_clause,[],[f1787])).
% 6.13/1.21  fof(f2238,plain,(
% 6.13/1.21    spl5_51 | ~spl5_43),
% 6.13/1.21    inference(avatar_split_clause,[],[f2216,f1787,f2235])).
% 6.13/1.21  fof(f2216,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_43),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1789,f1789,f69])).
% 6.13/1.21  fof(f2233,plain,(
% 6.13/1.21    spl5_50 | ~spl5_43 | spl5_44),
% 6.13/1.21    inference(avatar_split_clause,[],[f2219,f1792,f1787,f2230])).
% 6.13/1.21  fof(f2230,plain,(
% 6.13/1.21    spl5_50 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 6.13/1.21  fof(f2219,plain,(
% 6.13/1.21    r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2))) | (~spl5_43 | spl5_44)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1794,f1789,f74])).
% 6.13/1.21  fof(f2189,plain,(
% 6.13/1.21    spl5_48 | ~spl5_47),
% 6.13/1.21    inference(avatar_split_clause,[],[f2179,f1871,f2038])).
% 6.13/1.21  fof(f2038,plain,(
% 6.13/1.21    spl5_48 <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 6.13/1.21  fof(f1871,plain,(
% 6.13/1.21    spl5_47 <=> k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 6.13/1.21  fof(f2179,plain,(
% 6.13/1.21    k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | ~spl5_47),
% 6.13/1.21    inference(forward_demodulation,[],[f1873,f1912])).
% 6.13/1.21  fof(f1873,plain,(
% 6.13/1.21    k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | ~spl5_47),
% 6.13/1.21    inference(avatar_component_clause,[],[f1871])).
% 6.13/1.21  fof(f2188,plain,(
% 6.13/1.21    spl5_48 | ~spl5_41),
% 6.13/1.21    inference(avatar_split_clause,[],[f2182,f1770,f2038])).
% 6.13/1.21  fof(f1770,plain,(
% 6.13/1.21    spl5_41 <=> sK2 = k3_xboole_0(sK2,k3_tarski(sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 6.13/1.21  fof(f2182,plain,(
% 6.13/1.21    k3_tarski(sK1) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | ~spl5_41),
% 6.13/1.21    inference(forward_demodulation,[],[f1869,f1912])).
% 6.13/1.21  fof(f1869,plain,(
% 6.13/1.21    k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | ~spl5_41),
% 6.13/1.21    inference(forward_demodulation,[],[f1868,f60])).
% 6.13/1.21  fof(f1868,plain,(
% 6.13/1.21    k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) | ~spl5_41),
% 6.13/1.21    inference(forward_demodulation,[],[f1864,f1755])).
% 6.13/1.21  fof(f1864,plain,(
% 6.13/1.21    k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k5_xboole_0(sK2,sK2))) | ~spl5_41),
% 6.13/1.21    inference(superposition,[],[f62,f1772])).
% 6.13/1.21  fof(f1772,plain,(
% 6.13/1.21    sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) | ~spl5_41),
% 6.13/1.21    inference(avatar_component_clause,[],[f1770])).
% 6.13/1.21  fof(f2187,plain,(
% 6.13/1.21    spl5_38 | spl5_39),
% 6.13/1.21    inference(avatar_split_clause,[],[f1834,f1703,f1695])).
% 6.13/1.21  fof(f1834,plain,(
% 6.13/1.21    r1_tarski(sK2,k3_tarski(sK1)) | spl5_39),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1704,f40])).
% 6.13/1.21  fof(f2186,plain,(
% 6.13/1.21    spl5_38 | spl5_39),
% 6.13/1.21    inference(avatar_split_clause,[],[f1846,f1703,f1695])).
% 6.13/1.21  fof(f1846,plain,(
% 6.13/1.21    r1_tarski(sK2,k3_tarski(sK1)) | spl5_39),
% 6.13/1.21    inference(resolution,[],[f1704,f40])).
% 6.13/1.21  fof(f2184,plain,(
% 6.13/1.21    ~spl5_41 | spl5_48),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f2183])).
% 6.13/1.21  fof(f2183,plain,(
% 6.13/1.21    $false | (~spl5_41 | spl5_48)),
% 6.13/1.21    inference(subsumption_resolution,[],[f2182,f2040])).
% 6.13/1.21  fof(f2040,plain,(
% 6.13/1.21    k3_tarski(sK1) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | spl5_48),
% 6.13/1.21    inference(avatar_component_clause,[],[f2038])).
% 6.13/1.21  fof(f2181,plain,(
% 6.13/1.21    ~spl5_47 | spl5_48),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f2180])).
% 6.13/1.21  fof(f2180,plain,(
% 6.13/1.21    $false | (~spl5_47 | spl5_48)),
% 6.13/1.21    inference(subsumption_resolution,[],[f2179,f2040])).
% 6.13/1.21  fof(f2178,plain,(
% 6.13/1.21    spl5_49 | ~spl5_39 | spl5_40),
% 6.13/1.21    inference(avatar_split_clause,[],[f2164,f1708,f1703,f2175])).
% 6.13/1.21  fof(f2175,plain,(
% 6.13/1.21    spl5_49 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1))))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 6.13/1.21  fof(f2164,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1)))) | (~spl5_39 | spl5_40)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1705,f1710,f74])).
% 6.13/1.21  fof(f1705,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | ~spl5_39),
% 6.13/1.21    inference(avatar_component_clause,[],[f1703])).
% 6.13/1.21  fof(f2041,plain,(
% 6.13/1.21    ~spl5_48 | spl5_47),
% 6.13/1.21    inference(avatar_split_clause,[],[f2002,f1871,f2038])).
% 6.13/1.21  fof(f2002,plain,(
% 6.13/1.21    k3_tarski(sK1) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | spl5_47),
% 6.13/1.21    inference(backward_demodulation,[],[f1872,f1912])).
% 6.13/1.21  fof(f1872,plain,(
% 6.13/1.21    k5_xboole_0(k3_tarski(sK1),k5_xboole_0(sK2,sK2)) != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_tarski(sK1))) | spl5_47),
% 6.13/1.21    inference(avatar_component_clause,[],[f1871])).
% 6.13/1.21  fof(f1874,plain,(
% 6.13/1.21    spl5_47 | ~spl5_41),
% 6.13/1.21    inference(avatar_split_clause,[],[f1869,f1770,f1871])).
% 6.13/1.21  fof(f1828,plain,(
% 6.13/1.21    spl5_46 | ~spl5_39),
% 6.13/1.21    inference(avatar_split_clause,[],[f1808,f1703,f1824])).
% 6.13/1.21  fof(f1808,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_39),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1705,f1705,f69])).
% 6.13/1.21  fof(f1827,plain,(
% 6.13/1.21    spl5_46 | ~spl5_39),
% 6.13/1.21    inference(avatar_split_clause,[],[f1809,f1703,f1824])).
% 6.13/1.21  fof(f1809,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_39),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1705,f1705,f69])).
% 6.13/1.21  fof(f1805,plain,(
% 6.13/1.21    spl5_45 | ~spl5_42),
% 6.13/1.21    inference(avatar_split_clause,[],[f1799,f1775,f1802])).
% 6.13/1.21  fof(f1802,plain,(
% 6.13/1.21    spl5_45 <=> k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 6.13/1.21  fof(f1799,plain,(
% 6.13/1.21    k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2) | ~spl5_42),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1776,f35])).
% 6.13/1.21  fof(f1795,plain,(
% 6.13/1.21    ~spl5_44 | spl5_42),
% 6.13/1.21    inference(avatar_split_clause,[],[f1784,f1775,f1792])).
% 6.13/1.21  fof(f1784,plain,(
% 6.13/1.21    ~r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) | spl5_42),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1777,f41])).
% 6.13/1.21  fof(f1777,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | spl5_42),
% 6.13/1.21    inference(avatar_component_clause,[],[f1775])).
% 6.13/1.21  fof(f1790,plain,(
% 6.13/1.21    spl5_43 | spl5_42),
% 6.13/1.21    inference(avatar_split_clause,[],[f1785,f1775,f1787])).
% 6.13/1.21  fof(f1785,plain,(
% 6.13/1.21    r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | spl5_42),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1777,f40])).
% 6.13/1.21  fof(f1781,plain,(
% 6.13/1.21    ~spl5_42 | spl5_37 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1780,f1695,f1690,f1775])).
% 6.13/1.21  fof(f1780,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | (spl5_37 | ~spl5_38)),
% 6.13/1.21    inference(subsumption_resolution,[],[f1768,f1691])).
% 6.13/1.21  fof(f1691,plain,(
% 6.13/1.21    sK2 != k3_tarski(sK1) | spl5_37),
% 6.13/1.21    inference(avatar_component_clause,[],[f1690])).
% 6.13/1.21  fof(f1779,plain,(
% 6.13/1.21    ~spl5_42 | spl5_37 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1765,f1695,f1690,f1775])).
% 6.13/1.21  fof(f1765,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | (spl5_37 | ~spl5_38)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1691,f1697,f38])).
% 6.13/1.21  fof(f1778,plain,(
% 6.13/1.21    ~spl5_42 | spl5_37 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1766,f1695,f1690,f1775])).
% 6.13/1.21  fof(f1766,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(sK1),sK2) | (spl5_37 | ~spl5_38)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1691,f1697,f38])).
% 6.13/1.21  fof(f1773,plain,(
% 6.13/1.21    spl5_41 | ~spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1767,f1695,f1770])).
% 6.13/1.21  fof(f1767,plain,(
% 6.13/1.21    sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) | ~spl5_38),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1697,f35])).
% 6.13/1.21  fof(f1711,plain,(
% 6.13/1.21    ~spl5_40 | spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1700,f1695,f1708])).
% 6.13/1.21  fof(f1700,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) | spl5_38),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1696,f41])).
% 6.13/1.21  fof(f1696,plain,(
% 6.13/1.21    ~r1_tarski(sK2,k3_tarski(sK1)) | spl5_38),
% 6.13/1.21    inference(avatar_component_clause,[],[f1695])).
% 6.13/1.21  fof(f1706,plain,(
% 6.13/1.21    spl5_39 | spl5_38),
% 6.13/1.21    inference(avatar_split_clause,[],[f1701,f1695,f1703])).
% 6.13/1.21  fof(f1701,plain,(
% 6.13/1.21    r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | spl5_38),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1696,f40])).
% 6.13/1.21  fof(f1699,plain,(
% 6.13/1.21    spl5_38 | ~spl5_25),
% 6.13/1.21    inference(avatar_split_clause,[],[f1687,f1548,f1695])).
% 6.13/1.21  fof(f1687,plain,(
% 6.13/1.21    r1_tarski(sK2,k3_tarski(sK1)) | ~spl5_25),
% 6.13/1.21    inference(superposition,[],[f674,f1550])).
% 6.13/1.21  fof(f1550,plain,(
% 6.13/1.21    sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_25),
% 6.13/1.21    inference(avatar_component_clause,[],[f1548])).
% 6.13/1.21  fof(f1698,plain,(
% 6.13/1.21    spl5_38 | ~spl5_25),
% 6.13/1.21    inference(avatar_split_clause,[],[f1680,f1548,f1695])).
% 6.13/1.21  fof(f1680,plain,(
% 6.13/1.21    r1_tarski(sK2,k3_tarski(sK1)) | ~spl5_25),
% 6.13/1.21    inference(superposition,[],[f59,f1550])).
% 6.13/1.21  fof(f1693,plain,(
% 6.13/1.21    spl5_37 | ~spl5_25),
% 6.13/1.21    inference(avatar_split_clause,[],[f1679,f1548,f1690])).
% 6.13/1.21  fof(f1679,plain,(
% 6.13/1.21    sK2 = k3_tarski(sK1) | ~spl5_25),
% 6.13/1.21    inference(superposition,[],[f58,f1550])).
% 6.13/1.21  fof(f1667,plain,(
% 6.13/1.21    ~spl5_36 | spl5_26),
% 6.13/1.21    inference(avatar_split_clause,[],[f1656,f1552,f1664])).
% 6.13/1.21  fof(f1664,plain,(
% 6.13/1.21    spl5_36 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 6.13/1.21  fof(f1656,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl5_26),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1554,f41])).
% 6.13/1.21  fof(f1662,plain,(
% 6.13/1.21    spl5_35 | spl5_26),
% 6.13/1.21    inference(avatar_split_clause,[],[f1657,f1552,f1659])).
% 6.13/1.21  fof(f1659,plain,(
% 6.13/1.21    spl5_35 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 6.13/1.21  fof(f1657,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1) | spl5_26),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1554,f40])).
% 6.13/1.21  fof(f1649,plain,(
% 6.13/1.21    ~spl5_34 | ~spl5_16 | spl5_31),
% 6.13/1.21    inference(avatar_split_clause,[],[f1638,f1602,f1463,f1646])).
% 6.13/1.21  fof(f1646,plain,(
% 6.13/1.21    spl5_34 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 6.13/1.21  fof(f1638,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | (~spl5_16 | spl5_31)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1604,f1465,f39])).
% 6.13/1.21  fof(f1631,plain,(
% 6.13/1.21    ~spl5_33 | ~spl5_15 | spl5_31),
% 6.13/1.21    inference(avatar_split_clause,[],[f1617,f1602,f1457,f1628])).
% 6.13/1.21  fof(f1628,plain,(
% 6.13/1.21    spl5_33 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 6.13/1.21  fof(f1617,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (~spl5_15 | spl5_31)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1459,f1604,f39])).
% 6.13/1.21  fof(f1626,plain,(
% 6.13/1.21    ~spl5_32 | ~spl5_17 | spl5_31),
% 6.13/1.21    inference(avatar_split_clause,[],[f1618,f1602,f1472,f1623])).
% 6.13/1.21  fof(f1623,plain,(
% 6.13/1.21    spl5_32 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 6.13/1.21  fof(f1618,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | (~spl5_17 | spl5_31)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1474,f1604,f39])).
% 6.13/1.21  fof(f1606,plain,(
% 6.13/1.21    ~spl5_31 | ~spl5_22 | spl5_30),
% 6.13/1.21    inference(avatar_split_clause,[],[f1595,f1580,f1524,f1602])).
% 6.13/1.21  fof(f1524,plain,(
% 6.13/1.21    spl5_22 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 6.13/1.21  fof(f1580,plain,(
% 6.13/1.21    spl5_30 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 6.13/1.21  fof(f1595,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),sK1) | (~spl5_22 | spl5_30)),
% 6.13/1.21    inference(backward_demodulation,[],[f1582,f1526])).
% 6.13/1.21  fof(f1526,plain,(
% 6.13/1.21    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2) | ~spl5_22),
% 6.13/1.21    inference(avatar_component_clause,[],[f1524])).
% 6.13/1.21  fof(f1582,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_30),
% 6.13/1.21    inference(avatar_component_clause,[],[f1580])).
% 6.13/1.21  fof(f1605,plain,(
% 6.13/1.21    ~spl5_31 | ~spl5_22 | spl5_29),
% 6.13/1.21    inference(avatar_split_clause,[],[f1594,f1575,f1524,f1602])).
% 6.13/1.21  fof(f1575,plain,(
% 6.13/1.21    spl5_29 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 6.13/1.21  fof(f1594,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,sK1),sK1) | (~spl5_22 | spl5_29)),
% 6.13/1.21    inference(backward_demodulation,[],[f1576,f1526])).
% 6.13/1.21  fof(f1576,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) | spl5_29),
% 6.13/1.21    inference(avatar_component_clause,[],[f1575])).
% 6.13/1.21  fof(f1600,plain,(
% 6.13/1.21    spl5_14 | ~spl5_22),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f1599])).
% 6.13/1.21  fof(f1599,plain,(
% 6.13/1.21    $false | (spl5_14 | ~spl5_22)),
% 6.13/1.21    inference(subsumption_resolution,[],[f1598,f72])).
% 6.13/1.21  fof(f1598,plain,(
% 6.13/1.21    ~r1_tarski(sK1,sK1) | (spl5_14 | ~spl5_22)),
% 6.13/1.21    inference(forward_demodulation,[],[f1585,f58])).
% 6.13/1.21  fof(f1585,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1)),sK1) | (spl5_14 | ~spl5_22)),
% 6.13/1.21    inference(backward_demodulation,[],[f1212,f1526])).
% 6.13/1.21  fof(f1212,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) | spl5_14),
% 6.13/1.21    inference(avatar_component_clause,[],[f1210])).
% 6.13/1.21  fof(f1210,plain,(
% 6.13/1.21    spl5_14 <=> r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 6.13/1.21  fof(f1597,plain,(
% 6.13/1.21    spl5_4 | ~spl5_22),
% 6.13/1.21    inference(avatar_contradiction_clause,[],[f1596])).
% 6.13/1.21  fof(f1596,plain,(
% 6.13/1.21    $false | (spl5_4 | ~spl5_22)),
% 6.13/1.21    inference(subsumption_resolution,[],[f1584,f58])).
% 6.13/1.21  fof(f1584,plain,(
% 6.13/1.21    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | (spl5_4 | ~spl5_22)),
% 6.13/1.21    inference(backward_demodulation,[],[f96,f1526])).
% 6.13/1.21  fof(f1583,plain,(
% 6.13/1.21    ~spl5_30 | spl5_23),
% 6.13/1.21    inference(avatar_split_clause,[],[f1572,f1528,f1580])).
% 6.13/1.21  fof(f1572,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_23),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1530,f41])).
% 6.13/1.21  fof(f1578,plain,(
% 6.13/1.21    spl5_29 | spl5_23),
% 6.13/1.21    inference(avatar_split_clause,[],[f1573,f1528,f1575])).
% 6.13/1.21  fof(f1573,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) | spl5_23),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1530,f40])).
% 6.13/1.21  fof(f1569,plain,(
% 6.13/1.21    ~spl5_28 | spl5_20),
% 6.13/1.21    inference(avatar_split_clause,[],[f1558,f1504,f1566])).
% 6.13/1.21  fof(f1566,plain,(
% 6.13/1.21    spl5_28 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 6.13/1.21  fof(f1504,plain,(
% 6.13/1.21    spl5_20 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 6.13/1.21  fof(f1558,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_20),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1506,f41])).
% 6.13/1.21  fof(f1506,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_20),
% 6.13/1.21    inference(avatar_component_clause,[],[f1504])).
% 6.13/1.21  fof(f1564,plain,(
% 6.13/1.21    spl5_27 | spl5_20),
% 6.13/1.21    inference(avatar_split_clause,[],[f1559,f1504,f1561])).
% 6.13/1.21  fof(f1559,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | spl5_20),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1506,f40])).
% 6.13/1.21  fof(f1555,plain,(
% 6.13/1.21    spl5_25 | ~spl5_26 | ~spl5_17),
% 6.13/1.21    inference(avatar_split_clause,[],[f1541,f1472,f1552,f1548])).
% 6.13/1.21  fof(f1541,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_17),
% 6.13/1.21    inference(resolution,[],[f1474,f38])).
% 6.13/1.21  fof(f1546,plain,(
% 6.13/1.21    spl5_24 | ~spl5_17),
% 6.13/1.21    inference(avatar_split_clause,[],[f1538,f1472,f1543])).
% 6.13/1.21  fof(f1543,plain,(
% 6.13/1.21    spl5_24 <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 6.13/1.21  fof(f1538,plain,(
% 6.13/1.21    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_17),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1474,f35])).
% 6.13/1.21  fof(f1531,plain,(
% 6.13/1.21    spl5_22 | ~spl5_23 | ~spl5_16),
% 6.13/1.21    inference(avatar_split_clause,[],[f1517,f1463,f1528,f1524])).
% 6.13/1.21  fof(f1517,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2) | ~spl5_16),
% 6.13/1.21    inference(resolution,[],[f1465,f38])).
% 6.13/1.21  fof(f1522,plain,(
% 6.13/1.21    spl5_21 | ~spl5_16),
% 6.13/1.21    inference(avatar_split_clause,[],[f1514,f1463,f1519])).
% 6.13/1.21  fof(f1519,plain,(
% 6.13/1.21    spl5_21 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 6.13/1.21  fof(f1514,plain,(
% 6.13/1.21    k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_16),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1465,f35])).
% 6.13/1.21  fof(f1507,plain,(
% 6.13/1.21    spl5_19 | ~spl5_20 | ~spl5_15),
% 6.13/1.21    inference(avatar_split_clause,[],[f1493,f1457,f1504,f1500])).
% 6.13/1.21  fof(f1493,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_15),
% 6.13/1.21    inference(resolution,[],[f1459,f38])).
% 6.13/1.21  fof(f1498,plain,(
% 6.13/1.21    spl5_18 | ~spl5_15),
% 6.13/1.21    inference(avatar_split_clause,[],[f1490,f1457,f1495])).
% 6.13/1.21  fof(f1495,plain,(
% 6.13/1.21    spl5_18 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 6.13/1.21  fof(f1490,plain,(
% 6.13/1.21    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_15),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f1459,f35])).
% 6.13/1.21  fof(f1475,plain,(
% 6.13/1.21    spl5_17 | ~spl5_2),
% 6.13/1.21    inference(avatar_split_clause,[],[f1421,f83,f1472])).
% 6.13/1.21  fof(f1421,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_2),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f85,f69])).
% 6.13/1.21  fof(f1470,plain,(
% 6.13/1.21    spl5_16 | ~spl5_2 | ~spl5_3),
% 6.13/1.21    inference(avatar_split_clause,[],[f1422,f88,f83,f1463])).
% 6.13/1.21  fof(f1422,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | (~spl5_2 | ~spl5_3)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f85,f69])).
% 6.13/1.21  fof(f1466,plain,(
% 6.13/1.21    spl5_16 | ~spl5_2 | ~spl5_3),
% 6.13/1.21    inference(avatar_split_clause,[],[f1461,f88,f83,f1463])).
% 6.13/1.21  fof(f1461,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | (~spl5_2 | ~spl5_3)),
% 6.13/1.21    inference(forward_demodulation,[],[f1426,f60])).
% 6.13/1.21  fof(f1426,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) | (~spl5_2 | ~spl5_3)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f90,f69])).
% 6.13/1.21  fof(f1460,plain,(
% 6.13/1.21    spl5_15 | ~spl5_3),
% 6.13/1.21    inference(avatar_split_clause,[],[f1427,f88,f1457])).
% 6.13/1.21  fof(f1427,plain,(
% 6.13/1.21    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_3),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f90,f90,f69])).
% 6.13/1.21  fof(f1214,plain,(
% 6.13/1.21    ~spl5_14 | spl5_4),
% 6.13/1.21    inference(avatar_split_clause,[],[f1207,f94,f1210])).
% 6.13/1.21  fof(f1207,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) | spl5_4),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f59,f96,f38])).
% 6.13/1.21  fof(f1213,plain,(
% 6.13/1.21    ~spl5_14 | spl5_4),
% 6.13/1.21    inference(avatar_split_clause,[],[f1208,f94,f1210])).
% 6.13/1.21  fof(f1208,plain,(
% 6.13/1.21    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) | spl5_4),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f59,f96,f38])).
% 6.13/1.21  fof(f969,plain,(
% 6.13/1.21    spl5_13 | ~spl5_2 | spl5_5),
% 6.13/1.21    inference(avatar_split_clause,[],[f936,f143,f83,f966])).
% 6.13/1.21  fof(f966,plain,(
% 6.13/1.21    spl5_13 <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 6.13/1.21  fof(f143,plain,(
% 6.13/1.21    spl5_5 <=> r2_hidden(sK2,k5_xboole_0(sK1,sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 6.13/1.21  fof(f936,plain,(
% 6.13/1.21    r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_2 | spl5_5)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f145,f74])).
% 6.13/1.21  fof(f145,plain,(
% 6.13/1.21    ~r2_hidden(sK2,k5_xboole_0(sK1,sK1)) | spl5_5),
% 6.13/1.21    inference(avatar_component_clause,[],[f143])).
% 6.13/1.21  fof(f964,plain,(
% 6.13/1.21    spl5_12 | ~spl5_7 | spl5_8),
% 6.13/1.21    inference(avatar_split_clause,[],[f939,f165,f160,f960])).
% 6.13/1.21  fof(f960,plain,(
% 6.13/1.21    spl5_12 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 6.13/1.21  fof(f165,plain,(
% 6.13/1.21    spl5_8 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 6.13/1.21  fof(f939,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_7 | spl5_8)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f162,f167,f74])).
% 6.13/1.21  fof(f167,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl5_8),
% 6.13/1.21    inference(avatar_component_clause,[],[f165])).
% 6.13/1.21  fof(f963,plain,(
% 6.13/1.21    spl5_12 | ~spl5_2 | spl5_8),
% 6.13/1.21    inference(avatar_split_clause,[],[f940,f165,f83,f960])).
% 6.13/1.21  fof(f940,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_2 | spl5_8)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f206,f167,f74])).
% 6.13/1.21  fof(f805,plain,(
% 6.13/1.21    spl5_11 | ~spl5_3),
% 6.13/1.21    inference(avatar_split_clause,[],[f799,f88,f802])).
% 6.13/1.21  fof(f802,plain,(
% 6.13/1.21    spl5_11 <=> r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 6.13/1.21  fof(f799,plain,(
% 6.13/1.21    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))) | ~spl5_3),
% 6.13/1.21    inference(superposition,[],[f694,f98])).
% 6.13/1.21  fof(f754,plain,(
% 6.13/1.21    spl5_10 | ~spl5_2),
% 6.13/1.21    inference(avatar_split_clause,[],[f748,f83,f751])).
% 6.13/1.21  fof(f751,plain,(
% 6.13/1.21    spl5_10 <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 6.13/1.21  fof(f748,plain,(
% 6.13/1.21    r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))) | ~spl5_2),
% 6.13/1.21    inference(superposition,[],[f693,f98])).
% 6.13/1.21  fof(f204,plain,(
% 6.13/1.21    ~spl5_9 | spl5_5),
% 6.13/1.21    inference(avatar_split_clause,[],[f198,f143,f201])).
% 6.13/1.21  fof(f201,plain,(
% 6.13/1.21    spl5_9 <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 6.13/1.21  fof(f198,plain,(
% 6.13/1.21    ~r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | spl5_5),
% 6.13/1.21    inference(backward_demodulation,[],[f174,f196])).
% 6.13/1.21  fof(f174,plain,(
% 6.13/1.21    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))) ) | spl5_5),
% 6.13/1.21    inference(forward_demodulation,[],[f170,f43])).
% 6.13/1.21  fof(f170,plain,(
% 6.13/1.21    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))) ) | spl5_5),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f145,f76])).
% 6.13/1.21  fof(f168,plain,(
% 6.13/1.21    ~spl5_8 | spl5_6),
% 6.13/1.21    inference(avatar_split_clause,[],[f157,f152,f165])).
% 6.13/1.21  fof(f157,plain,(
% 6.13/1.21    ~r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl5_6),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f154,f41])).
% 6.13/1.21  fof(f163,plain,(
% 6.13/1.21    spl5_7 | spl5_6),
% 6.13/1.21    inference(avatar_split_clause,[],[f158,f152,f160])).
% 6.13/1.21  fof(f158,plain,(
% 6.13/1.21    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) | spl5_6),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f154,f40])).
% 6.13/1.21  fof(f156,plain,(
% 6.13/1.21    ~spl5_6 | ~spl5_2 | spl5_5),
% 6.13/1.21    inference(avatar_split_clause,[],[f147,f143,f83,f152])).
% 6.13/1.21  fof(f147,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl5_2 | spl5_5)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f145,f105])).
% 6.13/1.21  fof(f155,plain,(
% 6.13/1.21    ~spl5_6 | ~spl5_2 | spl5_5),
% 6.13/1.21    inference(avatar_split_clause,[],[f148,f143,f83,f152])).
% 6.13/1.21  fof(f148,plain,(
% 6.13/1.21    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl5_2 | spl5_5)),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f145,f39])).
% 6.13/1.21  fof(f146,plain,(
% 6.13/1.21    ~spl5_5 | ~spl5_2),
% 6.13/1.21    inference(avatar_split_clause,[],[f141,f83,f143])).
% 6.13/1.21  fof(f141,plain,(
% 6.13/1.21    ~r2_hidden(sK2,k5_xboole_0(sK1,sK1)) | ~spl5_2),
% 6.13/1.21    inference(superposition,[],[f129,f98])).
% 6.13/1.21  fof(f129,plain,(
% 6.13/1.21    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ) | ~spl5_2),
% 6.13/1.21    inference(unit_resulting_resolution,[],[f85,f75])).
% 6.13/1.21  fof(f97,plain,(
% 6.13/1.21    ~spl5_4 | spl5_1),
% 6.13/1.21    inference(avatar_split_clause,[],[f92,f78,f94])).
% 6.13/1.21  fof(f78,plain,(
% 6.13/1.21    spl5_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))),
% 6.13/1.21    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 6.13/1.21  fof(f92,plain,(
% 6.13/1.21    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl5_1),
% 6.13/1.21    inference(forward_demodulation,[],[f80,f60])).
% 6.13/1.21  fof(f80,plain,(
% 6.13/1.21    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) | spl5_1),
% 6.13/1.21    inference(avatar_component_clause,[],[f78])).
% 6.13/1.21  fof(f91,plain,(
% 6.13/1.21    spl5_3),
% 6.13/1.21    inference(avatar_split_clause,[],[f24,f88])).
% 6.13/1.21  fof(f24,plain,(
% 6.13/1.21    r2_hidden(sK0,sK1)),
% 6.13/1.21    inference(cnf_transformation,[],[f21])).
% 6.13/1.21  fof(f21,plain,(
% 6.13/1.21    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 6.13/1.21    inference(flattening,[],[f20])).
% 6.13/1.21  fof(f20,plain,(
% 6.13/1.21    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 6.13/1.21    inference(ennf_transformation,[],[f18])).
% 6.13/1.21  fof(f18,negated_conjecture,(
% 6.13/1.21    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 6.13/1.21    inference(negated_conjecture,[],[f17])).
% 6.13/1.21  fof(f17,conjecture,(
% 6.13/1.21    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 6.13/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 6.13/1.21  fof(f86,plain,(
% 6.13/1.21    spl5_2),
% 6.13/1.21    inference(avatar_split_clause,[],[f25,f83])).
% 6.13/1.21  fof(f25,plain,(
% 6.13/1.21    r2_hidden(sK2,sK1)),
% 6.13/1.21    inference(cnf_transformation,[],[f21])).
% 6.13/1.21  fof(f81,plain,(
% 6.13/1.21    ~spl5_1),
% 6.13/1.21    inference(avatar_split_clause,[],[f57,f78])).
% 6.13/1.21  fof(f57,plain,(
% 6.13/1.21    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))),
% 6.13/1.21    inference(definition_unfolding,[],[f26,f56,f55])).
% 6.13/1.21  fof(f26,plain,(
% 6.13/1.21    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 6.13/1.21    inference(cnf_transformation,[],[f21])).
% 6.13/1.21  % SZS output end Proof for theBenchmark
% 6.13/1.21  % (29356)------------------------------
% 6.13/1.21  % (29356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.13/1.21  % (29356)Termination reason: Refutation
% 6.13/1.21  
% 6.13/1.21  % (29356)Memory used [KB]: 4221
% 6.13/1.21  % (29356)Time elapsed: 0.773 s
% 6.13/1.21  % (29356)------------------------------
% 6.13/1.21  % (29356)------------------------------
% 6.72/1.23  % (29363)Time limit reached!
% 6.72/1.23  % (29363)------------------------------
% 6.72/1.23  % (29363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.72/1.23  % (29363)Termination reason: Time limit
% 6.72/1.23  
% 6.72/1.23  % (29363)Memory used [KB]: 4861
% 6.72/1.23  % (29363)Time elapsed: 0.821 s
% 6.72/1.23  % (29363)------------------------------
% 6.72/1.23  % (29363)------------------------------
% 6.72/1.23  % (29341)Success in time 0.861 s
%------------------------------------------------------------------------------

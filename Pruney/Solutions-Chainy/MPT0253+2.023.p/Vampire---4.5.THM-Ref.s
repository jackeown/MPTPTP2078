%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:09 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  495 (3333 expanded)
%              Number of leaves         :  114 (1221 expanded)
%              Depth                    :   14
%              Number of atoms          : 1074 (5969 expanded)
%              Number of equality atoms :  131 (2103 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f140,f149,f150,f157,f162,f198,f750,f751,f756,f1052,f1057,f1062,f1067,f1082,f1091,f1106,f1115,f1130,f1139,f1154,f1163,f1172,f1177,f1186,f1191,f1204,f1205,f1240,f1245,f1250,f1264,f1269,f1270,f1277,f1282,f1290,f1299,f1308,f1313,f1323,f1380,f1381,f1587,f1630,f1632,f1633,f1708,f1713,f1714,f1715,f1716,f1717,f1720,f1754,f1759,f1760,f1761,f1762,f1767,f1770,f1800,f1813,f1818,f1872,f1877,f2240,f2242,f2247,f2277,f2282,f2292,f2299,f2304,f2311,f2316,f2325,f2330,f2343,f2345,f2350,f2355,f2356,f2376,f2377,f2385,f2419,f2439,f2440,f2457,f2950,f2956,f2965,f2966,f2974,f2978,f2995,f3008,f3156,f3176,f3180,f3195,f3200,f3202,f3240,f3245,f3250,f3251,f3256,f3261,f3281,f3313,f3315,f3320,f3325])).

fof(f3325,plain,
    ( spl5_97
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f3289,f1049,f3322])).

fof(f3322,plain,
    ( spl5_97
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1049,plain,
    ( spl5_11
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f3289,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f1051,f1488])).

fof(f1488,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f1327,f1415])).

fof(f1415,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[],[f1347,f189])).

fof(f189,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(unit_resulting_resolution,[],[f180,f180,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f171,f40])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f171,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k5_xboole_0(X3,X3)) ),
    inference(subsumption_resolution,[],[f167,f129])).

fof(f129,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f75,f92])).

fof(f92,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    inference(cnf_transformation,[],[f5])).

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
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f167,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X3,X3))
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f76,f92])).

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
    inference(cnf_transformation,[],[f3])).

fof(f1347,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f1324,f92])).

fof(f1324,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f54])).

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

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f56,f32])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1327,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f61,f35])).

% (11133)Termination reason: Time limit

% (11133)Memory used [KB]: 14711
% (11133)Time elapsed: 0.531 s
% (11133)------------------------------
% (11133)------------------------------
fof(f1051,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f3320,plain,
    ( spl5_96
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f3290,f1054,f3317])).

fof(f3317,plain,
    ( spl5_96
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1054,plain,
    ( spl5_12
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f3290,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f1056,f1488])).

fof(f1056,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f3315,plain,
    ( ~ spl5_13
    | spl5_72 ),
    inference(avatar_contradiction_clause,[],[f3314])).

fof(f3314,plain,
    ( $false
    | ~ spl5_13
    | spl5_72 ),
    inference(subsumption_resolution,[],[f3291,f2354])).

fof(f2354,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl5_72 ),
    inference(avatar_component_clause,[],[f2352])).

fof(f2352,plain,
    ( spl5_72
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f3291,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f1061,f1488])).

fof(f1061,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1059,plain,
    ( spl5_13
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f3313,plain,
    ( spl5_95
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f3292,f1064,f3310])).

fof(f3310,plain,
    ( spl5_95
  <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f1064,plain,
    ( spl5_14
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f3292,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f1066,f1488])).

fof(f1066,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f3281,plain,
    ( spl5_94
    | ~ spl5_87
    | spl5_88 ),
    inference(avatar_split_clause,[],[f3266,f3197,f3192,f3278])).

fof(f3278,plain,
    ( spl5_94
  <=> r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f3192,plain,
    ( spl5_87
  <=> r2_hidden(sK3(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f3197,plain,
    ( spl5_88
  <=> r2_hidden(sK3(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f3266,plain,
    ( r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl5_87
    | spl5_88 ),
    inference(unit_resulting_resolution,[],[f3194,f3199,f74])).

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
    inference(cnf_transformation,[],[f3])).

fof(f3199,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl5_88 ),
    inference(avatar_component_clause,[],[f3197])).

fof(f3194,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f3192])).

fof(f3261,plain,
    ( spl5_93
    | ~ spl5_2
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3210,f3192,f83,f3258])).

fof(f3258,plain,
    ( spl5_93
  <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f83,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f3210,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1)
    | ~ spl5_2
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f85,f3194,f69])).

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

fof(f85,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f3256,plain,
    ( spl5_92
    | ~ spl5_3
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3211,f3192,f88,f3253])).

fof(f3253,plain,
    ( spl5_92
  <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f88,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f3211,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1)
    | ~ spl5_3
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f90,f3194,f69])).

fof(f90,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f3251,plain,
    ( spl5_89
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3216,f3192,f3237])).

fof(f3237,plain,
    ( spl5_89
  <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f3216,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f3194,f3194,f69])).

fof(f3250,plain,
    ( spl5_91
    | ~ spl5_2
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3217,f3192,f83,f3247])).

fof(f3247,plain,
    ( spl5_91
  <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f3217,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1)
    | ~ spl5_2
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f85,f3194,f69])).

fof(f3245,plain,
    ( spl5_90
    | ~ spl5_3
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3218,f3192,f88,f3242])).

fof(f3242,plain,
    ( spl5_90
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f3218,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1)
    | ~ spl5_3
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f90,f3194,f69])).

fof(f3240,plain,
    ( spl5_89
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3223,f3192,f3237])).

fof(f3223,plain,
    ( r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f3194,f3194,f69])).

fof(f3202,plain,
    ( spl5_87
    | spl5_84 ),
    inference(avatar_split_clause,[],[f3182,f3169,f3192])).

fof(f3169,plain,
    ( spl5_84
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f3182,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_84 ),
    inference(unit_resulting_resolution,[],[f72,f3171,f101])).

fof(f101,plain,(
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

fof(f3171,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_84 ),
    inference(avatar_component_clause,[],[f3169])).

fof(f3200,plain,
    ( ~ spl5_88
    | spl5_84 ),
    inference(avatar_split_clause,[],[f3189,f3169,f3197])).

fof(f3189,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl5_84 ),
    inference(unit_resulting_resolution,[],[f3171,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3195,plain,
    ( spl5_87
    | spl5_84 ),
    inference(avatar_split_clause,[],[f3190,f3169,f3192])).

fof(f3190,plain,
    ( r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_84 ),
    inference(unit_resulting_resolution,[],[f3171,f40])).

fof(f3180,plain,
    ( ~ spl5_84
    | spl5_86
    | ~ spl5_2
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f3166,f2382,f83,f3178,f3169])).

fof(f3178,plain,
    ( spl5_86
  <=> ! [X1] : r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f2382,plain,
    ( spl5_74
  <=> sK2 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f3166,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0)
        | ~ r1_tarski(sK1,sK2) )
    | ~ spl5_2
    | ~ spl5_74 ),
    inference(resolution,[],[f3157,f239])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),X1)
        | ~ r1_tarski(sK1,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f200,f39])).

fof(f200,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f179,f40])).

fof(f179,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k5_xboole_0(X0,X0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f171,f99])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f39,f85])).

fof(f3157,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,sK0) )
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f3146,f171])).

fof(f3146,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k5_xboole_0(sK2,sK2))
        | r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl5_74 ),
    inference(superposition,[],[f74,f2384])).

fof(f2384,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f2382])).

fof(f3176,plain,
    ( ~ spl5_84
    | spl5_85
    | ~ spl5_6
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f3165,f2382,f154,f3173,f3169])).

fof(f3173,plain,
    ( spl5_85
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f154,plain,
    ( spl5_6
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f3165,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_6
    | ~ spl5_74 ),
    inference(resolution,[],[f3157,f232])).

fof(f232,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f156,f39])).

fof(f156,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f3156,plain,
    ( spl5_83
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f3151,f2382,f3153])).

fof(f3153,plain,
    ( spl5_83
  <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f3151,plain,
    ( sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f3142,f1489])).

fof(f1489,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = X4 ),
    inference(backward_demodulation,[],[f1351,f1415])).

fof(f1351,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f1350,f1347])).

fof(f1350,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,X3)))) ),
    inference(forward_demodulation,[],[f1328,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1328,plain,(
    ! [X4,X3] : k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X3,X3))) ),
    inference(superposition,[],[f61,f190])).

fof(f190,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f180,f35])).

fof(f3142,plain,
    ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k5_xboole_0(sK2,sK2)))
    | ~ spl5_74 ),
    inference(superposition,[],[f62,f2384])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f56,f56,f32])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3008,plain,
    ( ~ spl5_74
    | spl5_78 ),
    inference(avatar_contradiction_clause,[],[f3007])).

fof(f3007,plain,
    ( $false
    | ~ spl5_74
    | spl5_78 ),
    inference(subsumption_resolution,[],[f2990,f180])).

fof(f2990,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,sK2),sK0)
    | ~ spl5_74
    | spl5_78 ),
    inference(backward_demodulation,[],[f2949,f2384])).

fof(f2949,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)
    | spl5_78 ),
    inference(avatar_component_clause,[],[f2947])).

fof(f2947,plain,
    ( spl5_78
  <=> r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f2995,plain,
    ( ~ spl5_81
    | spl5_59
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f2994,f2382,f2244,f2971])).

fof(f2971,plain,
    ( spl5_81
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f2244,plain,
    ( spl5_59
  <=> sK2 = k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f2994,plain,
    ( sK0 != sK2
    | spl5_59
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f2980,f1415])).

fof(f2980,plain,
    ( sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))
    | spl5_59
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f2246,f2384])).

fof(f2246,plain,
    ( sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | spl5_59 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2978,plain,
    ( spl5_62
    | spl5_82
    | spl5_65 ),
    inference(avatar_split_clause,[],[f2890,f2301,f2976,f2285])).

fof(f2285,plain,
    ( spl5_62
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2976,plain,
    ( spl5_82
  <=> ! [X2] : ~ r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f2301,plain,
    ( spl5_65
  <=> r2_hidden(sK3(sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f2890,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2)))
        | r1_tarski(sK2,sK0) )
    | spl5_65 ),
    inference(resolution,[],[f2408,f101])).

fof(f2408,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))
    | spl5_65 ),
    inference(unit_resulting_resolution,[],[f2303,f76])).

fof(f2303,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK0)
    | spl5_65 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2974,plain,
    ( ~ spl5_81
    | spl5_59 ),
    inference(avatar_split_clause,[],[f2969,f2244,f2971])).

fof(f2969,plain,
    ( sK0 != sK2
    | spl5_59 ),
    inference(subsumption_resolution,[],[f2968,f72])).

fof(f2968,plain,
    ( sK0 != sK2
    | ~ r1_tarski(sK0,sK0)
    | spl5_59 ),
    inference(inner_rewriting,[],[f2967])).

fof(f2967,plain,
    ( sK0 != sK2
    | ~ r1_tarski(sK2,sK0)
    | spl5_59 ),
    inference(forward_demodulation,[],[f2792,f1415])).

fof(f2792,plain,
    ( sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,sK2))
    | ~ r1_tarski(sK2,sK0)
    | spl5_59 ),
    inference(superposition,[],[f2246,f35])).

fof(f2966,plain,
    ( spl5_80
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f2917,f2416,f2962])).

fof(f2962,plain,
    ( spl5_80
  <=> r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f2416,plain,
    ( spl5_75
  <=> r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f2917,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f2418,f2418,f69])).

fof(f2418,plain,
    ( r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f2416])).

fof(f2965,plain,
    ( spl5_80
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f2918,f2416,f2962])).

fof(f2918,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f2418,f2418,f69])).

fof(f2956,plain,
    ( spl5_79
    | spl5_65
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f2951,f2416,f2301,f2953])).

fof(f2953,plain,
    ( spl5_79
  <=> r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f2951,plain,
    ( r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0))))
    | spl5_65
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f2923,f43])).

fof(f2923,plain,
    ( r2_hidden(sK3(sK2,sK0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)))
    | spl5_65
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f2303,f2418,f74])).

fof(f2950,plain,
    ( ~ spl5_78
    | spl5_65
    | ~ spl5_75 ),
    inference(avatar_split_clause,[],[f2931,f2416,f2301,f2947])).

fof(f2931,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)
    | spl5_65
    | ~ spl5_75 ),
    inference(unit_resulting_resolution,[],[f2303,f2418,f39])).

fof(f2457,plain,
    ( spl5_77
    | ~ spl5_66
    | spl5_67 ),
    inference(avatar_split_clause,[],[f2443,f2313,f2308,f2454])).

fof(f2454,plain,
    ( spl5_77
  <=> r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f2308,plain,
    ( spl5_66
  <=> r2_hidden(sK3(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f2313,plain,
    ( spl5_67
  <=> r2_hidden(sK3(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f2443,plain,
    ( r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))
    | ~ spl5_66
    | spl5_67 ),
    inference(unit_resulting_resolution,[],[f2310,f2315,f74])).

fof(f2315,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK2)
    | spl5_67 ),
    inference(avatar_component_clause,[],[f2313])).

fof(f2310,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f2308])).

fof(f2440,plain,
    ( spl5_76
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2420,f2308,f2436])).

fof(f2436,plain,
    ( spl5_76
  <=> r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f2420,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f2310,f2310,f69])).

fof(f2439,plain,
    ( spl5_76
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f2421,f2308,f2436])).

fof(f2421,plain,
    ( r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)
    | ~ spl5_66 ),
    inference(unit_resulting_resolution,[],[f2310,f2310,f69])).

fof(f2419,plain,
    ( spl5_75
    | ~ spl5_64
    | spl5_65 ),
    inference(avatar_split_clause,[],[f2405,f2301,f2296,f2416])).

fof(f2296,plain,
    ( spl5_64
  <=> r2_hidden(sK3(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f2405,plain,
    ( r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | ~ spl5_64
    | spl5_65 ),
    inference(unit_resulting_resolution,[],[f2298,f2303,f74])).

fof(f2298,plain,
    ( r2_hidden(sK3(sK2,sK0),sK2)
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f2296])).

fof(f2385,plain,
    ( spl5_74
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f2379,f2285,f2382])).

fof(f2379,plain,
    ( sK2 = k3_xboole_0(sK2,sK0)
    | ~ spl5_62 ),
    inference(unit_resulting_resolution,[],[f2286,f35])).

fof(f2286,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2377,plain,
    ( spl5_73
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f2357,f2296,f2373])).

fof(f2373,plain,
    ( spl5_73
  <=> r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2357,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2)
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f2298,f2298,f69])).

fof(f2376,plain,
    ( spl5_73
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f2358,f2296,f2373])).

fof(f2358,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2)
    | ~ spl5_64 ),
    inference(unit_resulting_resolution,[],[f2298,f2298,f69])).

fof(f2356,plain,
    ( ~ spl5_72
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2337,f78,f2352])).

fof(f78,plain,
    ( spl5_1
  <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2337,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f80,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f29,f56,f56])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f80,plain,
    ( sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f2355,plain,
    ( ~ spl5_72
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2336,f78,f2352])).

fof(f2336,plain,
    ( sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f80,f60])).

fof(f2350,plain,
    ( ~ spl5_71
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2335,f78,f2347])).

fof(f2347,plain,
    ( spl5_71
  <=> sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f2335,plain,
    ( sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))
    | spl5_1 ),
    inference(superposition,[],[f80,f61])).

fof(f2345,plain,
    ( ~ spl5_70
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2344,f78,f2340])).

fof(f2340,plain,
    ( spl5_70
  <=> r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f2344,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)
    | spl5_1 ),
    inference(forward_demodulation,[],[f2333,f60])).

fof(f2333,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f1206,f80,f38])).

fof(f1206,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(superposition,[],[f59,f60])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2343,plain,
    ( ~ spl5_70
    | spl5_1 ),
    inference(avatar_split_clause,[],[f2338,f78,f2340])).

fof(f2338,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)
    | spl5_1 ),
    inference(forward_demodulation,[],[f2334,f60])).

fof(f2334,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f1206,f80,f38])).

fof(f2330,plain,
    ( ~ spl5_69
    | spl5_51
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f2318,f2289,f1756,f2327])).

fof(f2327,plain,
    ( spl5_69
  <=> r2_hidden(sK3(sK2,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f1756,plain,
    ( spl5_51
  <=> r2_hidden(sK3(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f2289,plain,
    ( spl5_63
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f2318,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK0)
    | spl5_51
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f1758,f2290,f39])).

fof(f2290,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f1758,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | spl5_51 ),
    inference(avatar_component_clause,[],[f1756])).

fof(f2325,plain,
    ( spl5_68
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f2319,f2289,f2322])).

fof(f2322,plain,
    ( spl5_68
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f2319,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_63 ),
    inference(unit_resulting_resolution,[],[f2290,f35])).

fof(f2316,plain,
    ( ~ spl5_67
    | spl5_63 ),
    inference(avatar_split_clause,[],[f2305,f2289,f2313])).

fof(f2305,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),sK2)
    | spl5_63 ),
    inference(unit_resulting_resolution,[],[f2291,f41])).

fof(f2291,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl5_63 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f2311,plain,
    ( spl5_66
    | spl5_63 ),
    inference(avatar_split_clause,[],[f2306,f2289,f2308])).

fof(f2306,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | spl5_63 ),
    inference(unit_resulting_resolution,[],[f2291,f40])).

fof(f2304,plain,
    ( ~ spl5_65
    | spl5_62 ),
    inference(avatar_split_clause,[],[f2293,f2285,f2301])).

fof(f2293,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),sK0)
    | spl5_62 ),
    inference(unit_resulting_resolution,[],[f2287,f41])).

fof(f2287,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl5_62 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2299,plain,
    ( spl5_64
    | spl5_62 ),
    inference(avatar_split_clause,[],[f2294,f2285,f2296])).

fof(f2294,plain,
    ( r2_hidden(sK3(sK2,sK0),sK2)
    | spl5_62 ),
    inference(unit_resulting_resolution,[],[f2287,f40])).

fof(f2292,plain,
    ( ~ spl5_62
    | ~ spl5_63
    | spl5_58 ),
    inference(avatar_split_clause,[],[f2283,f2237,f2289,f2285])).

fof(f2237,plain,
    ( spl5_58
  <=> r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2283,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK2,sK0)
    | spl5_58 ),
    inference(forward_demodulation,[],[f2269,f1415])).

fof(f2269,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)),sK2)
    | ~ r1_tarski(sK2,sK0)
    | spl5_58 ),
    inference(superposition,[],[f2239,f35])).

fof(f2239,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2)
    | spl5_58 ),
    inference(avatar_component_clause,[],[f2237])).

fof(f2282,plain,
    ( ~ spl5_61
    | spl5_58 ),
    inference(avatar_split_clause,[],[f2267,f2237,f2279])).

fof(f2279,plain,
    ( spl5_61
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f2267,plain,
    ( ~ r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),sK2)
    | spl5_58 ),
    inference(unit_resulting_resolution,[],[f2239,f41])).

fof(f2277,plain,
    ( spl5_60
    | spl5_58 ),
    inference(avatar_split_clause,[],[f2268,f2237,f2274])).

fof(f2274,plain,
    ( spl5_60
  <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f2268,plain,
    ( r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))))
    | spl5_58 ),
    inference(unit_resulting_resolution,[],[f2239,f40])).

fof(f2247,plain,
    ( ~ spl5_59
    | spl5_50 ),
    inference(avatar_split_clause,[],[f2234,f1751,f2244])).

fof(f1751,plain,
    ( spl5_50
  <=> sK2 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f2234,plain,
    ( sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))
    | spl5_50 ),
    inference(superposition,[],[f1753,f61])).

fof(f1753,plain,
    ( sK2 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_50 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f2242,plain,
    ( ~ spl5_58
    | spl5_50 ),
    inference(avatar_split_clause,[],[f2241,f1751,f2237])).

fof(f2241,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2)
    | spl5_50 ),
    inference(forward_demodulation,[],[f2232,f61])).

fof(f2232,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2)
    | spl5_50 ),
    inference(unit_resulting_resolution,[],[f1206,f1753,f38])).

fof(f2240,plain,
    ( ~ spl5_58
    | spl5_50 ),
    inference(avatar_split_clause,[],[f2235,f1751,f2237])).

fof(f2235,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2)
    | spl5_50 ),
    inference(forward_demodulation,[],[f2233,f61])).

fof(f2233,plain,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2)
    | spl5_50 ),
    inference(unit_resulting_resolution,[],[f1206,f1753,f38])).

fof(f1877,plain,
    ( ~ spl5_57
    | spl5_26 ),
    inference(avatar_split_clause,[],[f1866,f1160,f1874])).

fof(f1874,plain,
    ( spl5_57
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f1160,plain,
    ( spl5_26
  <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1866,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f1162,f41])).

fof(f1162,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1872,plain,
    ( spl5_56
    | spl5_26 ),
    inference(avatar_split_clause,[],[f1867,f1160,f1869])).

fof(f1869,plain,
    ( spl5_56
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1867,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1)
    | spl5_26 ),
    inference(unit_resulting_resolution,[],[f1162,f40])).

fof(f1818,plain,
    ( ~ spl5_55
    | spl5_23 ),
    inference(avatar_split_clause,[],[f1807,f1136,f1815])).

fof(f1815,plain,
    ( spl5_55
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1136,plain,
    ( spl5_23
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1807,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f1138,f41])).

fof(f1138,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1813,plain,
    ( spl5_54
    | spl5_23 ),
    inference(avatar_split_clause,[],[f1808,f1136,f1810])).

fof(f1810,plain,
    ( spl5_54
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1808,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f1138,f40])).

fof(f1800,plain,
    ( ~ spl5_53
    | ~ spl5_12
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1789,f1201,f1054,f1797])).

fof(f1797,plain,
    ( spl5_53
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f1201,plain,
    ( spl5_31
  <=> r2_hidden(sK3(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f1789,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK0))
    | ~ spl5_12
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1203,f1056,f39])).

fof(f1203,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f1201])).

fof(f1770,plain,
    ( spl5_37
    | ~ spl5_40
    | ~ spl5_49 ),
    inference(avatar_contradiction_clause,[],[f1769])).

fof(f1769,plain,
    ( $false
    | spl5_37
    | ~ spl5_40
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f1749,f1735])).

fof(f1735,plain,
    ( ! [X0] : ~ r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),X0),sK2)
    | spl5_37
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f1398,f1294])).

fof(f1294,plain,
    ( sK2 = k3_tarski(sK1)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1292,plain,
    ( spl5_40
  <=> sK2 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f1398,plain,
    ( ! [X0] : ~ r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),X0),sK2)
    | spl5_37 ),
    inference(unit_resulting_resolution,[],[f519,f1275,f39])).

fof(f1275,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1274,plain,
    ( spl5_37
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f519,plain,(
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

fof(f1749,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)
    | ~ spl5_40
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f1712,f1294])).

fof(f1712,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1710,plain,
    ( spl5_49
  <=> r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1767,plain,
    ( spl5_52
    | ~ spl5_40
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f1730,f1377,f1292,f1764])).

fof(f1764,plain,
    ( spl5_52
  <=> r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1377,plain,
    ( spl5_45
  <=> r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1730,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)
    | ~ spl5_40
    | ~ spl5_45 ),
    inference(backward_demodulation,[],[f1379,f1294])).

fof(f1379,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1762,plain,
    ( ~ spl5_51
    | ~ spl5_40
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1728,f1310,f1292,f1756])).

fof(f1310,plain,
    ( spl5_43
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1728,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_40
    | spl5_43 ),
    inference(backward_demodulation,[],[f1312,f1294])).

fof(f1312,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)
    | spl5_43 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1761,plain,
    ( ~ spl5_51
    | ~ spl5_40
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1727,f1305,f1292,f1756])).

fof(f1305,plain,
    ( spl5_42
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1727,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | ~ spl5_40
    | spl5_42 ),
    inference(backward_demodulation,[],[f1306,f1294])).

fof(f1306,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1760,plain,
    ( ~ spl5_51
    | spl5_38
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1724,f1292,f1279,f1756])).

fof(f1279,plain,
    ( spl5_38
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1724,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | spl5_38
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f1281,f1294])).

fof(f1281,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | spl5_38 ),
    inference(avatar_component_clause,[],[f1279])).

fof(f1759,plain,
    ( ~ spl5_51
    | spl5_37
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1723,f1292,f1274,f1756])).

fof(f1723,plain,
    ( ~ r2_hidden(sK3(sK2,sK2),sK2)
    | spl5_37
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f1275,f1294])).

fof(f1754,plain,
    ( ~ spl5_50
    | spl5_36
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f1722,f1292,f1266,f1751])).

fof(f1266,plain,
    ( spl5_36
  <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f1722,plain,
    ( sK2 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_36
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f1267,f1294])).

fof(f1267,plain,
    ( k3_tarski(sK1) != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | spl5_36 ),
    inference(avatar_component_clause,[],[f1266])).

fof(f1720,plain,
    ( spl5_40
    | ~ spl5_35
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1719,f1296,f1261,f1292])).

fof(f1261,plain,
    ( spl5_35
  <=> r1_tarski(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f1296,plain,
    ( spl5_41
  <=> r1_tarski(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1719,plain,
    ( sK2 = k3_tarski(sK1)
    | ~ spl5_35
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1318,f1263])).

fof(f1263,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1318,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK1))
    | sK2 = k3_tarski(sK1)
    | ~ spl5_41 ),
    inference(resolution,[],[f1297,f38])).

fof(f1297,plain,
    ( r1_tarski(k3_tarski(sK1),sK2)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f1717,plain,
    ( spl5_40
    | ~ spl5_41
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1386,f1261,f1296,f1292])).

fof(f1386,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_35 ),
    inference(resolution,[],[f1263,f38])).

fof(f1716,plain,
    ( spl5_40
    | ~ spl5_41
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1285,f1261,f1296,f1292])).

fof(f1285,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_35 ),
    inference(resolution,[],[f1263,f38])).

fof(f1715,plain,
    ( spl5_40
    | ~ spl5_41
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1639,f1261,f1296,f1292])).

fof(f1639,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | sK2 = k3_tarski(sK1)
    | ~ spl5_35 ),
    inference(resolution,[],[f1263,f38])).

fof(f1714,plain,
    ( spl5_49
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1691,f1305,f1710])).

fof(f1691,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f1307,f1307,f69])).

fof(f1307,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1713,plain,
    ( spl5_49
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1692,f1305,f1710])).

fof(f1692,plain,
    ( r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f1307,f1307,f69])).

fof(f1708,plain,
    ( spl5_48
    | ~ spl5_42
    | spl5_43 ),
    inference(avatar_split_clause,[],[f1695,f1310,f1305,f1705])).

fof(f1705,plain,
    ( spl5_48
  <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1695,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2)))
    | ~ spl5_42
    | spl5_43 ),
    inference(unit_resulting_resolution,[],[f1312,f1307,f74])).

fof(f1633,plain,
    ( spl5_35
    | spl5_37 ),
    inference(avatar_split_clause,[],[f1387,f1274,f1261])).

fof(f1387,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | spl5_37 ),
    inference(unit_resulting_resolution,[],[f1275,f40])).

fof(f1632,plain,
    ( spl5_35
    | spl5_37 ),
    inference(avatar_split_clause,[],[f1399,f1274,f1261])).

fof(f1399,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | spl5_37 ),
    inference(resolution,[],[f1275,f40])).

fof(f1630,plain,
    ( spl5_47
    | ~ spl5_37
    | spl5_38 ),
    inference(avatar_split_clause,[],[f1616,f1279,f1274,f1627])).

fof(f1627,plain,
    ( spl5_47
  <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1616,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1))))
    | ~ spl5_37
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f1276,f1281,f74])).

fof(f1276,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1587,plain,
    ( spl5_46
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f1582,f1287,f1584])).

fof(f1584,plain,
    ( spl5_46
  <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f1287,plain,
    ( spl5_39
  <=> sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f1582,plain,
    ( k3_tarski(sK1) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2))
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f1571,f1489])).

fof(f1571,plain,
    ( k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k5_xboole_0(sK2,sK2)))
    | ~ spl5_39 ),
    inference(superposition,[],[f62,f1289])).

fof(f1289,plain,
    ( sK2 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f1287])).

fof(f1381,plain,
    ( spl5_45
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f1363,f1274,f1377])).

fof(f1363,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f1276,f1276,f69])).

fof(f1380,plain,
    ( spl5_45
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f1364,f1274,f1377])).

fof(f1364,plain,
    ( r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)
    | ~ spl5_37 ),
    inference(unit_resulting_resolution,[],[f1276,f1276,f69])).

fof(f1323,plain,
    ( spl5_44
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1317,f1296,f1320])).

fof(f1320,plain,
    ( spl5_44
  <=> k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1317,plain,
    ( k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl5_41 ),
    inference(unit_resulting_resolution,[],[f1297,f35])).

fof(f1313,plain,
    ( ~ spl5_43
    | spl5_41 ),
    inference(avatar_split_clause,[],[f1302,f1296,f1310])).

fof(f1302,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)
    | spl5_41 ),
    inference(unit_resulting_resolution,[],[f1298,f41])).

fof(f1298,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK2)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f1308,plain,
    ( spl5_42
    | spl5_41 ),
    inference(avatar_split_clause,[],[f1303,f1296,f1305])).

fof(f1303,plain,
    ( r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))
    | spl5_41 ),
    inference(unit_resulting_resolution,[],[f1298,f40])).

fof(f1299,plain,
    ( spl5_40
    | ~ spl5_41
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1285,f1261,f1296,f1292])).

fof(f1290,plain,
    ( spl5_39
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f1284,f1261,f1287])).

fof(f1284,plain,
    ( sK2 = k3_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl5_35 ),
    inference(unit_resulting_resolution,[],[f1263,f35])).

fof(f1282,plain,
    ( ~ spl5_38
    | spl5_35 ),
    inference(avatar_split_clause,[],[f1271,f1261,f1279])).

fof(f1271,plain,
    ( ~ r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f1262,f41])).

fof(f1262,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK1))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1277,plain,
    ( spl5_37
    | spl5_35 ),
    inference(avatar_split_clause,[],[f1272,f1261,f1274])).

fof(f1272,plain,
    ( r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f1262,f40])).

fof(f1270,plain,
    ( spl5_36
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f1253,f1108,f1266])).

fof(f1108,plain,
    ( spl5_19
  <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1253,plain,
    ( k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_19 ),
    inference(superposition,[],[f60,f1110])).

fof(f1110,plain,
    ( sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1269,plain,
    ( spl5_36
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f1252,f1108,f1266])).

fof(f1252,plain,
    ( k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_19 ),
    inference(superposition,[],[f60,f1110])).

fof(f1264,plain,
    ( spl5_35
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f1251,f1108,f1261])).

fof(f1251,plain,
    ( r1_tarski(sK2,k3_tarski(sK1))
    | ~ spl5_19 ),
    inference(superposition,[],[f59,f1110])).

fof(f1250,plain,
    ( ~ spl5_34
    | ~ spl5_11
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1230,f1201,f1049,f1247])).

fof(f1247,plain,
    ( spl5_34
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f1230,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_11
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1051,f1203,f39])).

fof(f1245,plain,
    ( ~ spl5_33
    | ~ spl5_13
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1231,f1201,f1059,f1242])).

fof(f1242,plain,
    ( spl5_33
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f1231,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | ~ spl5_13
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1061,f1203,f39])).

fof(f1240,plain,
    ( ~ spl5_32
    | ~ spl5_14
    | spl5_31 ),
    inference(avatar_split_clause,[],[f1232,f1201,f1064,f1237])).

fof(f1237,plain,
    ( spl5_32
  <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f1232,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_14
    | spl5_31 ),
    inference(unit_resulting_resolution,[],[f1066,f1203,f39])).

fof(f1205,plain,
    ( ~ spl5_31
    | ~ spl5_19
    | spl5_30 ),
    inference(avatar_split_clause,[],[f1199,f1188,f1108,f1201])).

fof(f1188,plain,
    ( spl5_30
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1199,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_19
    | spl5_30 ),
    inference(backward_demodulation,[],[f1190,f1110])).

fof(f1190,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f1204,plain,
    ( ~ spl5_31
    | ~ spl5_19
    | spl5_29 ),
    inference(avatar_split_clause,[],[f1198,f1183,f1108,f1201])).

fof(f1183,plain,
    ( spl5_29
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f1198,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl5_19
    | spl5_29 ),
    inference(backward_demodulation,[],[f1184,f1110])).

fof(f1184,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f1183])).

fof(f1191,plain,
    ( ~ spl5_30
    | spl5_20 ),
    inference(avatar_split_clause,[],[f1180,f1112,f1188])).

fof(f1112,plain,
    ( spl5_20
  <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1180,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0))
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f1114,f41])).

fof(f1114,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1186,plain,
    ( spl5_29
    | spl5_20 ),
    inference(avatar_split_clause,[],[f1181,f1112,f1183])).

fof(f1181,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1)
    | spl5_20 ),
    inference(unit_resulting_resolution,[],[f1114,f40])).

fof(f1177,plain,
    ( ~ spl5_28
    | spl5_17 ),
    inference(avatar_split_clause,[],[f1166,f1088,f1174])).

fof(f1174,plain,
    ( spl5_28
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f1088,plain,
    ( spl5_17
  <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1166,plain,
    ( ~ r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f1090,f41])).

fof(f1090,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f1172,plain,
    ( spl5_27
    | spl5_17 ),
    inference(avatar_split_clause,[],[f1167,f1088,f1169])).

fof(f1169,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f1167,plain,
    ( r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f1090,f40])).

fof(f1163,plain,
    ( spl5_25
    | ~ spl5_26
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1149,f1064,f1160,f1156])).

fof(f1156,plain,
    ( spl5_25
  <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f1149,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f1066,f38])).

fof(f1154,plain,
    ( spl5_24
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f1146,f1064,f1151])).

fof(f1151,plain,
    ( spl5_24
  <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f1146,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f1066,f35])).

fof(f1139,plain,
    ( spl5_22
    | ~ spl5_23
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1125,f1059,f1136,f1132])).

fof(f1132,plain,
    ( spl5_22
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1125,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f1061,f38])).

fof(f1130,plain,
    ( spl5_21
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f1122,f1059,f1127])).

fof(f1127,plain,
    ( spl5_21
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1122,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f1061,f35])).

fof(f1115,plain,
    ( spl5_19
    | ~ spl5_20
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1101,f1054,f1112,f1108])).

fof(f1101,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0))
    | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f1056,f38])).

fof(f1106,plain,
    ( spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f1098,f1054,f1103])).

fof(f1103,plain,
    ( spl5_18
  <=> k3_enumset1(sK2,sK2,sK2,sK2,sK0) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1098,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK0) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f1056,f35])).

fof(f1091,plain,
    ( spl5_16
    | ~ spl5_17
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1077,f1049,f1088,f1084])).

fof(f1084,plain,
    ( spl5_16
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1077,plain,
    ( ~ r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f1051,f38])).

fof(f1082,plain,
    ( spl5_15
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1074,f1049,f1079])).

fof(f1079,plain,
    ( spl5_15
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1074,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f1051,f35])).

fof(f1067,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f994,f83,f1064])).

fof(f994,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f85,f85,f69])).

fof(f1062,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f995,f88,f83,f1059])).

fof(f995,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f90,f85,f69])).

fof(f1057,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1001,f88,f83,f1054])).

fof(f1001,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f85,f90,f69])).

fof(f1052,plain,
    ( spl5_11
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f1002,f88,f1049])).

fof(f1002,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f90,f90,f69])).

fof(f756,plain,
    ( spl5_10
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f720,f137,f83,f753])).

fof(f753,plain,
    ( spl5_10
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f137,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f720,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f139,f74])).

fof(f139,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f751,plain,
    ( spl5_9
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f724,f159,f154,f747])).

fof(f747,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f159,plain,
    ( spl5_7
  <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f724,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_6
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f156,f161,f74])).

fof(f161,plain,
    ( ~ r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f750,plain,
    ( spl5_9
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f725,f159,f83,f747])).

fof(f725,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | ~ spl5_2
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f200,f161,f74])).

fof(f198,plain,
    ( ~ spl5_8
    | spl5_4 ),
    inference(avatar_split_clause,[],[f192,f137,f195])).

fof(f195,plain,
    ( spl5_8
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f192,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))
    | spl5_4 ),
    inference(backward_demodulation,[],[f168,f190])).

fof(f168,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))
    | spl5_4 ),
    inference(forward_demodulation,[],[f164,f43])).

fof(f164,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f139,f76])).

fof(f162,plain,
    ( ~ spl5_7
    | spl5_5 ),
    inference(avatar_split_clause,[],[f151,f146,f159])).

fof(f146,plain,
    ( spl5_5
  <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f151,plain,
    ( ~ r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f148,f41])).

fof(f148,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f157,plain,
    ( spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f152,f146,f154])).

fof(f152,plain,
    ( r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f148,f40])).

fof(f150,plain,
    ( ~ spl5_5
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f141,f137,f83,f146])).

fof(f141,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f139,f99])).

fof(f149,plain,
    ( ~ spl5_5
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f142,f137,f83,f146])).

fof(f142,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,sK1))
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f85,f139,f39])).

fof(f140,plain,
    ( ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f135,f83,f137])).

fof(f135,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f123,f92])).

fof(f123,plain,
    ( ! [X0] : ~ r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f85,f75])).

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
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11138)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (11130)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (11122)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (11121)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (11119)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (11116)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (11117)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (11118)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (11137)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (11135)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (11136)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (11132)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (11120)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (11145)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (11123)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (11143)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (11141)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (11142)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (11140)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.55  % (11126)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (11125)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.55  % (11133)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (11127)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.55  % (11124)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (11134)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.55  % (11136)Refutation not found, incomplete strategy% (11136)------------------------------
% 1.35/0.55  % (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (11136)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (11136)Memory used [KB]: 10746
% 1.35/0.55  % (11136)Time elapsed: 0.138 s
% 1.35/0.55  % (11136)------------------------------
% 1.35/0.55  % (11136)------------------------------
% 1.35/0.55  % (11144)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.56  % (11128)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.56  % (11129)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.56  % (11131)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.60/0.58  % (11139)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.44/0.68  % (11146)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.44/0.85  % (11121)Time limit reached!
% 3.44/0.85  % (11121)------------------------------
% 3.44/0.85  % (11121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.85  % (11121)Termination reason: Time limit
% 3.44/0.85  
% 3.44/0.85  % (11121)Memory used [KB]: 10746
% 3.44/0.85  % (11121)Time elapsed: 0.436 s
% 3.44/0.85  % (11121)------------------------------
% 3.44/0.85  % (11121)------------------------------
% 3.86/0.91  % (11126)Time limit reached!
% 3.86/0.91  % (11126)------------------------------
% 3.86/0.91  % (11126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (11126)Termination reason: Time limit
% 3.86/0.92  
% 3.86/0.92  % (11126)Memory used [KB]: 14456
% 3.86/0.92  % (11126)Time elapsed: 0.509 s
% 3.86/0.92  % (11126)------------------------------
% 3.86/0.92  % (11126)------------------------------
% 3.86/0.92  % (11128)Time limit reached!
% 3.86/0.92  % (11128)------------------------------
% 3.86/0.92  % (11128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (11128)Termination reason: Time limit
% 3.86/0.92  
% 3.86/0.92  % (11128)Memory used [KB]: 8699
% 3.86/0.92  % (11128)Time elapsed: 0.510 s
% 3.86/0.92  % (11128)------------------------------
% 3.86/0.92  % (11128)------------------------------
% 3.86/0.92  % (11130)Refutation found. Thanks to Tanya!
% 3.86/0.92  % SZS status Theorem for theBenchmark
% 3.86/0.93  % (11116)Time limit reached!
% 3.86/0.93  % (11116)------------------------------
% 3.86/0.93  % (11116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.93  % (11116)Termination reason: Time limit
% 3.86/0.93  
% 3.86/0.93  % (11116)Memory used [KB]: 3454
% 3.86/0.93  % (11116)Time elapsed: 0.513 s
% 3.86/0.93  % (11116)------------------------------
% 3.86/0.93  % (11116)------------------------------
% 3.86/0.93  % (11117)Time limit reached!
% 3.86/0.93  % (11117)------------------------------
% 3.86/0.93  % (11117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.93  % (11117)Termination reason: Time limit
% 3.86/0.93  % (11117)Termination phase: Saturation
% 3.86/0.93  
% 3.86/0.93  % (11117)Memory used [KB]: 8827
% 3.86/0.93  % (11117)Time elapsed: 0.500 s
% 3.86/0.93  % (11117)------------------------------
% 3.86/0.93  % (11117)------------------------------
% 3.86/0.94  % (11133)Time limit reached!
% 3.86/0.94  % (11133)------------------------------
% 3.86/0.94  % (11133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.95  % SZS output start Proof for theBenchmark
% 3.86/0.95  fof(f3326,plain,(
% 3.86/0.95    $false),
% 3.86/0.95    inference(avatar_sat_refutation,[],[f81,f86,f91,f140,f149,f150,f157,f162,f198,f750,f751,f756,f1052,f1057,f1062,f1067,f1082,f1091,f1106,f1115,f1130,f1139,f1154,f1163,f1172,f1177,f1186,f1191,f1204,f1205,f1240,f1245,f1250,f1264,f1269,f1270,f1277,f1282,f1290,f1299,f1308,f1313,f1323,f1380,f1381,f1587,f1630,f1632,f1633,f1708,f1713,f1714,f1715,f1716,f1717,f1720,f1754,f1759,f1760,f1761,f1762,f1767,f1770,f1800,f1813,f1818,f1872,f1877,f2240,f2242,f2247,f2277,f2282,f2292,f2299,f2304,f2311,f2316,f2325,f2330,f2343,f2345,f2350,f2355,f2356,f2376,f2377,f2385,f2419,f2439,f2440,f2457,f2950,f2956,f2965,f2966,f2974,f2978,f2995,f3008,f3156,f3176,f3180,f3195,f3200,f3202,f3240,f3245,f3250,f3251,f3256,f3261,f3281,f3313,f3315,f3320,f3325])).
% 3.86/0.95  fof(f3325,plain,(
% 3.86/0.95    spl5_97 | ~spl5_11),
% 3.86/0.95    inference(avatar_split_clause,[],[f3289,f1049,f3322])).
% 3.86/0.95  fof(f3322,plain,(
% 3.86/0.95    spl5_97 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 3.86/0.95  fof(f1049,plain,(
% 3.86/0.95    spl5_11 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.86/0.95  fof(f3289,plain,(
% 3.86/0.95    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~spl5_11),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f1051,f1488])).
% 3.86/0.95  fof(f1488,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.86/0.95    inference(backward_demodulation,[],[f1327,f1415])).
% 3.86/0.95  fof(f1415,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0) )),
% 3.86/0.95    inference(superposition,[],[f1347,f189])).
% 3.86/0.95  fof(f189,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1)) )),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f180,f180,f38])).
% 3.86/0.95  fof(f38,plain,(
% 3.86/0.95    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.86/0.95    inference(cnf_transformation,[],[f5])).
% 3.86/0.95  fof(f5,axiom,(
% 3.86/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.86/0.95  fof(f180,plain,(
% 3.86/0.95    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f171,f40])).
% 3.86/0.95  fof(f40,plain,(
% 3.86/0.95    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f23])).
% 3.86/0.95  fof(f23,plain,(
% 3.86/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.86/0.95    inference(ennf_transformation,[],[f2])).
% 3.86/0.95  fof(f2,axiom,(
% 3.86/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.86/0.95  fof(f171,plain,(
% 3.86/0.95    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3))) )),
% 3.86/0.95    inference(subsumption_resolution,[],[f167,f129])).
% 3.86/0.95  fof(f129,plain,(
% 3.86/0.95    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | ~r2_hidden(X4,X3)) )),
% 3.86/0.95    inference(superposition,[],[f75,f92])).
% 3.86/0.95  fof(f92,plain,(
% 3.86/0.95    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f72,f35])).
% 3.86/0.95  fof(f35,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f22])).
% 3.86/0.95  fof(f22,plain,(
% 3.86/0.95    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.86/0.95    inference(ennf_transformation,[],[f7])).
% 3.86/0.95  fof(f7,axiom,(
% 3.86/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.86/0.95  fof(f72,plain,(
% 3.86/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.95    inference(equality_resolution,[],[f37])).
% 3.86/0.95  fof(f37,plain,(
% 3.86/0.95    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.86/0.95    inference(cnf_transformation,[],[f5])).
% 3.86/0.95  fof(f75,plain,(
% 3.86/0.95    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 3.86/0.95    inference(equality_resolution,[],[f64])).
% 3.86/0.95  fof(f64,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.86/0.95    inference(definition_unfolding,[],[f48,f32])).
% 3.86/0.95  fof(f32,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.86/0.95    inference(cnf_transformation,[],[f6])).
% 3.86/0.95  fof(f6,axiom,(
% 3.86/0.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.86/0.95  fof(f48,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.86/0.95    inference(cnf_transformation,[],[f3])).
% 3.86/0.95  fof(f3,axiom,(
% 3.86/0.95    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.86/0.95  fof(f167,plain,(
% 3.86/0.95    ( ! [X4,X3] : (~r2_hidden(X4,k5_xboole_0(X3,X3)) | r2_hidden(X4,X3)) )),
% 3.86/0.95    inference(superposition,[],[f76,f92])).
% 3.86/0.95  fof(f76,plain,(
% 3.86/0.95    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 3.86/0.95    inference(equality_resolution,[],[f65])).
% 3.86/0.95  fof(f65,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.86/0.95    inference(definition_unfolding,[],[f47,f32])).
% 3.86/0.95  fof(f47,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.86/0.95    inference(cnf_transformation,[],[f3])).
% 3.86/0.95  fof(f1347,plain,(
% 3.86/0.95    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 3.86/0.95    inference(forward_demodulation,[],[f1324,f92])).
% 3.86/0.95  fof(f1324,plain,(
% 3.86/0.95    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 3.86/0.95    inference(superposition,[],[f61,f58])).
% 3.86/0.95  fof(f58,plain,(
% 3.86/0.95    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 3.86/0.95    inference(definition_unfolding,[],[f27,f56])).
% 3.86/0.95  fof(f56,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.86/0.95    inference(definition_unfolding,[],[f30,f55])).
% 3.86/0.95  fof(f55,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.86/0.95    inference(definition_unfolding,[],[f31,f54])).
% 3.86/0.95  fof(f54,plain,(
% 3.86/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.86/0.95    inference(definition_unfolding,[],[f42,f53])).
% 3.86/0.95  fof(f53,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f14])).
% 3.86/0.95  fof(f14,axiom,(
% 3.86/0.95    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.86/0.95  fof(f42,plain,(
% 3.86/0.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f13])).
% 3.86/0.95  fof(f13,axiom,(
% 3.86/0.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.86/0.95  fof(f31,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f12])).
% 3.86/0.95  fof(f12,axiom,(
% 3.86/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.86/0.95  fof(f30,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.86/0.95    inference(cnf_transformation,[],[f15])).
% 3.86/0.95  fof(f15,axiom,(
% 3.86/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.86/0.95  fof(f27,plain,(
% 3.86/0.95    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.86/0.95    inference(cnf_transformation,[],[f19])).
% 3.86/0.95  fof(f19,plain,(
% 3.86/0.95    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.86/0.95    inference(rectify,[],[f4])).
% 3.86/0.95  fof(f4,axiom,(
% 3.86/0.95    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.86/0.95  fof(f61,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.86/0.95    inference(definition_unfolding,[],[f33,f56,f32])).
% 3.86/0.95  fof(f33,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.86/0.95    inference(cnf_transformation,[],[f11])).
% 3.86/0.95  fof(f11,axiom,(
% 3.86/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.86/0.95  fof(f1327,plain,(
% 3.86/0.95    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,X0)) | ~r1_tarski(X0,X1)) )),
% 3.86/0.95    inference(superposition,[],[f61,f35])).
% 3.86/0.95  % (11133)Termination reason: Time limit
% 3.86/0.95  
% 3.86/0.95  % (11133)Memory used [KB]: 14711
% 3.86/0.95  % (11133)Time elapsed: 0.531 s
% 3.86/0.95  % (11133)------------------------------
% 3.86/0.95  % (11133)------------------------------
% 3.86/0.95  fof(f1051,plain,(
% 3.86/0.95    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_11),
% 3.86/0.95    inference(avatar_component_clause,[],[f1049])).
% 3.86/0.95  fof(f3320,plain,(
% 3.86/0.95    spl5_96 | ~spl5_12),
% 3.86/0.95    inference(avatar_split_clause,[],[f3290,f1054,f3317])).
% 3.86/0.95  fof(f3317,plain,(
% 3.86/0.95    spl5_96 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)))),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 3.86/0.95  fof(f1054,plain,(
% 3.86/0.95    spl5_12 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.86/0.95  fof(f3290,plain,(
% 3.86/0.95    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0))) | ~spl5_12),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f1056,f1488])).
% 3.86/0.95  fof(f1056,plain,(
% 3.86/0.95    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) | ~spl5_12),
% 3.86/0.95    inference(avatar_component_clause,[],[f1054])).
% 3.86/0.95  fof(f3315,plain,(
% 3.86/0.95    ~spl5_13 | spl5_72),
% 3.86/0.95    inference(avatar_contradiction_clause,[],[f3314])).
% 3.86/0.95  fof(f3314,plain,(
% 3.86/0.95    $false | (~spl5_13 | spl5_72)),
% 3.86/0.95    inference(subsumption_resolution,[],[f3291,f2354])).
% 3.86/0.95  fof(f2354,plain,(
% 3.86/0.95    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl5_72),
% 3.86/0.95    inference(avatar_component_clause,[],[f2352])).
% 3.86/0.95  fof(f2352,plain,(
% 3.86/0.95    spl5_72 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 3.86/0.95  fof(f3291,plain,(
% 3.86/0.95    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | ~spl5_13),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f1061,f1488])).
% 3.86/0.95  fof(f1061,plain,(
% 3.86/0.95    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_13),
% 3.86/0.95    inference(avatar_component_clause,[],[f1059])).
% 3.86/0.95  fof(f1059,plain,(
% 3.86/0.95    spl5_13 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.86/0.95  fof(f3313,plain,(
% 3.86/0.95    spl5_95 | ~spl5_14),
% 3.86/0.95    inference(avatar_split_clause,[],[f3292,f1064,f3310])).
% 3.86/0.95  fof(f3310,plain,(
% 3.86/0.95    spl5_95 <=> sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 3.86/0.95  fof(f1064,plain,(
% 3.86/0.95    spl5_14 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.86/0.95  fof(f3292,plain,(
% 3.86/0.95    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~spl5_14),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f1066,f1488])).
% 3.86/0.95  fof(f1066,plain,(
% 3.86/0.95    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_14),
% 3.86/0.95    inference(avatar_component_clause,[],[f1064])).
% 3.86/0.95  fof(f3281,plain,(
% 3.86/0.95    spl5_94 | ~spl5_87 | spl5_88),
% 3.86/0.95    inference(avatar_split_clause,[],[f3266,f3197,f3192,f3278])).
% 3.86/0.95  fof(f3278,plain,(
% 3.86/0.95    spl5_94 <=> r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 3.86/0.95  fof(f3192,plain,(
% 3.86/0.95    spl5_87 <=> r2_hidden(sK3(sK1,sK2),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 3.86/0.95  fof(f3197,plain,(
% 3.86/0.95    spl5_88 <=> r2_hidden(sK3(sK1,sK2),sK2)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 3.86/0.95  fof(f3266,plain,(
% 3.86/0.95    r2_hidden(sK3(sK1,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl5_87 | spl5_88)),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f3194,f3199,f74])).
% 3.86/0.95  fof(f74,plain,(
% 3.86/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 3.86/0.95    inference(equality_resolution,[],[f63])).
% 3.86/0.95  fof(f63,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.86/0.95    inference(definition_unfolding,[],[f49,f32])).
% 3.86/0.95  fof(f49,plain,(
% 3.86/0.95    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.86/0.95    inference(cnf_transformation,[],[f3])).
% 3.86/0.95  fof(f3199,plain,(
% 3.86/0.95    ~r2_hidden(sK3(sK1,sK2),sK2) | spl5_88),
% 3.86/0.95    inference(avatar_component_clause,[],[f3197])).
% 3.86/0.95  fof(f3194,plain,(
% 3.86/0.95    r2_hidden(sK3(sK1,sK2),sK1) | ~spl5_87),
% 3.86/0.95    inference(avatar_component_clause,[],[f3192])).
% 3.86/0.95  fof(f3261,plain,(
% 3.86/0.95    spl5_93 | ~spl5_2 | ~spl5_87),
% 3.86/0.95    inference(avatar_split_clause,[],[f3210,f3192,f83,f3258])).
% 3.86/0.95  fof(f3258,plain,(
% 3.86/0.95    spl5_93 <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 3.86/0.95  fof(f83,plain,(
% 3.86/0.95    spl5_2 <=> r2_hidden(sK2,sK1)),
% 3.86/0.95    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.86/0.95  fof(f3210,plain,(
% 3.86/0.95    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK2),sK1) | (~spl5_2 | ~spl5_87)),
% 3.86/0.95    inference(unit_resulting_resolution,[],[f85,f3194,f69])).
% 3.86/0.95  fof(f69,plain,(
% 3.86/0.95    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.86/0.95    inference(definition_unfolding,[],[f52,f55])).
% 3.86/0.95  fof(f52,plain,(
% 3.86/0.95    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.86/0.95    inference(cnf_transformation,[],[f16])).
% 3.86/0.95  fof(f16,axiom,(
% 3.86/0.95    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.86/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.86/0.95  fof(f85,plain,(
% 3.86/0.95    r2_hidden(sK2,sK1) | ~spl5_2),
% 3.86/0.95    inference(avatar_component_clause,[],[f83])).
% 4.49/0.95  fof(f3256,plain,(
% 4.49/0.95    spl5_92 | ~spl5_3 | ~spl5_87),
% 4.49/0.95    inference(avatar_split_clause,[],[f3211,f3192,f88,f3253])).
% 4.49/0.96  fof(f3253,plain,(
% 4.49/0.96    spl5_92 <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 4.49/0.96  fof(f88,plain,(
% 4.49/0.96    spl5_3 <=> r2_hidden(sK0,sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 4.49/0.96  fof(f3211,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK0),sK1) | (~spl5_3 | ~spl5_87)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f90,f3194,f69])).
% 4.49/0.96  fof(f90,plain,(
% 4.49/0.96    r2_hidden(sK0,sK1) | ~spl5_3),
% 4.49/0.96    inference(avatar_component_clause,[],[f88])).
% 4.49/0.96  fof(f3251,plain,(
% 4.49/0.96    spl5_89 | ~spl5_87),
% 4.49/0.96    inference(avatar_split_clause,[],[f3216,f3192,f3237])).
% 4.49/0.96  fof(f3237,plain,(
% 4.49/0.96    spl5_89 <=> r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).
% 4.49/0.96  fof(f3216,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) | ~spl5_87),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f3194,f3194,f69])).
% 4.49/0.96  fof(f3250,plain,(
% 4.49/0.96    spl5_91 | ~spl5_2 | ~spl5_87),
% 4.49/0.96    inference(avatar_split_clause,[],[f3217,f3192,f83,f3247])).
% 4.49/0.96  fof(f3247,plain,(
% 4.49/0.96    spl5_91 <=> r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 4.49/0.96  fof(f3217,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3(sK1,sK2)),sK1) | (~spl5_2 | ~spl5_87)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f3194,f69])).
% 4.49/0.96  fof(f3245,plain,(
% 4.49/0.96    spl5_90 | ~spl5_3 | ~spl5_87),
% 4.49/0.96    inference(avatar_split_clause,[],[f3218,f3192,f88,f3242])).
% 4.49/0.96  fof(f3242,plain,(
% 4.49/0.96    spl5_90 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 4.49/0.96  fof(f3218,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK3(sK1,sK2)),sK1) | (~spl5_3 | ~spl5_87)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f90,f3194,f69])).
% 4.49/0.96  fof(f3240,plain,(
% 4.49/0.96    spl5_89 | ~spl5_87),
% 4.49/0.96    inference(avatar_split_clause,[],[f3223,f3192,f3237])).
% 4.49/0.96  fof(f3223,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2),sK3(sK1,sK2)),sK1) | ~spl5_87),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f3194,f3194,f69])).
% 4.49/0.96  fof(f3202,plain,(
% 4.49/0.96    spl5_87 | spl5_84),
% 4.49/0.96    inference(avatar_split_clause,[],[f3182,f3169,f3192])).
% 4.49/0.96  fof(f3169,plain,(
% 4.49/0.96    spl5_84 <=> r1_tarski(sK1,sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 4.49/0.96  fof(f3182,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,sK2),sK1) | spl5_84),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f72,f3171,f101])).
% 4.49/0.96  fof(f101,plain,(
% 4.49/0.96    ( ! [X4,X2,X3] : (r2_hidden(sK3(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 4.49/0.96    inference(resolution,[],[f39,f40])).
% 4.49/0.96  fof(f39,plain,(
% 4.49/0.96    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.49/0.96    inference(cnf_transformation,[],[f23])).
% 4.49/0.96  fof(f3171,plain,(
% 4.49/0.96    ~r1_tarski(sK1,sK2) | spl5_84),
% 4.49/0.96    inference(avatar_component_clause,[],[f3169])).
% 4.49/0.96  fof(f3200,plain,(
% 4.49/0.96    ~spl5_88 | spl5_84),
% 4.49/0.96    inference(avatar_split_clause,[],[f3189,f3169,f3197])).
% 4.49/0.96  fof(f3189,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK2),sK2) | spl5_84),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f3171,f41])).
% 4.49/0.96  fof(f41,plain,(
% 4.49/0.96    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 4.49/0.96    inference(cnf_transformation,[],[f23])).
% 4.49/0.96  fof(f3195,plain,(
% 4.49/0.96    spl5_87 | spl5_84),
% 4.49/0.96    inference(avatar_split_clause,[],[f3190,f3169,f3192])).
% 4.49/0.96  fof(f3190,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,sK2),sK1) | spl5_84),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f3171,f40])).
% 4.49/0.96  fof(f3180,plain,(
% 4.49/0.96    ~spl5_84 | spl5_86 | ~spl5_2 | ~spl5_74),
% 4.49/0.96    inference(avatar_split_clause,[],[f3166,f2382,f83,f3178,f3169])).
% 4.49/0.96  fof(f3178,plain,(
% 4.49/0.96    spl5_86 <=> ! [X1] : r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 4.49/0.96  fof(f2382,plain,(
% 4.49/0.96    spl5_74 <=> sK2 = k3_xboole_0(sK2,sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 4.49/0.96  fof(f3166,plain,(
% 4.49/0.96    ( ! [X1] : (r2_hidden(sK3(sK1,k5_xboole_0(X1,X1)),sK0) | ~r1_tarski(sK1,sK2)) ) | (~spl5_2 | ~spl5_74)),
% 4.49/0.96    inference(resolution,[],[f3157,f239])).
% 4.49/0.96  fof(f239,plain,(
% 4.49/0.96    ( ! [X0,X1] : (r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),X1) | ~r1_tarski(sK1,X1)) ) | ~spl5_2),
% 4.49/0.96    inference(resolution,[],[f200,f39])).
% 4.49/0.96  fof(f200,plain,(
% 4.49/0.96    ( ! [X0] : (r2_hidden(sK3(sK1,k5_xboole_0(X0,X0)),sK1)) ) | ~spl5_2),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f179,f40])).
% 4.49/0.96  fof(f179,plain,(
% 4.49/0.96    ( ! [X0] : (~r1_tarski(sK1,k5_xboole_0(X0,X0))) ) | ~spl5_2),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f171,f99])).
% 4.49/0.96  fof(f99,plain,(
% 4.49/0.96    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2,X0)) ) | ~spl5_2),
% 4.49/0.96    inference(resolution,[],[f39,f85])).
% 4.49/0.96  fof(f3157,plain,(
% 4.49/0.96    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,sK0)) ) | ~spl5_74),
% 4.49/0.96    inference(subsumption_resolution,[],[f3146,f171])).
% 4.49/0.96  fof(f3146,plain,(
% 4.49/0.96    ( ! [X3] : (r2_hidden(X3,k5_xboole_0(sK2,sK2)) | r2_hidden(X3,sK0) | ~r2_hidden(X3,sK2)) ) | ~spl5_74),
% 4.49/0.96    inference(superposition,[],[f74,f2384])).
% 4.49/0.96  fof(f2384,plain,(
% 4.49/0.96    sK2 = k3_xboole_0(sK2,sK0) | ~spl5_74),
% 4.49/0.96    inference(avatar_component_clause,[],[f2382])).
% 4.49/0.96  fof(f3176,plain,(
% 4.49/0.96    ~spl5_84 | spl5_85 | ~spl5_6 | ~spl5_74),
% 4.49/0.96    inference(avatar_split_clause,[],[f3165,f2382,f154,f3173,f3169])).
% 4.49/0.96  fof(f3173,plain,(
% 4.49/0.96    spl5_85 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 4.49/0.96  fof(f154,plain,(
% 4.49/0.96    spl5_6 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 4.49/0.96  fof(f3165,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK0) | ~r1_tarski(sK1,sK2) | (~spl5_6 | ~spl5_74)),
% 4.49/0.96    inference(resolution,[],[f3157,f232])).
% 4.49/0.96  fof(f232,plain,(
% 4.49/0.96    ( ! [X0] : (r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),X0) | ~r1_tarski(sK1,X0)) ) | ~spl5_6),
% 4.49/0.96    inference(resolution,[],[f156,f39])).
% 4.49/0.96  fof(f156,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) | ~spl5_6),
% 4.49/0.96    inference(avatar_component_clause,[],[f154])).
% 4.49/0.96  fof(f3156,plain,(
% 4.49/0.96    spl5_83 | ~spl5_74),
% 4.49/0.96    inference(avatar_split_clause,[],[f3151,f2382,f3153])).
% 4.49/0.96  fof(f3153,plain,(
% 4.49/0.96    spl5_83 <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 4.49/0.96  fof(f3151,plain,(
% 4.49/0.96    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | ~spl5_74),
% 4.49/0.96    inference(forward_demodulation,[],[f3142,f1489])).
% 4.49/0.96  fof(f1489,plain,(
% 4.49/0.96    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = X4) )),
% 4.49/0.96    inference(backward_demodulation,[],[f1351,f1415])).
% 4.49/0.96  fof(f1351,plain,(
% 4.49/0.96    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,X3))) )),
% 4.49/0.96    inference(forward_demodulation,[],[f1350,f1347])).
% 4.49/0.96  fof(f1350,plain,(
% 4.49/0.96    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,X3))))) )),
% 4.49/0.96    inference(forward_demodulation,[],[f1328,f43])).
% 4.49/0.96  fof(f43,plain,(
% 4.49/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.49/0.96    inference(cnf_transformation,[],[f10])).
% 4.49/0.96  fof(f10,axiom,(
% 4.49/0.96    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.49/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.49/0.96  fof(f1328,plain,(
% 4.49/0.96    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) = k5_xboole_0(X4,k5_xboole_0(k5_xboole_0(X3,X3),k5_xboole_0(X3,X3)))) )),
% 4.49/0.96    inference(superposition,[],[f61,f190])).
% 4.49/0.96  fof(f190,plain,(
% 4.49/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X1)) )),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f180,f35])).
% 4.49/0.96  fof(f3142,plain,(
% 4.49/0.96    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k5_xboole_0(sK2,sK2))) | ~spl5_74),
% 4.49/0.96    inference(superposition,[],[f62,f2384])).
% 4.49/0.96  fof(f62,plain,(
% 4.49/0.96    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 4.49/0.96    inference(definition_unfolding,[],[f34,f56,f56,f32])).
% 4.49/0.96  fof(f34,plain,(
% 4.49/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.49/0.96    inference(cnf_transformation,[],[f8])).
% 4.49/0.96  fof(f8,axiom,(
% 4.49/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.49/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.49/0.96  fof(f3008,plain,(
% 4.49/0.96    ~spl5_74 | spl5_78),
% 4.49/0.96    inference(avatar_contradiction_clause,[],[f3007])).
% 4.49/0.96  fof(f3007,plain,(
% 4.49/0.96    $false | (~spl5_74 | spl5_78)),
% 4.49/0.96    inference(subsumption_resolution,[],[f2990,f180])).
% 4.49/0.96  fof(f2990,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK2,sK2),sK0) | (~spl5_74 | spl5_78)),
% 4.49/0.96    inference(backward_demodulation,[],[f2949,f2384])).
% 4.49/0.96  fof(f2949,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0) | spl5_78),
% 4.49/0.96    inference(avatar_component_clause,[],[f2947])).
% 4.49/0.96  fof(f2947,plain,(
% 4.49/0.96    spl5_78 <=> r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 4.49/0.96  fof(f2995,plain,(
% 4.49/0.96    ~spl5_81 | spl5_59 | ~spl5_74),
% 4.49/0.96    inference(avatar_split_clause,[],[f2994,f2382,f2244,f2971])).
% 4.49/0.96  fof(f2971,plain,(
% 4.49/0.96    spl5_81 <=> sK0 = sK2),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 4.49/0.96  fof(f2244,plain,(
% 4.49/0.96    spl5_59 <=> sK2 = k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 4.49/0.96  fof(f2994,plain,(
% 4.49/0.96    sK0 != sK2 | (spl5_59 | ~spl5_74)),
% 4.49/0.96    inference(forward_demodulation,[],[f2980,f1415])).
% 4.49/0.96  fof(f2980,plain,(
% 4.49/0.96    sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)) | (spl5_59 | ~spl5_74)),
% 4.49/0.96    inference(backward_demodulation,[],[f2246,f2384])).
% 4.49/0.96  fof(f2246,plain,(
% 4.49/0.96    sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | spl5_59),
% 4.49/0.96    inference(avatar_component_clause,[],[f2244])).
% 4.49/0.96  fof(f2978,plain,(
% 4.49/0.96    spl5_62 | spl5_82 | spl5_65),
% 4.49/0.96    inference(avatar_split_clause,[],[f2890,f2301,f2976,f2285])).
% 4.49/0.96  fof(f2285,plain,(
% 4.49/0.96    spl5_62 <=> r1_tarski(sK2,sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 4.49/0.96  fof(f2976,plain,(
% 4.49/0.96    spl5_82 <=> ! [X2] : ~r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 4.49/0.96  fof(f2301,plain,(
% 4.49/0.96    spl5_65 <=> r2_hidden(sK3(sK2,sK0),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 4.49/0.96  fof(f2890,plain,(
% 4.49/0.96    ( ! [X2] : (~r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2))) | r1_tarski(sK2,sK0)) ) | spl5_65),
% 4.49/0.96    inference(resolution,[],[f2408,f101])).
% 4.49/0.96  fof(f2408,plain,(
% 4.49/0.96    ( ! [X0] : (~r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ) | spl5_65),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2303,f76])).
% 4.49/0.96  fof(f2303,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK0),sK0) | spl5_65),
% 4.49/0.96    inference(avatar_component_clause,[],[f2301])).
% 4.49/0.96  fof(f2974,plain,(
% 4.49/0.96    ~spl5_81 | spl5_59),
% 4.49/0.96    inference(avatar_split_clause,[],[f2969,f2244,f2971])).
% 4.49/0.96  fof(f2969,plain,(
% 4.49/0.96    sK0 != sK2 | spl5_59),
% 4.49/0.96    inference(subsumption_resolution,[],[f2968,f72])).
% 4.49/0.96  fof(f2968,plain,(
% 4.49/0.96    sK0 != sK2 | ~r1_tarski(sK0,sK0) | spl5_59),
% 4.49/0.96    inference(inner_rewriting,[],[f2967])).
% 4.49/0.96  fof(f2967,plain,(
% 4.49/0.96    sK0 != sK2 | ~r1_tarski(sK2,sK0) | spl5_59),
% 4.49/0.96    inference(forward_demodulation,[],[f2792,f1415])).
% 4.49/0.96  fof(f2792,plain,(
% 4.49/0.96    sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)) | ~r1_tarski(sK2,sK0) | spl5_59),
% 4.49/0.96    inference(superposition,[],[f2246,f35])).
% 4.49/0.96  fof(f2966,plain,(
% 4.49/0.96    spl5_80 | ~spl5_75),
% 4.49/0.96    inference(avatar_split_clause,[],[f2917,f2416,f2962])).
% 4.49/0.96  fof(f2962,plain,(
% 4.49/0.96    spl5_80 <=> r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).
% 4.49/0.96  fof(f2416,plain,(
% 4.49/0.96    spl5_75 <=> r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 4.49/0.96  fof(f2917,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | ~spl5_75),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2418,f2418,f69])).
% 4.49/0.96  fof(f2418,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | ~spl5_75),
% 4.49/0.96    inference(avatar_component_clause,[],[f2416])).
% 4.49/0.96  fof(f2965,plain,(
% 4.49/0.96    spl5_80 | ~spl5_75),
% 4.49/0.96    inference(avatar_split_clause,[],[f2918,f2416,f2962])).
% 4.49/0.96  fof(f2918,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | ~spl5_75),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2418,f2418,f69])).
% 4.49/0.96  fof(f2956,plain,(
% 4.49/0.96    spl5_79 | spl5_65 | ~spl5_75),
% 4.49/0.96    inference(avatar_split_clause,[],[f2951,f2416,f2301,f2953])).
% 4.49/0.96  fof(f2953,plain,(
% 4.49/0.96    spl5_79 <=> r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 4.49/0.96  fof(f2951,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0)))) | (spl5_65 | ~spl5_75)),
% 4.49/0.96    inference(forward_demodulation,[],[f2923,f43])).
% 4.49/0.96  fof(f2923,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0))) | (spl5_65 | ~spl5_75)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2303,f2418,f74])).
% 4.49/0.96  fof(f2950,plain,(
% 4.49/0.96    ~spl5_78 | spl5_65 | ~spl5_75),
% 4.49/0.96    inference(avatar_split_clause,[],[f2931,f2416,f2301,f2947])).
% 4.49/0.96  fof(f2931,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)),sK0) | (spl5_65 | ~spl5_75)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2303,f2418,f39])).
% 4.49/0.96  fof(f2457,plain,(
% 4.49/0.96    spl5_77 | ~spl5_66 | spl5_67),
% 4.49/0.96    inference(avatar_split_clause,[],[f2443,f2313,f2308,f2454])).
% 4.49/0.96  fof(f2454,plain,(
% 4.49/0.96    spl5_77 <=> r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 4.49/0.96  fof(f2308,plain,(
% 4.49/0.96    spl5_66 <=> r2_hidden(sK3(sK0,sK2),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 4.49/0.96  fof(f2313,plain,(
% 4.49/0.96    spl5_67 <=> r2_hidden(sK3(sK0,sK2),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 4.49/0.96  fof(f2443,plain,(
% 4.49/0.96    r2_hidden(sK3(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) | (~spl5_66 | spl5_67)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2310,f2315,f74])).
% 4.49/0.96  fof(f2315,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK0,sK2),sK2) | spl5_67),
% 4.49/0.96    inference(avatar_component_clause,[],[f2313])).
% 4.49/0.96  fof(f2310,plain,(
% 4.49/0.96    r2_hidden(sK3(sK0,sK2),sK0) | ~spl5_66),
% 4.49/0.96    inference(avatar_component_clause,[],[f2308])).
% 4.49/0.96  fof(f2440,plain,(
% 4.49/0.96    spl5_76 | ~spl5_66),
% 4.49/0.96    inference(avatar_split_clause,[],[f2420,f2308,f2436])).
% 4.49/0.96  fof(f2436,plain,(
% 4.49/0.96    spl5_76 <=> r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 4.49/0.96  fof(f2420,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) | ~spl5_66),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2310,f2310,f69])).
% 4.49/0.96  fof(f2439,plain,(
% 4.49/0.96    spl5_76 | ~spl5_66),
% 4.49/0.96    inference(avatar_split_clause,[],[f2421,f2308,f2436])).
% 4.49/0.96  fof(f2421,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2),sK3(sK0,sK2)),sK0) | ~spl5_66),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2310,f2310,f69])).
% 4.49/0.96  fof(f2419,plain,(
% 4.49/0.96    spl5_75 | ~spl5_64 | spl5_65),
% 4.49/0.96    inference(avatar_split_clause,[],[f2405,f2301,f2296,f2416])).
% 4.49/0.96  fof(f2296,plain,(
% 4.49/0.96    spl5_64 <=> r2_hidden(sK3(sK2,sK0),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 4.49/0.96  fof(f2405,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | (~spl5_64 | spl5_65)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2298,f2303,f74])).
% 4.49/0.96  fof(f2298,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),sK2) | ~spl5_64),
% 4.49/0.96    inference(avatar_component_clause,[],[f2296])).
% 4.49/0.96  fof(f2385,plain,(
% 4.49/0.96    spl5_74 | ~spl5_62),
% 4.49/0.96    inference(avatar_split_clause,[],[f2379,f2285,f2382])).
% 4.49/0.96  fof(f2379,plain,(
% 4.49/0.96    sK2 = k3_xboole_0(sK2,sK0) | ~spl5_62),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2286,f35])).
% 4.49/0.96  fof(f2286,plain,(
% 4.49/0.96    r1_tarski(sK2,sK0) | ~spl5_62),
% 4.49/0.96    inference(avatar_component_clause,[],[f2285])).
% 4.49/0.96  fof(f2377,plain,(
% 4.49/0.96    spl5_73 | ~spl5_64),
% 4.49/0.96    inference(avatar_split_clause,[],[f2357,f2296,f2373])).
% 4.49/0.96  fof(f2373,plain,(
% 4.49/0.96    spl5_73 <=> r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 4.49/0.96  fof(f2357,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2) | ~spl5_64),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2298,f2298,f69])).
% 4.49/0.96  fof(f2376,plain,(
% 4.49/0.96    spl5_73 | ~spl5_64),
% 4.49/0.96    inference(avatar_split_clause,[],[f2358,f2296,f2373])).
% 4.49/0.96  fof(f2358,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0),sK3(sK2,sK0)),sK2) | ~spl5_64),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2298,f2298,f69])).
% 4.49/0.96  fof(f2356,plain,(
% 4.49/0.96    ~spl5_72 | spl5_1),
% 4.49/0.96    inference(avatar_split_clause,[],[f2337,f78,f2352])).
% 4.49/0.96  fof(f78,plain,(
% 4.49/0.96    spl5_1 <=> sK1 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 4.49/0.96  fof(f2337,plain,(
% 4.49/0.96    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl5_1),
% 4.49/0.96    inference(superposition,[],[f80,f60])).
% 4.49/0.96  fof(f60,plain,(
% 4.49/0.96    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 4.49/0.96    inference(definition_unfolding,[],[f29,f56,f56])).
% 4.49/0.96  fof(f29,plain,(
% 4.49/0.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.49/0.96    inference(cnf_transformation,[],[f1])).
% 4.49/0.96  fof(f1,axiom,(
% 4.49/0.96    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.49/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.49/0.96  fof(f80,plain,(
% 4.49/0.96    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) | spl5_1),
% 4.49/0.96    inference(avatar_component_clause,[],[f78])).
% 4.49/0.96  fof(f2355,plain,(
% 4.49/0.96    ~spl5_72 | spl5_1),
% 4.49/0.96    inference(avatar_split_clause,[],[f2336,f78,f2352])).
% 4.49/0.96  fof(f2336,plain,(
% 4.49/0.96    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) | spl5_1),
% 4.49/0.96    inference(superposition,[],[f80,f60])).
% 4.49/0.96  fof(f2350,plain,(
% 4.49/0.96    ~spl5_71 | spl5_1),
% 4.49/0.96    inference(avatar_split_clause,[],[f2335,f78,f2347])).
% 4.49/0.96  fof(f2347,plain,(
% 4.49/0.96    spl5_71 <=> sK1 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 4.49/0.96  fof(f2335,plain,(
% 4.49/0.96    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))) | spl5_1),
% 4.49/0.96    inference(superposition,[],[f80,f61])).
% 4.49/0.96  fof(f2345,plain,(
% 4.49/0.96    ~spl5_70 | spl5_1),
% 4.49/0.96    inference(avatar_split_clause,[],[f2344,f78,f2340])).
% 4.49/0.96  fof(f2340,plain,(
% 4.49/0.96    spl5_70 <=> r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 4.49/0.96  fof(f2344,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) | spl5_1),
% 4.49/0.96    inference(forward_demodulation,[],[f2333,f60])).
% 4.49/0.96  fof(f2333,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),sK1) | spl5_1),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1206,f80,f38])).
% 4.49/0.96  fof(f1206,plain,(
% 4.49/0.96    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) )),
% 4.49/0.96    inference(superposition,[],[f59,f60])).
% 4.49/0.96  fof(f59,plain,(
% 4.49/0.96    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 4.49/0.96    inference(definition_unfolding,[],[f28,f56])).
% 4.49/0.96  fof(f28,plain,(
% 4.49/0.96    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.49/0.96    inference(cnf_transformation,[],[f9])).
% 4.49/0.96  fof(f9,axiom,(
% 4.49/0.96    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.49/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.49/0.96  fof(f2343,plain,(
% 4.49/0.96    ~spl5_70 | spl5_1),
% 4.49/0.96    inference(avatar_split_clause,[],[f2338,f78,f2340])).
% 4.49/0.96  fof(f2338,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),sK1) | spl5_1),
% 4.49/0.96    inference(forward_demodulation,[],[f2334,f60])).
% 4.49/0.96  fof(f2334,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),sK1) | spl5_1),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1206,f80,f38])).
% 4.49/0.96  fof(f2330,plain,(
% 4.49/0.96    ~spl5_69 | spl5_51 | ~spl5_63),
% 4.49/0.96    inference(avatar_split_clause,[],[f2318,f2289,f1756,f2327])).
% 4.49/0.96  fof(f2327,plain,(
% 4.49/0.96    spl5_69 <=> r2_hidden(sK3(sK2,sK2),sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 4.49/0.96  fof(f1756,plain,(
% 4.49/0.96    spl5_51 <=> r2_hidden(sK3(sK2,sK2),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 4.49/0.96  fof(f2289,plain,(
% 4.49/0.96    spl5_63 <=> r1_tarski(sK0,sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 4.49/0.96  fof(f2318,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK0) | (spl5_51 | ~spl5_63)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1758,f2290,f39])).
% 4.49/0.96  fof(f2290,plain,(
% 4.49/0.96    r1_tarski(sK0,sK2) | ~spl5_63),
% 4.49/0.96    inference(avatar_component_clause,[],[f2289])).
% 4.49/0.96  fof(f1758,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK2) | spl5_51),
% 4.49/0.96    inference(avatar_component_clause,[],[f1756])).
% 4.49/0.96  fof(f2325,plain,(
% 4.49/0.96    spl5_68 | ~spl5_63),
% 4.49/0.96    inference(avatar_split_clause,[],[f2319,f2289,f2322])).
% 4.49/0.96  fof(f2322,plain,(
% 4.49/0.96    spl5_68 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 4.49/0.96  fof(f2319,plain,(
% 4.49/0.96    sK0 = k3_xboole_0(sK0,sK2) | ~spl5_63),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2290,f35])).
% 4.49/0.96  fof(f2316,plain,(
% 4.49/0.96    ~spl5_67 | spl5_63),
% 4.49/0.96    inference(avatar_split_clause,[],[f2305,f2289,f2313])).
% 4.49/0.96  fof(f2305,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK0,sK2),sK2) | spl5_63),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2291,f41])).
% 4.49/0.96  fof(f2291,plain,(
% 4.49/0.96    ~r1_tarski(sK0,sK2) | spl5_63),
% 4.49/0.96    inference(avatar_component_clause,[],[f2289])).
% 4.49/0.96  fof(f2311,plain,(
% 4.49/0.96    spl5_66 | spl5_63),
% 4.49/0.96    inference(avatar_split_clause,[],[f2306,f2289,f2308])).
% 4.49/0.96  fof(f2306,plain,(
% 4.49/0.96    r2_hidden(sK3(sK0,sK2),sK0) | spl5_63),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2291,f40])).
% 4.49/0.96  fof(f2304,plain,(
% 4.49/0.96    ~spl5_65 | spl5_62),
% 4.49/0.96    inference(avatar_split_clause,[],[f2293,f2285,f2301])).
% 4.49/0.96  fof(f2293,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK0),sK0) | spl5_62),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2287,f41])).
% 4.49/0.96  fof(f2287,plain,(
% 4.49/0.96    ~r1_tarski(sK2,sK0) | spl5_62),
% 4.49/0.96    inference(avatar_component_clause,[],[f2285])).
% 4.49/0.96  fof(f2299,plain,(
% 4.49/0.96    spl5_64 | spl5_62),
% 4.49/0.96    inference(avatar_split_clause,[],[f2294,f2285,f2296])).
% 4.49/0.96  fof(f2294,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,sK0),sK2) | spl5_62),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2287,f40])).
% 4.49/0.96  fof(f2292,plain,(
% 4.49/0.96    ~spl5_62 | ~spl5_63 | spl5_58),
% 4.49/0.96    inference(avatar_split_clause,[],[f2283,f2237,f2289,f2285])).
% 4.49/0.96  fof(f2237,plain,(
% 4.49/0.96    spl5_58 <=> r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 4.49/0.96  fof(f2283,plain,(
% 4.49/0.96    ~r1_tarski(sK0,sK2) | ~r1_tarski(sK2,sK0) | spl5_58),
% 4.49/0.96    inference(forward_demodulation,[],[f2269,f1415])).
% 4.49/0.96  fof(f2269,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,sK2)),sK2) | ~r1_tarski(sK2,sK0) | spl5_58),
% 4.49/0.96    inference(superposition,[],[f2239,f35])).
% 4.49/0.96  fof(f2239,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2) | spl5_58),
% 4.49/0.96    inference(avatar_component_clause,[],[f2237])).
% 4.49/0.96  fof(f2282,plain,(
% 4.49/0.96    ~spl5_61 | spl5_58),
% 4.49/0.96    inference(avatar_split_clause,[],[f2267,f2237,f2279])).
% 4.49/0.96  fof(f2279,plain,(
% 4.49/0.96    spl5_61 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 4.49/0.96  fof(f2267,plain,(
% 4.49/0.96    ~r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),sK2) | spl5_58),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2239,f41])).
% 4.49/0.96  fof(f2277,plain,(
% 4.49/0.96    spl5_60 | spl5_58),
% 4.49/0.96    inference(avatar_split_clause,[],[f2268,f2237,f2274])).
% 4.49/0.96  fof(f2274,plain,(
% 4.49/0.96    spl5_60 <=> r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 4.49/0.96  fof(f2268,plain,(
% 4.49/0.96    r2_hidden(sK3(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2),k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)))) | spl5_58),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f2239,f40])).
% 4.49/0.96  fof(f2247,plain,(
% 4.49/0.96    ~spl5_59 | spl5_50),
% 4.49/0.96    inference(avatar_split_clause,[],[f2234,f1751,f2244])).
% 4.49/0.96  fof(f1751,plain,(
% 4.49/0.96    spl5_50 <=> sK2 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 4.49/0.96  fof(f2234,plain,(
% 4.49/0.96    sK2 != k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))) | spl5_50),
% 4.49/0.96    inference(superposition,[],[f1753,f61])).
% 4.49/0.96  fof(f1753,plain,(
% 4.49/0.96    sK2 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_50),
% 4.49/0.96    inference(avatar_component_clause,[],[f1751])).
% 4.49/0.96  fof(f2242,plain,(
% 4.49/0.96    ~spl5_58 | spl5_50),
% 4.49/0.96    inference(avatar_split_clause,[],[f2241,f1751,f2237])).
% 4.49/0.96  fof(f2241,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2) | spl5_50),
% 4.49/0.96    inference(forward_demodulation,[],[f2232,f61])).
% 4.49/0.96  fof(f2232,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2) | spl5_50),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1206,f1753,f38])).
% 4.49/0.96  fof(f2240,plain,(
% 4.49/0.96    ~spl5_58 | spl5_50),
% 4.49/0.96    inference(avatar_split_clause,[],[f2235,f1751,f2237])).
% 4.49/0.96  fof(f2235,plain,(
% 4.49/0.96    ~r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),sK2) | spl5_50),
% 4.49/0.96    inference(forward_demodulation,[],[f2233,f61])).
% 4.49/0.96  fof(f2233,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK2) | spl5_50),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1206,f1753,f38])).
% 4.49/0.96  fof(f1877,plain,(
% 4.49/0.96    ~spl5_57 | spl5_26),
% 4.49/0.96    inference(avatar_split_clause,[],[f1866,f1160,f1874])).
% 4.49/0.96  fof(f1874,plain,(
% 4.49/0.96    spl5_57 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 4.49/0.96  fof(f1160,plain,(
% 4.49/0.96    spl5_26 <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 4.49/0.96  fof(f1866,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl5_26),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1162,f41])).
% 4.49/0.96  fof(f1162,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl5_26),
% 4.49/0.96    inference(avatar_component_clause,[],[f1160])).
% 4.49/0.96  fof(f1872,plain,(
% 4.49/0.96    spl5_56 | spl5_26),
% 4.49/0.96    inference(avatar_split_clause,[],[f1867,f1160,f1869])).
% 4.49/0.96  fof(f1869,plain,(
% 4.49/0.96    spl5_56 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 4.49/0.96  fof(f1867,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK1) | spl5_26),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1162,f40])).
% 4.49/0.96  fof(f1818,plain,(
% 4.49/0.96    ~spl5_55 | spl5_23),
% 4.49/0.96    inference(avatar_split_clause,[],[f1807,f1136,f1815])).
% 4.49/0.96  fof(f1815,plain,(
% 4.49/0.96    spl5_55 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 4.49/0.96  fof(f1136,plain,(
% 4.49/0.96    spl5_23 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 4.49/0.96  fof(f1807,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_23),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1138,f41])).
% 4.49/0.96  fof(f1138,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_23),
% 4.49/0.96    inference(avatar_component_clause,[],[f1136])).
% 4.49/0.96  fof(f1813,plain,(
% 4.49/0.96    spl5_54 | spl5_23),
% 4.49/0.96    inference(avatar_split_clause,[],[f1808,f1136,f1810])).
% 4.49/0.96  fof(f1810,plain,(
% 4.49/0.96    spl5_54 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 4.49/0.96  fof(f1808,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)),sK1) | spl5_23),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1138,f40])).
% 4.49/0.96  fof(f1800,plain,(
% 4.49/0.96    ~spl5_53 | ~spl5_12 | spl5_31),
% 4.49/0.96    inference(avatar_split_clause,[],[f1789,f1201,f1054,f1797])).
% 4.49/0.96  fof(f1797,plain,(
% 4.49/0.96    spl5_53 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 4.49/0.96  fof(f1201,plain,(
% 4.49/0.96    spl5_31 <=> r2_hidden(sK3(sK1,sK1),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 4.49/0.96  fof(f1789,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK0)) | (~spl5_12 | spl5_31)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1203,f1056,f39])).
% 4.49/0.96  fof(f1203,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),sK1) | spl5_31),
% 4.49/0.96    inference(avatar_component_clause,[],[f1201])).
% 4.49/0.96  fof(f1770,plain,(
% 4.49/0.96    spl5_37 | ~spl5_40 | ~spl5_49),
% 4.49/0.96    inference(avatar_contradiction_clause,[],[f1769])).
% 4.49/0.96  fof(f1769,plain,(
% 4.49/0.96    $false | (spl5_37 | ~spl5_40 | ~spl5_49)),
% 4.49/0.96    inference(subsumption_resolution,[],[f1749,f1735])).
% 4.49/0.96  fof(f1735,plain,(
% 4.49/0.96    ( ! [X0] : (~r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),X0),sK2)) ) | (spl5_37 | ~spl5_40)),
% 4.49/0.96    inference(backward_demodulation,[],[f1398,f1294])).
% 4.49/0.96  fof(f1294,plain,(
% 4.49/0.96    sK2 = k3_tarski(sK1) | ~spl5_40),
% 4.49/0.96    inference(avatar_component_clause,[],[f1292])).
% 4.49/0.96  fof(f1292,plain,(
% 4.49/0.96    spl5_40 <=> sK2 = k3_tarski(sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 4.49/0.96  fof(f1398,plain,(
% 4.49/0.96    ( ! [X0] : (~r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),X0),sK2)) ) | spl5_37),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f519,f1275,f39])).
% 4.49/0.96  fof(f1275,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | spl5_37),
% 4.49/0.96    inference(avatar_component_clause,[],[f1274])).
% 4.49/0.96  fof(f1274,plain,(
% 4.49/0.96    spl5_37 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 4.49/0.96  fof(f519,plain,(
% 4.49/0.96    ( ! [X0,X1] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X1))) )),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f72,f71])).
% 4.49/0.96  fof(f71,plain,(
% 4.49/0.96    ( ! [X2,X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 4.49/0.96    inference(definition_unfolding,[],[f50,f55])).
% 4.49/0.96  fof(f50,plain,(
% 4.49/0.96    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 4.49/0.96    inference(cnf_transformation,[],[f16])).
% 4.49/0.96  fof(f1749,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) | (~spl5_40 | ~spl5_49)),
% 4.49/0.96    inference(backward_demodulation,[],[f1712,f1294])).
% 4.49/0.96  fof(f1712,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_49),
% 4.49/0.96    inference(avatar_component_clause,[],[f1710])).
% 4.49/0.96  fof(f1710,plain,(
% 4.49/0.96    spl5_49 <=> r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 4.49/0.96  fof(f1767,plain,(
% 4.49/0.96    spl5_52 | ~spl5_40 | ~spl5_45),
% 4.49/0.96    inference(avatar_split_clause,[],[f1730,f1377,f1292,f1764])).
% 4.49/0.96  fof(f1764,plain,(
% 4.49/0.96    spl5_52 <=> r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 4.49/0.96  fof(f1377,plain,(
% 4.49/0.96    spl5_45 <=> r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 4.49/0.96  fof(f1730,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2),sK3(sK2,sK2)),sK2) | (~spl5_40 | ~spl5_45)),
% 4.49/0.96    inference(backward_demodulation,[],[f1379,f1294])).
% 4.49/0.96  fof(f1379,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_45),
% 4.49/0.96    inference(avatar_component_clause,[],[f1377])).
% 4.49/0.96  fof(f1762,plain,(
% 4.49/0.96    ~spl5_51 | ~spl5_40 | spl5_43),
% 4.49/0.96    inference(avatar_split_clause,[],[f1728,f1310,f1292,f1756])).
% 4.49/0.96  fof(f1310,plain,(
% 4.49/0.96    spl5_43 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 4.49/0.96  fof(f1728,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_40 | spl5_43)),
% 4.49/0.96    inference(backward_demodulation,[],[f1312,f1294])).
% 4.49/0.96  fof(f1312,plain,(
% 4.49/0.96    ~r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) | spl5_43),
% 4.49/0.96    inference(avatar_component_clause,[],[f1310])).
% 4.49/0.96  fof(f1761,plain,(
% 4.49/0.96    ~spl5_51 | ~spl5_40 | spl5_42),
% 4.49/0.96    inference(avatar_split_clause,[],[f1727,f1305,f1292,f1756])).
% 4.49/0.96  fof(f1305,plain,(
% 4.49/0.96    spl5_42 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 4.49/0.96  fof(f1727,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK2) | (~spl5_40 | spl5_42)),
% 4.49/0.96    inference(backward_demodulation,[],[f1306,f1294])).
% 4.49/0.96  fof(f1306,plain,(
% 4.49/0.96    ~r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | spl5_42),
% 4.49/0.96    inference(avatar_component_clause,[],[f1305])).
% 4.49/0.96  fof(f1760,plain,(
% 4.49/0.96    ~spl5_51 | spl5_38 | ~spl5_40),
% 4.49/0.96    inference(avatar_split_clause,[],[f1724,f1292,f1279,f1756])).
% 4.49/0.96  fof(f1279,plain,(
% 4.49/0.96    spl5_38 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 4.49/0.96  fof(f1724,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK2) | (spl5_38 | ~spl5_40)),
% 4.49/0.96    inference(backward_demodulation,[],[f1281,f1294])).
% 4.49/0.96  fof(f1281,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) | spl5_38),
% 4.49/0.96    inference(avatar_component_clause,[],[f1279])).
% 4.49/0.96  fof(f1759,plain,(
% 4.49/0.96    ~spl5_51 | spl5_37 | ~spl5_40),
% 4.49/0.96    inference(avatar_split_clause,[],[f1723,f1292,f1274,f1756])).
% 4.49/0.96  fof(f1723,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,sK2),sK2) | (spl5_37 | ~spl5_40)),
% 4.49/0.96    inference(backward_demodulation,[],[f1275,f1294])).
% 4.49/0.96  fof(f1754,plain,(
% 4.49/0.96    ~spl5_50 | spl5_36 | ~spl5_40),
% 4.49/0.96    inference(avatar_split_clause,[],[f1722,f1292,f1266,f1751])).
% 4.49/0.96  fof(f1266,plain,(
% 4.49/0.96    spl5_36 <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 4.49/0.96  fof(f1722,plain,(
% 4.49/0.96    sK2 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | (spl5_36 | ~spl5_40)),
% 4.49/0.96    inference(backward_demodulation,[],[f1267,f1294])).
% 4.49/0.96  fof(f1267,plain,(
% 4.49/0.96    k3_tarski(sK1) != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | spl5_36),
% 4.49/0.96    inference(avatar_component_clause,[],[f1266])).
% 4.49/0.96  fof(f1720,plain,(
% 4.49/0.96    spl5_40 | ~spl5_35 | ~spl5_41),
% 4.49/0.96    inference(avatar_split_clause,[],[f1719,f1296,f1261,f1292])).
% 4.49/0.96  fof(f1261,plain,(
% 4.49/0.96    spl5_35 <=> r1_tarski(sK2,k3_tarski(sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 4.49/0.96  fof(f1296,plain,(
% 4.49/0.96    spl5_41 <=> r1_tarski(k3_tarski(sK1),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 4.49/0.96  fof(f1719,plain,(
% 4.49/0.96    sK2 = k3_tarski(sK1) | (~spl5_35 | ~spl5_41)),
% 4.49/0.96    inference(subsumption_resolution,[],[f1318,f1263])).
% 4.49/0.96  fof(f1263,plain,(
% 4.49/0.96    r1_tarski(sK2,k3_tarski(sK1)) | ~spl5_35),
% 4.49/0.96    inference(avatar_component_clause,[],[f1261])).
% 4.49/0.96  fof(f1318,plain,(
% 4.49/0.96    ~r1_tarski(sK2,k3_tarski(sK1)) | sK2 = k3_tarski(sK1) | ~spl5_41),
% 4.49/0.96    inference(resolution,[],[f1297,f38])).
% 4.49/0.96  fof(f1297,plain,(
% 4.49/0.96    r1_tarski(k3_tarski(sK1),sK2) | ~spl5_41),
% 4.49/0.96    inference(avatar_component_clause,[],[f1296])).
% 4.49/0.96  fof(f1717,plain,(
% 4.49/0.96    spl5_40 | ~spl5_41 | ~spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1386,f1261,f1296,f1292])).
% 4.49/0.96  fof(f1386,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_35),
% 4.49/0.96    inference(resolution,[],[f1263,f38])).
% 4.49/0.96  fof(f1716,plain,(
% 4.49/0.96    spl5_40 | ~spl5_41 | ~spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1285,f1261,f1296,f1292])).
% 4.49/0.96  fof(f1285,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_35),
% 4.49/0.96    inference(resolution,[],[f1263,f38])).
% 4.49/0.96  fof(f1715,plain,(
% 4.49/0.96    spl5_40 | ~spl5_41 | ~spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1639,f1261,f1296,f1292])).
% 4.49/0.96  fof(f1639,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(sK1),sK2) | sK2 = k3_tarski(sK1) | ~spl5_35),
% 4.49/0.96    inference(resolution,[],[f1263,f38])).
% 4.49/0.96  fof(f1714,plain,(
% 4.49/0.96    spl5_49 | ~spl5_42),
% 4.49/0.96    inference(avatar_split_clause,[],[f1691,f1305,f1710])).
% 4.49/0.96  fof(f1691,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_42),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1307,f1307,f69])).
% 4.49/0.96  fof(f1307,plain,(
% 4.49/0.96    r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | ~spl5_42),
% 4.49/0.96    inference(avatar_component_clause,[],[f1305])).
% 4.49/0.96  fof(f1713,plain,(
% 4.49/0.96    spl5_49 | ~spl5_42),
% 4.49/0.96    inference(avatar_split_clause,[],[f1692,f1305,f1710])).
% 4.49/0.96  fof(f1692,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2),sK3(k3_tarski(sK1),sK2)),k3_tarski(sK1)) | ~spl5_42),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1307,f1307,f69])).
% 4.49/0.96  fof(f1708,plain,(
% 4.49/0.96    spl5_48 | ~spl5_42 | spl5_43),
% 4.49/0.96    inference(avatar_split_clause,[],[f1695,f1310,f1305,f1705])).
% 4.49/0.96  fof(f1705,plain,(
% 4.49/0.96    spl5_48 <=> r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2)))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 4.49/0.96  fof(f1695,plain,(
% 4.49/0.96    r2_hidden(sK3(k3_tarski(sK1),sK2),k5_xboole_0(k3_tarski(sK1),k3_xboole_0(k3_tarski(sK1),sK2))) | (~spl5_42 | spl5_43)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1312,f1307,f74])).
% 4.49/0.96  fof(f1633,plain,(
% 4.49/0.96    spl5_35 | spl5_37),
% 4.49/0.96    inference(avatar_split_clause,[],[f1387,f1274,f1261])).
% 4.49/0.96  fof(f1387,plain,(
% 4.49/0.96    r1_tarski(sK2,k3_tarski(sK1)) | spl5_37),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1275,f40])).
% 4.49/0.96  fof(f1632,plain,(
% 4.49/0.96    spl5_35 | spl5_37),
% 4.49/0.96    inference(avatar_split_clause,[],[f1399,f1274,f1261])).
% 4.49/0.96  fof(f1399,plain,(
% 4.49/0.96    r1_tarski(sK2,k3_tarski(sK1)) | spl5_37),
% 4.49/0.96    inference(resolution,[],[f1275,f40])).
% 4.49/0.96  fof(f1630,plain,(
% 4.49/0.96    spl5_47 | ~spl5_37 | spl5_38),
% 4.49/0.96    inference(avatar_split_clause,[],[f1616,f1279,f1274,f1627])).
% 4.49/0.96  fof(f1627,plain,(
% 4.49/0.96    spl5_47 <=> r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 4.49/0.96  fof(f1616,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,k3_tarski(sK1)),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_tarski(sK1)))) | (~spl5_37 | spl5_38)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1276,f1281,f74])).
% 4.49/0.96  fof(f1276,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | ~spl5_37),
% 4.49/0.96    inference(avatar_component_clause,[],[f1274])).
% 4.49/0.96  fof(f1587,plain,(
% 4.49/0.96    spl5_46 | ~spl5_39),
% 4.49/0.96    inference(avatar_split_clause,[],[f1582,f1287,f1584])).
% 4.49/0.96  fof(f1584,plain,(
% 4.49/0.96    spl5_46 <=> k3_tarski(sK1) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 4.49/0.96  fof(f1287,plain,(
% 4.49/0.96    spl5_39 <=> sK2 = k3_xboole_0(sK2,k3_tarski(sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 4.49/0.96  fof(f1582,plain,(
% 4.49/0.96    k3_tarski(sK1) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) | ~spl5_39),
% 4.49/0.96    inference(forward_demodulation,[],[f1571,f1489])).
% 4.49/0.96  fof(f1571,plain,(
% 4.49/0.96    k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),sK2)) = k3_tarski(k3_enumset1(k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k3_tarski(sK1),k5_xboole_0(sK2,sK2))) | ~spl5_39),
% 4.49/0.96    inference(superposition,[],[f62,f1289])).
% 4.49/0.96  fof(f1289,plain,(
% 4.49/0.96    sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) | ~spl5_39),
% 4.49/0.96    inference(avatar_component_clause,[],[f1287])).
% 4.49/0.96  fof(f1381,plain,(
% 4.49/0.96    spl5_45 | ~spl5_37),
% 4.49/0.96    inference(avatar_split_clause,[],[f1363,f1274,f1377])).
% 4.49/0.96  fof(f1363,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_37),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1276,f1276,f69])).
% 4.49/0.96  fof(f1380,plain,(
% 4.49/0.96    spl5_45 | ~spl5_37),
% 4.49/0.96    inference(avatar_split_clause,[],[f1364,f1274,f1377])).
% 4.49/0.96  fof(f1364,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1)),sK3(sK2,k3_tarski(sK1))),sK2) | ~spl5_37),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1276,f1276,f69])).
% 4.49/0.96  fof(f1323,plain,(
% 4.49/0.96    spl5_44 | ~spl5_41),
% 4.49/0.96    inference(avatar_split_clause,[],[f1317,f1296,f1320])).
% 4.49/0.96  fof(f1320,plain,(
% 4.49/0.96    spl5_44 <=> k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 4.49/0.96  fof(f1317,plain,(
% 4.49/0.96    k3_tarski(sK1) = k3_xboole_0(k3_tarski(sK1),sK2) | ~spl5_41),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1297,f35])).
% 4.49/0.96  fof(f1313,plain,(
% 4.49/0.96    ~spl5_43 | spl5_41),
% 4.49/0.96    inference(avatar_split_clause,[],[f1302,f1296,f1310])).
% 4.49/0.96  fof(f1302,plain,(
% 4.49/0.96    ~r2_hidden(sK3(k3_tarski(sK1),sK2),sK2) | spl5_41),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1298,f41])).
% 4.49/0.96  fof(f1298,plain,(
% 4.49/0.96    ~r1_tarski(k3_tarski(sK1),sK2) | spl5_41),
% 4.49/0.96    inference(avatar_component_clause,[],[f1296])).
% 4.49/0.96  fof(f1308,plain,(
% 4.49/0.96    spl5_42 | spl5_41),
% 4.49/0.96    inference(avatar_split_clause,[],[f1303,f1296,f1305])).
% 4.49/0.96  fof(f1303,plain,(
% 4.49/0.96    r2_hidden(sK3(k3_tarski(sK1),sK2),k3_tarski(sK1)) | spl5_41),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1298,f40])).
% 4.49/0.96  fof(f1299,plain,(
% 4.49/0.96    spl5_40 | ~spl5_41 | ~spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1285,f1261,f1296,f1292])).
% 4.49/0.96  fof(f1290,plain,(
% 4.49/0.96    spl5_39 | ~spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1284,f1261,f1287])).
% 4.49/0.96  fof(f1284,plain,(
% 4.49/0.96    sK2 = k3_xboole_0(sK2,k3_tarski(sK1)) | ~spl5_35),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1263,f35])).
% 4.49/0.96  fof(f1282,plain,(
% 4.49/0.96    ~spl5_38 | spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1271,f1261,f1279])).
% 4.49/0.96  fof(f1271,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK2,k3_tarski(sK1)),k3_tarski(sK1)) | spl5_35),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1262,f41])).
% 4.49/0.96  fof(f1262,plain,(
% 4.49/0.96    ~r1_tarski(sK2,k3_tarski(sK1)) | spl5_35),
% 4.49/0.96    inference(avatar_component_clause,[],[f1261])).
% 4.49/0.96  fof(f1277,plain,(
% 4.49/0.96    spl5_37 | spl5_35),
% 4.49/0.96    inference(avatar_split_clause,[],[f1272,f1261,f1274])).
% 4.49/0.96  fof(f1272,plain,(
% 4.49/0.96    r2_hidden(sK3(sK2,k3_tarski(sK1)),sK2) | spl5_35),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1262,f40])).
% 4.49/0.96  fof(f1270,plain,(
% 4.49/0.96    spl5_36 | ~spl5_19),
% 4.49/0.96    inference(avatar_split_clause,[],[f1253,f1108,f1266])).
% 4.49/0.96  fof(f1108,plain,(
% 4.49/0.96    spl5_19 <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 4.49/0.96  fof(f1253,plain,(
% 4.49/0.96    k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | ~spl5_19),
% 4.49/0.96    inference(superposition,[],[f60,f1110])).
% 4.49/0.96  fof(f1110,plain,(
% 4.49/0.96    sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0) | ~spl5_19),
% 4.49/0.96    inference(avatar_component_clause,[],[f1108])).
% 4.49/0.96  fof(f1269,plain,(
% 4.49/0.96    spl5_36 | ~spl5_19),
% 4.49/0.96    inference(avatar_split_clause,[],[f1252,f1108,f1266])).
% 4.49/0.96  fof(f1252,plain,(
% 4.49/0.96    k3_tarski(sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | ~spl5_19),
% 4.49/0.96    inference(superposition,[],[f60,f1110])).
% 4.49/0.96  fof(f1264,plain,(
% 4.49/0.96    spl5_35 | ~spl5_19),
% 4.49/0.96    inference(avatar_split_clause,[],[f1251,f1108,f1261])).
% 4.49/0.96  fof(f1251,plain,(
% 4.49/0.96    r1_tarski(sK2,k3_tarski(sK1)) | ~spl5_19),
% 4.49/0.96    inference(superposition,[],[f59,f1110])).
% 4.49/0.96  fof(f1250,plain,(
% 4.49/0.96    ~spl5_34 | ~spl5_11 | spl5_31),
% 4.49/0.96    inference(avatar_split_clause,[],[f1230,f1201,f1049,f1247])).
% 4.49/0.96  fof(f1247,plain,(
% 4.49/0.96    spl5_34 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 4.49/0.96  fof(f1230,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (~spl5_11 | spl5_31)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1051,f1203,f39])).
% 4.49/0.96  fof(f1245,plain,(
% 4.49/0.96    ~spl5_33 | ~spl5_13 | spl5_31),
% 4.49/0.96    inference(avatar_split_clause,[],[f1231,f1201,f1059,f1242])).
% 4.49/0.96  fof(f1242,plain,(
% 4.49/0.96    spl5_33 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 4.49/0.96  fof(f1231,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | (~spl5_13 | spl5_31)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1061,f1203,f39])).
% 4.49/0.96  fof(f1240,plain,(
% 4.49/0.96    ~spl5_32 | ~spl5_14 | spl5_31),
% 4.49/0.96    inference(avatar_split_clause,[],[f1232,f1201,f1064,f1237])).
% 4.49/0.96  fof(f1237,plain,(
% 4.49/0.96    spl5_32 <=> r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 4.49/0.96  fof(f1232,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | (~spl5_14 | spl5_31)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1066,f1203,f39])).
% 4.49/0.96  fof(f1205,plain,(
% 4.49/0.96    ~spl5_31 | ~spl5_19 | spl5_30),
% 4.49/0.96    inference(avatar_split_clause,[],[f1199,f1188,f1108,f1201])).
% 4.49/0.96  fof(f1188,plain,(
% 4.49/0.96    spl5_30 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 4.49/0.96  fof(f1199,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),sK1) | (~spl5_19 | spl5_30)),
% 4.49/0.96    inference(backward_demodulation,[],[f1190,f1110])).
% 4.49/0.96  fof(f1190,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0)) | spl5_30),
% 4.49/0.96    inference(avatar_component_clause,[],[f1188])).
% 4.49/0.96  fof(f1204,plain,(
% 4.49/0.96    ~spl5_31 | ~spl5_19 | spl5_29),
% 4.49/0.96    inference(avatar_split_clause,[],[f1198,f1183,f1108,f1201])).
% 4.49/0.96  fof(f1183,plain,(
% 4.49/0.96    spl5_29 <=> r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 4.49/0.96  fof(f1198,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,sK1),sK1) | (~spl5_19 | spl5_29)),
% 4.49/0.96    inference(backward_demodulation,[],[f1184,f1110])).
% 4.49/0.96  fof(f1184,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1) | spl5_29),
% 4.49/0.96    inference(avatar_component_clause,[],[f1183])).
% 4.49/0.96  fof(f1191,plain,(
% 4.49/0.96    ~spl5_30 | spl5_20),
% 4.49/0.96    inference(avatar_split_clause,[],[f1180,f1112,f1188])).
% 4.49/0.96  fof(f1112,plain,(
% 4.49/0.96    spl5_20 <=> r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 4.49/0.96  fof(f1180,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK0)) | spl5_20),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1114,f41])).
% 4.49/0.96  fof(f1114,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)) | spl5_20),
% 4.49/0.96    inference(avatar_component_clause,[],[f1112])).
% 4.49/0.96  fof(f1186,plain,(
% 4.49/0.96    spl5_29 | spl5_20),
% 4.49/0.96    inference(avatar_split_clause,[],[f1181,f1112,f1183])).
% 4.49/0.96  fof(f1181,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)),sK1) | spl5_20),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1114,f40])).
% 4.49/0.96  fof(f1177,plain,(
% 4.49/0.96    ~spl5_28 | spl5_17),
% 4.49/0.96    inference(avatar_split_clause,[],[f1166,f1088,f1174])).
% 4.49/0.96  fof(f1174,plain,(
% 4.49/0.96    spl5_28 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 4.49/0.96  fof(f1088,plain,(
% 4.49/0.96    spl5_17 <=> r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 4.49/0.96  fof(f1166,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_17),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1090,f41])).
% 4.49/0.96  fof(f1090,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | spl5_17),
% 4.49/0.96    inference(avatar_component_clause,[],[f1088])).
% 4.49/0.96  fof(f1172,plain,(
% 4.49/0.96    spl5_27 | spl5_17),
% 4.49/0.96    inference(avatar_split_clause,[],[f1167,f1088,f1169])).
% 4.49/0.96  fof(f1169,plain,(
% 4.49/0.96    spl5_27 <=> r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 4.49/0.96  fof(f1167,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) | spl5_17),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1090,f40])).
% 4.49/0.96  fof(f1163,plain,(
% 4.49/0.96    spl5_25 | ~spl5_26 | ~spl5_14),
% 4.49/0.96    inference(avatar_split_clause,[],[f1149,f1064,f1160,f1156])).
% 4.49/0.96  fof(f1156,plain,(
% 4.49/0.96    spl5_25 <=> sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 4.49/0.96  fof(f1149,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | ~spl5_14),
% 4.49/0.96    inference(resolution,[],[f1066,f38])).
% 4.49/0.96  fof(f1154,plain,(
% 4.49/0.96    spl5_24 | ~spl5_14),
% 4.49/0.96    inference(avatar_split_clause,[],[f1146,f1064,f1151])).
% 4.49/0.96  fof(f1151,plain,(
% 4.49/0.96    spl5_24 <=> k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 4.49/0.96  fof(f1146,plain,(
% 4.49/0.96    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_14),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1066,f35])).
% 4.49/0.96  fof(f1139,plain,(
% 4.49/0.96    spl5_22 | ~spl5_23 | ~spl5_13),
% 4.49/0.96    inference(avatar_split_clause,[],[f1125,f1059,f1136,f1132])).
% 4.49/0.96  fof(f1132,plain,(
% 4.49/0.96    spl5_22 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 4.49/0.96  fof(f1125,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK2) | ~spl5_13),
% 4.49/0.96    inference(resolution,[],[f1061,f38])).
% 4.49/0.96  fof(f1130,plain,(
% 4.49/0.96    spl5_21 | ~spl5_13),
% 4.49/0.96    inference(avatar_split_clause,[],[f1122,f1059,f1127])).
% 4.49/0.96  fof(f1127,plain,(
% 4.49/0.96    spl5_21 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 4.49/0.96  fof(f1122,plain,(
% 4.49/0.96    k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | ~spl5_13),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1061,f35])).
% 4.49/0.96  fof(f1115,plain,(
% 4.49/0.96    spl5_19 | ~spl5_20 | ~spl5_12),
% 4.49/0.96    inference(avatar_split_clause,[],[f1101,f1054,f1112,f1108])).
% 4.49/0.96  fof(f1101,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK0)) | sK1 = k3_enumset1(sK2,sK2,sK2,sK2,sK0) | ~spl5_12),
% 4.49/0.96    inference(resolution,[],[f1056,f38])).
% 4.49/0.96  fof(f1106,plain,(
% 4.49/0.96    spl5_18 | ~spl5_12),
% 4.49/0.96    inference(avatar_split_clause,[],[f1098,f1054,f1103])).
% 4.49/0.96  fof(f1103,plain,(
% 4.49/0.96    spl5_18 <=> k3_enumset1(sK2,sK2,sK2,sK2,sK0) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 4.49/0.96  fof(f1098,plain,(
% 4.49/0.96    k3_enumset1(sK2,sK2,sK2,sK2,sK0) = k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) | ~spl5_12),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1056,f35])).
% 4.49/0.96  fof(f1091,plain,(
% 4.49/0.96    spl5_16 | ~spl5_17 | ~spl5_11),
% 4.49/0.96    inference(avatar_split_clause,[],[f1077,f1049,f1088,f1084])).
% 4.49/0.96  fof(f1084,plain,(
% 4.49/0.96    spl5_16 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 4.49/0.96  fof(f1077,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl5_11),
% 4.49/0.96    inference(resolution,[],[f1051,f38])).
% 4.49/0.96  fof(f1082,plain,(
% 4.49/0.96    spl5_15 | ~spl5_11),
% 4.49/0.96    inference(avatar_split_clause,[],[f1074,f1049,f1079])).
% 4.49/0.96  fof(f1079,plain,(
% 4.49/0.96    spl5_15 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 4.49/0.96  fof(f1074,plain,(
% 4.49/0.96    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_11),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f1051,f35])).
% 4.49/0.96  fof(f1067,plain,(
% 4.49/0.96    spl5_14 | ~spl5_2),
% 4.49/0.96    inference(avatar_split_clause,[],[f994,f83,f1064])).
% 4.49/0.96  fof(f994,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) | ~spl5_2),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f85,f69])).
% 4.49/0.96  fof(f1062,plain,(
% 4.49/0.96    spl5_13 | ~spl5_2 | ~spl5_3),
% 4.49/0.96    inference(avatar_split_clause,[],[f995,f88,f83,f1059])).
% 4.49/0.96  fof(f995,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) | (~spl5_2 | ~spl5_3)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f90,f85,f69])).
% 4.49/0.96  fof(f1057,plain,(
% 4.49/0.96    spl5_12 | ~spl5_2 | ~spl5_3),
% 4.49/0.96    inference(avatar_split_clause,[],[f1001,f88,f83,f1054])).
% 4.49/0.96  fof(f1001,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK0),sK1) | (~spl5_2 | ~spl5_3)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f90,f69])).
% 4.49/0.96  fof(f1052,plain,(
% 4.49/0.96    spl5_11 | ~spl5_3),
% 4.49/0.96    inference(avatar_split_clause,[],[f1002,f88,f1049])).
% 4.49/0.96  fof(f1002,plain,(
% 4.49/0.96    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | ~spl5_3),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f90,f90,f69])).
% 4.49/0.96  fof(f756,plain,(
% 4.49/0.96    spl5_10 | ~spl5_2 | spl5_4),
% 4.49/0.96    inference(avatar_split_clause,[],[f720,f137,f83,f753])).
% 4.49/0.96  fof(f753,plain,(
% 4.49/0.96    spl5_10 <=> r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 4.49/0.96  fof(f137,plain,(
% 4.49/0.96    spl5_4 <=> r2_hidden(sK2,k5_xboole_0(sK1,sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 4.49/0.96  fof(f720,plain,(
% 4.49/0.96    r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_2 | spl5_4)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f139,f74])).
% 4.49/0.96  fof(f139,plain,(
% 4.49/0.96    ~r2_hidden(sK2,k5_xboole_0(sK1,sK1)) | spl5_4),
% 4.49/0.96    inference(avatar_component_clause,[],[f137])).
% 4.49/0.96  fof(f751,plain,(
% 4.49/0.96    spl5_9 | ~spl5_6 | spl5_7),
% 4.49/0.96    inference(avatar_split_clause,[],[f724,f159,f154,f747])).
% 4.49/0.96  fof(f747,plain,(
% 4.49/0.96    spl5_9 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 4.49/0.96  fof(f159,plain,(
% 4.49/0.96    spl5_7 <=> r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 4.49/0.96  fof(f724,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_6 | spl5_7)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f156,f161,f74])).
% 4.49/0.96  fof(f161,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl5_7),
% 4.49/0.96    inference(avatar_component_clause,[],[f159])).
% 4.49/0.96  fof(f750,plain,(
% 4.49/0.96    spl5_9 | ~spl5_2 | spl5_7),
% 4.49/0.96    inference(avatar_split_clause,[],[f725,f159,f83,f747])).
% 4.49/0.96  fof(f725,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | (~spl5_2 | spl5_7)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f200,f161,f74])).
% 4.49/0.96  fof(f198,plain,(
% 4.49/0.96    ~spl5_8 | spl5_4),
% 4.49/0.96    inference(avatar_split_clause,[],[f192,f137,f195])).
% 4.49/0.96  fof(f195,plain,(
% 4.49/0.96    spl5_8 <=> r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 4.49/0.96  fof(f192,plain,(
% 4.49/0.96    ~r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) | spl5_4),
% 4.49/0.96    inference(backward_demodulation,[],[f168,f190])).
% 4.49/0.96  fof(f168,plain,(
% 4.49/0.96    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK1),X0))))) ) | spl5_4),
% 4.49/0.96    inference(forward_demodulation,[],[f164,f43])).
% 4.49/0.96  fof(f164,plain,(
% 4.49/0.96    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),X0)))) ) | spl5_4),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f139,f76])).
% 4.49/0.96  fof(f162,plain,(
% 4.49/0.96    ~spl5_7 | spl5_5),
% 4.49/0.96    inference(avatar_split_clause,[],[f151,f146,f159])).
% 4.49/0.96  fof(f146,plain,(
% 4.49/0.96    spl5_5 <=> r1_tarski(sK1,k5_xboole_0(sK1,sK1))),
% 4.49/0.96    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 4.49/0.96  fof(f151,plain,(
% 4.49/0.96    ~r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,sK1)) | spl5_5),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f148,f41])).
% 4.49/0.96  fof(f148,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | spl5_5),
% 4.49/0.96    inference(avatar_component_clause,[],[f146])).
% 4.49/0.96  fof(f157,plain,(
% 4.49/0.96    spl5_6 | spl5_5),
% 4.49/0.96    inference(avatar_split_clause,[],[f152,f146,f154])).
% 4.49/0.96  fof(f152,plain,(
% 4.49/0.96    r2_hidden(sK3(sK1,k5_xboole_0(sK1,sK1)),sK1) | spl5_5),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f148,f40])).
% 4.49/0.96  fof(f150,plain,(
% 4.49/0.96    ~spl5_5 | ~spl5_2 | spl5_4),
% 4.49/0.96    inference(avatar_split_clause,[],[f141,f137,f83,f146])).
% 4.49/0.96  fof(f141,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl5_2 | spl5_4)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f139,f99])).
% 4.49/0.96  fof(f149,plain,(
% 4.49/0.96    ~spl5_5 | ~spl5_2 | spl5_4),
% 4.49/0.96    inference(avatar_split_clause,[],[f142,f137,f83,f146])).
% 4.49/0.96  fof(f142,plain,(
% 4.49/0.96    ~r1_tarski(sK1,k5_xboole_0(sK1,sK1)) | (~spl5_2 | spl5_4)),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f139,f39])).
% 4.49/0.96  fof(f140,plain,(
% 4.49/0.96    ~spl5_4 | ~spl5_2),
% 4.49/0.96    inference(avatar_split_clause,[],[f135,f83,f137])).
% 4.49/0.96  fof(f135,plain,(
% 4.49/0.96    ~r2_hidden(sK2,k5_xboole_0(sK1,sK1)) | ~spl5_2),
% 4.49/0.96    inference(superposition,[],[f123,f92])).
% 4.49/0.96  fof(f123,plain,(
% 4.49/0.96    ( ! [X0] : (~r2_hidden(sK2,k5_xboole_0(X0,k3_xboole_0(X0,sK1)))) ) | ~spl5_2),
% 4.49/0.96    inference(unit_resulting_resolution,[],[f85,f75])).
% 4.49/0.96  fof(f91,plain,(
% 4.49/0.96    spl5_3),
% 4.49/0.96    inference(avatar_split_clause,[],[f24,f88])).
% 4.49/0.96  fof(f24,plain,(
% 4.49/0.96    r2_hidden(sK0,sK1)),
% 4.49/0.96    inference(cnf_transformation,[],[f21])).
% 4.49/0.96  fof(f21,plain,(
% 4.49/0.96    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 4.49/0.96    inference(flattening,[],[f20])).
% 4.49/0.96  fof(f20,plain,(
% 4.49/0.96    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 4.49/0.96    inference(ennf_transformation,[],[f18])).
% 4.49/0.96  fof(f18,negated_conjecture,(
% 4.49/0.96    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 4.49/0.96    inference(negated_conjecture,[],[f17])).
% 4.49/0.97  fof(f17,conjecture,(
% 4.49/0.97    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 4.49/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 4.49/0.97  fof(f86,plain,(
% 4.49/0.97    spl5_2),
% 4.49/0.97    inference(avatar_split_clause,[],[f25,f83])).
% 4.49/0.97  fof(f25,plain,(
% 4.49/0.97    r2_hidden(sK2,sK1)),
% 4.49/0.97    inference(cnf_transformation,[],[f21])).
% 4.49/0.97  fof(f81,plain,(
% 4.49/0.97    ~spl5_1),
% 4.49/0.97    inference(avatar_split_clause,[],[f57,f78])).
% 4.49/0.97  fof(f57,plain,(
% 4.49/0.97    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1))),
% 4.49/0.97    inference(definition_unfolding,[],[f26,f56,f55])).
% 4.49/0.97  fof(f26,plain,(
% 4.49/0.97    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 4.49/0.97    inference(cnf_transformation,[],[f21])).
% 4.49/0.97  % SZS output end Proof for theBenchmark
% 4.49/0.97  % (11130)------------------------------
% 4.49/0.97  % (11130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/0.97  % (11130)Termination reason: Refutation
% 4.49/0.97  
% 4.49/0.97  % (11130)Memory used [KB]: 4093
% 4.49/0.97  % (11130)Time elapsed: 0.479 s
% 4.49/0.97  % (11130)------------------------------
% 4.49/0.97  % (11130)------------------------------
% 4.49/0.97  % (11115)Success in time 0.593 s
%------------------------------------------------------------------------------

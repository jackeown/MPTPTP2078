%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:22 EST 2020

% Result     : Theorem 6.40s
% Output     : Refutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :  648 (6600 expanded)
%              Number of leaves         :  110 (2264 expanded)
%              Depth                    :   13
%              Number of atoms          : 1899 (14744 expanded)
%              Number of equality atoms :  157 (2219 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f78,f82,f93,f94,f114,f119,f124,f125,f126,f127,f136,f137,f153,f158,f159,f161,f170,f171,f200,f289,f290,f298,f500,f501,f621,f622,f655,f848,f849,f865,f870,f875,f878,f879,f888,f889,f922,f923,f987,f988,f1068,f1073,f1074,f1083,f1088,f1107,f1112,f1143,f1148,f1268,f1273,f1390,f1395,f1400,f1418,f2420,f2425,f2498,f2503,f2505,f2506,f2508,f2510,f2519,f2520,f2743,f2747,f2839,f2844,f2845,f2850,f2852,f2853,f2854,f2859,f2860,f2861,f2862,f2863,f2868,f2873,f2875,f2881,f3185,f3209,f3305,f3345,f3771,f4203,f6315,f6316,f6317,f6318,f6332,f6333,f6358,f6359,f6360,f6361,f6362,f6367,f6505,f6551,f6552,f6701,f6702,f6763,f6764,f6765,f6766,f6767,f6772,f7115,f7120,f7378,f7383,f7388,f7393,f7398,f7399,f7400,f7404,f7406,f7407,f7412,f7413,f7422,f7424,f7425,f7426,f7427,f7428,f7429,f7430,f7431,f7432,f7433,f7434,f7435,f7440,f7441,f7442,f7443,f7448,f7449,f7450,f7451,f7457,f7466,f7469,f7478,f7479,f7480,f7481,f7484,f7493,f7494,f7883,f7884,f7888,f7889,f8062,f8067,f8101,f8109,f8115,f8148,f8153,f8158,f8172,f8173,f8202])).

fof(f8202,plain,(
    spl3_98 ),
    inference(avatar_contradiction_clause,[],[f8197])).

fof(f8197,plain,
    ( $false
    | spl3_98 ),
    inference(unit_resulting_resolution,[],[f45,f8171,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f8171,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl3_98 ),
    inference(avatar_component_clause,[],[f8169])).

fof(f8169,plain,
    ( spl3_98
  <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f8173,plain,
    ( ~ spl3_98
    | spl3_95 ),
    inference(avatar_split_clause,[],[f8166,f8145,f8169])).

fof(f8145,plain,
    ( spl3_95
  <=> r1_tarski(k4_xboole_0(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f8166,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl3_95 ),
    inference(resolution,[],[f8147,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f8147,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK1)
    | spl3_95 ),
    inference(avatar_component_clause,[],[f8145])).

fof(f8172,plain,
    ( ~ spl3_98
    | spl3_95 ),
    inference(avatar_split_clause,[],[f8163,f8145,f8169])).

fof(f8163,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl3_95 ),
    inference(unit_resulting_resolution,[],[f8147,f34])).

fof(f8158,plain,
    ( spl3_97
    | ~ spl3_90
    | ~ spl3_94 ),
    inference(avatar_split_clause,[],[f8141,f8112,f8059,f8155])).

fof(f8155,plain,
    ( spl3_97
  <=> k4_xboole_0(sK0,sK0) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f8059,plain,
    ( spl3_90
  <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f8112,plain,
    ( spl3_94
  <=> k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f8141,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_90
    | ~ spl3_94 ),
    inference(backward_demodulation,[],[f8061,f8114])).

fof(f8114,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)
    | ~ spl3_94 ),
    inference(avatar_component_clause,[],[f8112])).

fof(f8061,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f8059])).

fof(f8153,plain,
    ( ~ spl3_96
    | spl3_71
    | ~ spl3_94 ),
    inference(avatar_split_clause,[],[f8131,f8112,f6548,f8150])).

fof(f8150,plain,
    ( spl3_96
  <=> r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f6548,plain,
    ( spl3_71
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f8131,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_71
    | ~ spl3_94 ),
    inference(backward_demodulation,[],[f6550,f8114])).

fof(f6550,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_71 ),
    inference(avatar_component_clause,[],[f6548])).

fof(f8148,plain,
    ( ~ spl3_95
    | spl3_67
    | ~ spl3_94 ),
    inference(avatar_split_clause,[],[f8123,f8112,f6312,f8145])).

fof(f6312,plain,
    ( spl3_67
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f8123,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK0),sK1)
    | spl3_67
    | ~ spl3_94 ),
    inference(backward_demodulation,[],[f6314,f8114])).

fof(f6314,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl3_67 ),
    inference(avatar_component_clause,[],[f6312])).

fof(f8115,plain,
    ( spl3_94
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(avatar_split_clause,[],[f8110,f8064,f3182,f8112])).

fof(f3182,plain,
    ( spl3_61
  <=> k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f8064,plain,
    ( spl3_91
  <=> k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f8110,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)
    | ~ spl3_61
    | ~ spl3_91 ),
    inference(backward_demodulation,[],[f3184,f8066])).

fof(f8066,plain,
    ( k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_91 ),
    inference(avatar_component_clause,[],[f8064])).

fof(f3184,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f3182])).

fof(f8109,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_93
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f8105,f3182,f116,f76,f8107,f67,f62])).

fof(f62,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f8107,plain,
    ( spl3_93
  <=> ! [X90] :
        ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X90,X90)
        | ~ r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f76,plain,
    ( spl3_6
  <=> ! [X1,X0] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f116,plain,
    ( spl3_10
  <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f8105,plain,
    ( ! [X90] :
        ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X90,X90)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f8050,f3184])).

fof(f8050,plain,
    ( ! [X90] :
        ( k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(X90,X90)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2)) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f31,f6877])).

fof(f6877,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(X0,X0))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f6826,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f6826,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X0,X0)),X1)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f44,f1192])).

fof(f1192,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,X4),X7),k2_xboole_0(k10_relat_1(sK2,X5),X6))
        | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X4,X5)),X6) )
    | ~ spl3_6 ),
    inference(resolution,[],[f430,f33])).

fof(f430,plain,
    ( ! [X10,X8,X9] :
        ( ~ r1_tarski(k10_relat_1(sK2,X8),k2_xboole_0(k10_relat_1(sK2,X9),X10))
        | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X8,X9)),X10) )
    | ~ spl3_6 ),
    inference(superposition,[],[f34,f77])).

fof(f77,plain,
    ( ! [X0,X1] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f562,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,k2_relat_1(sK2)),X0)
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f552,f34])).

fof(f552,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f44,f252])).

fof(f252,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X3),X2)
        | r1_tarski(sK0,X2) )
    | ~ spl3_10 ),
    inference(resolution,[],[f194,f33])).

fof(f194,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X1)
        | r1_tarski(sK0,X1) )
    | ~ spl3_10 ),
    inference(superposition,[],[f33,f118])).

fof(f118,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f8101,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_92
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f8097,f2865,f116,f76,f8099,f67,f62])).

fof(f8099,plain,
    ( spl3_92
  <=> ! [X86,X87] : k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(X86,X86))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f2865,plain,
    ( spl3_60
  <=> k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f8097,plain,
    ( ! [X87,X86] :
        ( k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(X86,X86)))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f8096,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f8096,plain,
    ( ! [X87,X86] :
        ( k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1)))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f8095,f3161])).

fof(f3161,plain,
    ( ! [X5] : k10_relat_1(sK2,k4_xboole_0(X5,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k10_relat_1(sK2,X5),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_60 ),
    inference(superposition,[],[f77,f2867])).

fof(f2867,plain,
    ( k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f2865])).

fof(f8095,plain,
    ( ! [X87,X86] :
        ( k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k4_xboole_0(k10_relat_1(sK2,X87),k4_xboole_0(sK0,k2_relat_1(sK2)))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f8048,f43])).

fof(f8048,plain,
    ( ! [X87,X86] :
        ( k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k6_subset_1(k10_relat_1(sK2,X87),k4_xboole_0(sK0,k2_relat_1(sK2)))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f42,f6877])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f8067,plain,
    ( spl3_91
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f8011,f116,f76,f67,f62,f52,f8064])).

fof(f52,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f8011,plain,
    ( k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f177,f6877])).

fof(f177,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,X0)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f69,f103,f31])).

fof(f103,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f54,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f69,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f8062,plain,
    ( spl3_90
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f8057,f3182,f116,f76,f67,f62,f8059])).

fof(f8057,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f8010,f3184])).

fof(f8010,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f86,f6877])).

fof(f86,plain,
    ( ! [X0] : k4_xboole_0(k2_relat_1(sK2),X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k2_relat_1(sK2),X0)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f41,f69,f31])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f7889,plain,
    ( spl3_89
    | ~ spl3_88
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f7872,f150,f52,f7880,f7886])).

fof(f7886,plain,
    ( spl3_89
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f7880,plain,
    ( spl3_88
  <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f150,plain,
    ( spl3_14
  <=> k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f7872,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
        | r1_tarski(k4_xboole_0(sK0,X2),k10_relat_1(sK2,sK1)) )
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f1315,f323])).

fof(f323,plain,
    ( ! [X0,X1] : k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k4_xboole_0(sK0,X0),X1)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f180,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f180,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f103,f35])).

fof(f1315,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(X2,k10_relat_1(sK2,sK0)),X3),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
        | r1_tarski(X2,k10_relat_1(sK2,sK1)) )
    | ~ spl3_14 ),
    inference(resolution,[],[f491,f33])).

fof(f491,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k4_xboole_0(X2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
        | r1_tarski(X2,k10_relat_1(sK2,sK1)) )
    | ~ spl3_14 ),
    inference(superposition,[],[f32,f152])).

fof(f152,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f7888,plain,
    ( spl3_89
    | ~ spl3_88
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f7870,f150,f52,f7880,f7886])).

fof(f7870,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
        | r1_tarski(k4_xboole_0(sK0,X0),k10_relat_1(sK2,sK1)) )
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f1315,f322])).

fof(f322,plain,
    ( ! [X0,X1] : k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f180,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f7884,plain,
    ( spl3_87
    | ~ spl3_88
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f7867,f150,f52,f7880,f7876])).

fof(f7876,plain,
    ( spl3_87
  <=> r1_tarski(sK0,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f7867,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | r1_tarski(sK0,k10_relat_1(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f1315,f179])).

fof(f179,plain,
    ( ! [X0] : k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,X0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f103,f39])).

fof(f7883,plain,
    ( spl3_87
    | ~ spl3_88
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f7866,f150,f52,f7880,f7876])).

fof(f7866,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | r1_tarski(sK0,k10_relat_1(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f1315,f178])).

fof(f178,plain,
    ( ! [X0] : k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(sK0,X0),k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f103,f40])).

fof(f7494,plain,
    ( ~ spl3_77
    | ~ spl3_6
    | ~ spl3_10
    | spl3_67 ),
    inference(avatar_split_clause,[],[f7373,f6312,f116,f76,f7375])).

fof(f7375,plain,
    ( spl3_77
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f7373,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_67 ),
    inference(resolution,[],[f7206,f6421])).

fof(f6421,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0) )
    | spl3_67 ),
    inference(superposition,[],[f6324,f39])).

fof(f6324,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK1)
    | spl3_67 ),
    inference(unit_resulting_resolution,[],[f6314,f33])).

fof(f7206,plain,
    ( ! [X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X1)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f7054,f6877])).

fof(f7054,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X0))),X1)
    | ~ spl3_6 ),
    inference(superposition,[],[f6826,f77])).

fof(f7493,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7372,f116,f76,f47,f7380])).

fof(f7380,plain,
    ( spl3_78
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f47,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f7372,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f7206,f6302])).

fof(f6302,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,X3),sK1) )
    | spl3_1 ),
    inference(resolution,[],[f1374,f45])).

fof(f1374,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,X2),X3)
        | ~ r1_tarski(X2,X3) )
    | spl3_1 ),
    inference(superposition,[],[f210,f40])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,X0),X1) )
    | spl3_1 ),
    inference(resolution,[],[f174,f32])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_1 ),
    inference(superposition,[],[f98,f39])).

fof(f98,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f49,f33])).

fof(f49,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f7484,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f7343,f6329,f116,f76,f7409])).

fof(f7409,plain,
    ( spl3_82
  <=> r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f6329,plain,
    ( spl3_68
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f7343,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_68 ),
    inference(resolution,[],[f7206,f6451])).

fof(f6451,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_xboole_0(sK1,sK1))
        | ~ r1_tarski(sK0,X2) )
    | spl3_68 ),
    inference(superposition,[],[f6350,f39])).

fof(f6350,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k2_xboole_0(sK1,sK1))
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f6331,f33])).

fof(f6331,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | spl3_68 ),
    inference(avatar_component_clause,[],[f6329])).

fof(f7481,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7336,f116,f76,f47,f7380])).

fof(f7336,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f7206,f1412])).

fof(f1412,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k4_xboole_0(sK0,X1))
        | ~ r1_tarski(k4_xboole_0(sK0,X1),sK1) )
    | spl3_1 ),
    inference(superposition,[],[f1367,f40])).

fof(f1367,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f210])).

fof(f7480,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(avatar_split_clause,[],[f7334,f872,f116,f76,f7409])).

fof(f872,plain,
    ( spl3_29
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f7334,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(resolution,[],[f7206,f1362])).

fof(f1362,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k4_xboole_0(k4_xboole_0(sK0,sK0),X3))
        | ~ r1_tarski(sK0,X2) )
    | spl3_29 ),
    inference(superposition,[],[f966,f39])).

fof(f966,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,sK0),X1))
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f939,f33])).

fof(f939,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK0,sK0),X0))
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f41,f898])).

fof(f898,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,k4_xboole_0(sK0,sK0)) )
    | spl3_29 ),
    inference(superposition,[],[f892,f39])).

fof(f892,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0))
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f874,f33])).

fof(f874,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK0))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f872])).

fof(f7479,plain,
    ( ~ spl3_82
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7333,f116,f76,f47,f7409])).

fof(f7333,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f7206,f1235])).

fof(f1235,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k4_xboole_0(k4_xboole_0(sK1,X5),X6))
        | ~ r1_tarski(sK0,X4) )
    | spl3_1 ),
    inference(superposition,[],[f456,f39])).

fof(f456,plain,
    ( ! [X2,X0,X1] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,X1),X2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f447,f33])).

fof(f447,plain,
    ( ! [X0,X1] : ~ r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f271])).

fof(f271,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_tarski(X1,k4_xboole_0(sK1,X2)) )
    | spl3_1 ),
    inference(superposition,[],[f214,f39])).

fof(f214,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK1,X1))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f205,f33])).

fof(f205,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(sK1,X0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f174])).

fof(f7478,plain,
    ( ~ spl3_82
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_split_clause,[],[f7332,f282,f116,f111,f76,f52,f7409])).

fof(f111,plain,
    ( spl3_9
  <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f282,plain,
    ( spl3_19
  <=> r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f7332,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_19 ),
    inference(resolution,[],[f7206,f1575])).

fof(f1575,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k4_xboole_0(k4_xboole_0(sK0,X3),sK0))
        | ~ r1_tarski(sK0,X2) )
    | ~ spl3_2
    | ~ spl3_9
    | spl3_19 ),
    inference(superposition,[],[f1569,f39])).

fof(f1569,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X1),sK0))
    | ~ spl3_2
    | ~ spl3_9
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f1554,f33])).

fof(f1554,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),sK0))
    | ~ spl3_2
    | ~ spl3_9
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f827,f392])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,k4_xboole_0(k2_relat_1(sK2),sK0)) )
    | spl3_19 ),
    inference(superposition,[],[f292,f39])).

fof(f292,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f284,f33])).

fof(f284,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f282])).

fof(f827,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f103,f278])).

fof(f278,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_relat_1(sK2))
        | r1_tarski(k4_xboole_0(X2,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) )
    | ~ spl3_9 ),
    inference(superposition,[],[f34,f113])).

fof(f113,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f7469,plain,
    ( spl3_86
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7219,f116,f76,f7454])).

fof(f7454,plain,
    ( spl3_86
  <=> k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f7219,plain,
    ( k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f7206,f38])).

fof(f7466,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7462,f116,f76,f47,f7390])).

fof(f7390,plain,
    ( spl3_80
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f7462,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f7309,f7226])).

fof(f7226,plain,
    ( ! [X0] : k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X0)
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f7206,f38])).

fof(f7309,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X0)),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f7206,f1374])).

fof(f7457,plain,
    ( spl3_86
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7227,f116,f76,f7454])).

fof(f7227,plain,
    ( k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f7206,f38])).

fof(f7451,plain,
    ( ~ spl3_79
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7231,f116,f76,f47,f7385])).

fof(f7385,plain,
    ( spl3_79
  <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f7231,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f49,f7206,f557])).

fof(f557,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r1_tarski(sK0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(superposition,[],[f252,f39])).

fof(f7450,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7233,f116,f76,f47,f7380])).

fof(f7233,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).

fof(f7449,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7234,f116,f76,f47,f7380])).

fof(f7234,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).

fof(f7448,plain,
    ( ~ spl3_85
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7236,f116,f76,f47,f7445])).

fof(f7445,plain,
    ( spl3_85
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f7236,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).

fof(f7443,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7237,f116,f76,f47,f7390])).

fof(f7237,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f7206,f1374])).

fof(f7442,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7239,f116,f76,f47,f7380])).

fof(f7239,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).

fof(f7441,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7240,f116,f76,f47,f7380])).

fof(f7240,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).

fof(f7440,plain,
    ( ~ spl3_84
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7241,f116,f76,f47,f7437])).

fof(f7437,plain,
    ( spl3_84
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f7241,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f1741,f7206,f1374])).

fof(f1741,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),X0))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f1725,f34])).

fof(f1725,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(k2_relat_1(sK2),X0)))
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f44,f251])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),X1)
        | r1_tarski(sK0,k2_xboole_0(X0,X1)) )
    | ~ spl3_10 ),
    inference(resolution,[],[f194,f32])).

fof(f7435,plain,
    ( ~ spl3_82
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_split_clause,[],[f7251,f282,f116,f111,f76,f52,f7409])).

fof(f7251,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f7206,f1575])).

fof(f7434,plain,
    ( ~ spl3_82
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7252,f116,f76,f47,f7409])).

fof(f7252,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f1235])).

fof(f7433,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(avatar_split_clause,[],[f7253,f872,f116,f76,f7409])).

fof(f7253,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f7206,f1362])).

fof(f7432,plain,
    ( ~ spl3_79
    | ~ spl3_6
    | ~ spl3_10
    | spl3_21 ),
    inference(avatar_split_clause,[],[f7254,f295,f116,f76,f7385])).

fof(f295,plain,
    ( spl3_21
  <=> r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f7254,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f7206,f793])).

fof(f793,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(X0,k4_xboole_0(k2_relat_1(sK2),sK0)) )
    | spl3_21 ),
    inference(superposition,[],[f299,f39])).

fof(f299,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f297,f33])).

fof(f297,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f295])).

fof(f7431,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_split_clause,[],[f7256,f282,f116,f76,f7409])).

fof(f7256,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f7206,f392])).

fof(f7430,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7257,f116,f76,f47,f7380])).

fof(f7257,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f1412])).

fof(f7429,plain,
    ( ~ spl3_79
    | ~ spl3_6
    | ~ spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f7259,f133,f116,f76,f7385])).

fof(f133,plain,
    ( spl3_13
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f7259,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f7206,f438])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(X0,k4_xboole_0(sK0,X1)) )
    | spl3_13 ),
    inference(superposition,[],[f266,f39])).

fof(f266,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(sK0,X1))
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f259,f33])).

fof(f259,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK2),k4_xboole_0(sK0,X0))
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f41,f190])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(X0,sK0) )
    | spl3_13 ),
    inference(superposition,[],[f138,f39])).

fof(f138,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),sK0)
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f135,f33])).

fof(f135,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f7428,plain,
    ( ~ spl3_82
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7260,f116,f76,f47,f7409])).

fof(f7260,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f675])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,k4_xboole_0(sK0,k2_relat_1(sK2))) )
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f604,f39])).

fof(f604,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f211])).

fof(f211,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(k2_xboole_0(sK0,X3),X2) )
    | spl3_1 ),
    inference(resolution,[],[f174,f33])).

fof(f7427,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(avatar_split_clause,[],[f7262,f872,f116,f76,f7409])).

fof(f7262,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f7206,f898])).

fof(f7426,plain,
    ( ~ spl3_79
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7266,f116,f76,f47,f7385])).

fof(f7266,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f434])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(X0,k4_xboole_0(sK1,X1)) )
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f255,f39])).

fof(f255,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(sK1,X1))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f248,f33])).

fof(f248,plain,
    ( ! [X0] : ~ r1_tarski(k2_relat_1(sK2),k4_xboole_0(sK1,X0))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f205,f194])).

fof(f7425,plain,
    ( ~ spl3_82
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7267,f116,f76,f47,f7409])).

fof(f7267,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f271])).

fof(f7424,plain,
    ( ~ spl3_82
    | ~ spl3_6
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f7271,f6329,f116,f76,f7409])).

fof(f7271,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f7206,f6451])).

fof(f7422,plain,
    ( spl3_83
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7277,f116,f111,f76,f7419])).

fof(f7419,plain,
    ( spl3_83
  <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f7277,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f278])).

fof(f7413,plain,
    ( ~ spl3_79
    | ~ spl3_6
    | ~ spl3_10
    | spl3_13 ),
    inference(avatar_split_clause,[],[f7290,f133,f116,f76,f7385])).

fof(f7290,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f7206,f190])).

fof(f7412,plain,
    ( ~ spl3_82
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7297,f116,f76,f47,f7409])).

fof(f7297,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f174])).

fof(f7407,plain,
    ( ~ spl3_79
    | ~ spl3_6
    | ~ spl3_10
    | spl3_18 ),
    inference(avatar_split_clause,[],[f7299,f197,f116,f76,f7385])).

fof(f197,plain,
    ( spl3_18
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f7299,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f7206,f232])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_18 ),
    inference(superposition,[],[f201,f39])).

fof(f201,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),sK1)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f199,f33])).

fof(f199,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f7406,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7405,f116,f76,f47,f7390])).

fof(f7405,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f7304,f596])).

fof(f596,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_relat_1(sK2)) = k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0)
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f562,f38])).

fof(f7304,plain,
    ( ! [X0] : ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f427,f7206,f1374])).

fof(f427,plain,
    ( ! [X2,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,X2)),k10_relat_1(sK2,X1))
    | ~ spl3_6 ),
    inference(superposition,[],[f41,f77])).

fof(f7404,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7403,f116,f76,f47,f7390])).

fof(f7403,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f7402,f596])).

fof(f7402,plain,
    ( ! [X1] : ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X1))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f7305,f596])).

fof(f7305,plain,
    ( ! [X0,X1] : ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0),X1))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f955,f7206,f1374])).

fof(f955,plain,
    ( ! [X2,X0,X1] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,X1),X2)),k10_relat_1(sK2,X0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f427,f429])).

fof(f429,plain,
    ( ! [X6,X7,X5] :
        ( ~ r1_tarski(k10_relat_1(sK2,X5),X7)
        | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X5,X6)),X7) )
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f77])).

fof(f7400,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7307,f116,f76,f47,f7390])).

fof(f7307,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).

fof(f7399,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7308,f116,f76,f47,f7390])).

fof(f7308,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).

fof(f7398,plain,
    ( ~ spl3_81
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7310,f116,f76,f47,f7395])).

fof(f7395,plain,
    ( spl3_81
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f7310,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).

fof(f7393,plain,
    ( ~ spl3_80
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7311,f116,f76,f47,f7390])).

fof(f7311,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f7206,f1374])).

fof(f7388,plain,
    ( ~ spl3_79
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7312,f116,f76,f47,f7385])).

fof(f7312,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).

fof(f7383,plain,
    ( ~ spl3_78
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f7320,f116,f76,f47,f7380])).

fof(f7320,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f7206,f6302])).

fof(f7378,plain,
    ( ~ spl3_77
    | ~ spl3_6
    | ~ spl3_10
    | spl3_67 ),
    inference(avatar_split_clause,[],[f7321,f6312,f116,f76,f7375])).

fof(f7321,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_67 ),
    inference(unit_resulting_resolution,[],[f7206,f6421])).

fof(f7120,plain,
    ( ~ spl3_76
    | ~ spl3_6
    | ~ spl3_10
    | spl3_54 ),
    inference(avatar_split_clause,[],[f7101,f2516,f116,f76,f7117])).

fof(f7117,plain,
    ( spl3_76
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f2516,plain,
    ( spl3_54
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f7101,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_10
    | spl3_54 ),
    inference(backward_demodulation,[],[f2518,f6877])).

fof(f2518,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f7115,plain,
    ( spl3_75
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f7099,f2495,f116,f76,f7112])).

fof(f7112,plain,
    ( spl3_75
  <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f2495,plain,
    ( spl3_51
  <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f7099,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_51 ),
    inference(backward_demodulation,[],[f2497,f6877])).

fof(f2497,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f6772,plain,
    ( ~ spl3_74
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6740,f6698,f116,f6769])).

fof(f6769,plain,
    ( spl3_74
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f6698,plain,
    ( spl3_72
  <=> r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f6740,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f6700,f251])).

fof(f6700,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_72 ),
    inference(avatar_component_clause,[],[f6698])).

fof(f6767,plain,
    ( ~ spl3_73
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6743,f6698,f116,f6760])).

fof(f6760,plain,
    ( spl3_73
  <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f6743,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f45,f6700,f557])).

fof(f6766,plain,
    ( ~ spl3_73
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6744,f6698,f116,f6760])).

fof(f6744,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f44,f6700,f557])).

fof(f6765,plain,
    ( ~ spl3_73
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6747,f6698,f116,f6760])).

fof(f6747,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f45,f6700,f557])).

fof(f6764,plain,
    ( ~ spl3_73
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6748,f6698,f116,f6760])).

fof(f6748,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f44,f6700,f557])).

fof(f6763,plain,
    ( ~ spl3_73
    | ~ spl3_10
    | spl3_72 ),
    inference(avatar_split_clause,[],[f6753,f6698,f116,f6760])).

fof(f6753,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | ~ spl3_10
    | spl3_72 ),
    inference(unit_resulting_resolution,[],[f6700,f194])).

fof(f6702,plain,
    ( ~ spl3_72
    | spl3_71 ),
    inference(avatar_split_clause,[],[f6695,f6548,f6698])).

fof(f6695,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_71 ),
    inference(resolution,[],[f6550,f34])).

fof(f6701,plain,
    ( ~ spl3_72
    | spl3_71 ),
    inference(avatar_split_clause,[],[f6692,f6548,f6698])).

fof(f6692,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))
    | spl3_71 ),
    inference(unit_resulting_resolution,[],[f6550,f34])).

fof(f6552,plain,
    ( ~ spl3_71
    | ~ spl3_10
    | spl3_67 ),
    inference(avatar_split_clause,[],[f6546,f6312,f116,f6548])).

fof(f6546,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_10
    | spl3_67 ),
    inference(resolution,[],[f6421,f562])).

fof(f6551,plain,
    ( ~ spl3_71
    | ~ spl3_10
    | spl3_67 ),
    inference(avatar_split_clause,[],[f6526,f6312,f116,f6548])).

fof(f6526,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_10
    | spl3_67 ),
    inference(unit_resulting_resolution,[],[f562,f6421])).

fof(f6505,plain,
    ( spl3_34
    | spl3_66
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f6500,f80,f57,f4201,f1062])).

fof(f1062,plain,
    ( spl3_34
  <=> ! [X7] : k4_xboole_0(k10_relat_1(sK2,sK0),X7) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f4201,plain,
    ( spl3_66
  <=> ! [X12] : ~ r1_tarski(k2_xboole_0(X12,k10_relat_1(sK2,sK1)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f57,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_7
  <=> ! [X2] :
        ( ~ r1_tarski(X2,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f6500,plain,
    ( ! [X39,X40] :
        ( ~ r1_tarski(k2_xboole_0(X39,k10_relat_1(sK2,sK1)),k2_relat_1(sK2))
        | k4_xboole_0(k10_relat_1(sK2,sK0),X40) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X40))) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f1160,f503])).

fof(f503,plain,
    ( ! [X0] : k2_xboole_0(X0,k10_relat_1(sK2,sK1)) = k2_xboole_0(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f310,f40])).

fof(f310,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f142,f32])).

fof(f142,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f59,f35])).

fof(f59,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1160,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_relat_1(sK2))
        | k4_xboole_0(X0,X1) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X1))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f358,f33])).

fof(f358,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,k2_relat_1(sK2))
        | k4_xboole_0(X2,X3) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X2,X3))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f81,f35])).

fof(f81,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f6367,plain,
    ( ~ spl3_70
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6335,f6329,f116,f6364])).

fof(f6364,plain,
    ( spl3_70
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f6335,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),sK1)
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f6331,f251])).

fof(f6362,plain,
    ( ~ spl3_69
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6338,f6329,f116,f6355])).

fof(f6355,plain,
    ( spl3_69
  <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f6338,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f45,f6331,f557])).

fof(f6361,plain,
    ( ~ spl3_69
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6339,f6329,f116,f6355])).

fof(f6339,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f44,f6331,f557])).

fof(f6360,plain,
    ( ~ spl3_69
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6342,f6329,f116,f6355])).

fof(f6342,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f45,f6331,f557])).

fof(f6359,plain,
    ( ~ spl3_69
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6343,f6329,f116,f6355])).

fof(f6343,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f44,f6331,f557])).

fof(f6358,plain,
    ( ~ spl3_69
    | ~ spl3_10
    | spl3_68 ),
    inference(avatar_split_clause,[],[f6348,f6329,f116,f6355])).

fof(f6348,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))
    | ~ spl3_10
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f6331,f194])).

fof(f6333,plain,
    ( ~ spl3_68
    | spl3_67 ),
    inference(avatar_split_clause,[],[f6326,f6312,f6329])).

fof(f6326,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | spl3_67 ),
    inference(resolution,[],[f6314,f34])).

fof(f6332,plain,
    ( ~ spl3_68
    | spl3_67 ),
    inference(avatar_split_clause,[],[f6323,f6312,f6329])).

fof(f6323,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK1))
    | spl3_67 ),
    inference(unit_resulting_resolution,[],[f6314,f34])).

fof(f6318,plain,
    ( ~ spl3_67
    | spl3_1 ),
    inference(avatar_split_clause,[],[f6078,f47,f6312])).

fof(f6078,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f45,f45,f1374])).

fof(f6317,plain,
    ( ~ spl3_67
    | spl3_1 ),
    inference(avatar_split_clause,[],[f6079,f47,f6312])).

fof(f6079,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f45,f1374])).

fof(f6316,plain,
    ( ~ spl3_67
    | spl3_1 ),
    inference(avatar_split_clause,[],[f6082,f47,f6312])).

fof(f6082,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f45,f44,f1374])).

fof(f6315,plain,
    ( ~ spl3_67
    | spl3_1 ),
    inference(avatar_split_clause,[],[f6083,f47,f6312])).

fof(f6083,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f44,f1374])).

fof(f4203,plain,
    ( spl3_36
    | spl3_66
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f4196,f80,f57,f4201,f1070])).

fof(f1070,plain,
    ( spl3_36
  <=> k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f4196,plain,
    ( ! [X12] :
        ( ~ r1_tarski(k2_xboole_0(X12,k10_relat_1(sK2,sK1)),k2_relat_1(sK2))
        | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0))) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f355,f503])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f81,f33])).

fof(f3771,plain,
    ( ~ spl3_65
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f3766,f116,f47,f3768])).

fof(f3768,plain,
    ( spl3_65
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f3766,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f2701,f588])).

fof(f588,plain,
    ( ! [X0] : k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0) = X0
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f40])).

fof(f2701,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f1520])).

fof(f1520,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),X1) )
    | spl3_1 ),
    inference(superposition,[],[f1409,f39])).

fof(f1409,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),X1),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f1367,f33])).

fof(f3345,plain,
    ( spl3_64
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f3335,f984,f76,f3342])).

fof(f3342,plain,
    ( spl3_64
  <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k2_xboole_0(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f984,plain,
    ( spl3_33
  <=> k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3335,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_xboole_0(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl3_6
    | ~ spl3_33 ),
    inference(superposition,[],[f524,f986])).

fof(f986,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f984])).

fof(f524,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,X0) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(X0,X1)),k10_relat_1(sK2,X0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f427,f40])).

fof(f3305,plain,
    ( spl3_63
    | ~ spl3_6
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f3293,f2865,f76,f3302])).

fof(f3302,plain,
    ( spl3_63
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k10_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f3293,plain,
    ( r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | ~ spl3_6
    | ~ spl3_60 ),
    inference(superposition,[],[f532,f2867])).

fof(f532,plain,
    ( ! [X0,X1] : r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X1))),k10_relat_1(sK2,k10_relat_1(sK2,X0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f427,f77])).

fof(f3209,plain,
    ( ~ spl3_62
    | ~ spl3_4
    | ~ spl3_5
    | spl3_61
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f3179,f2865,f3182,f67,f62,f3206])).

fof(f3206,plain,
    ( spl3_62
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f3179,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))
    | ~ spl3_60 ),
    inference(superposition,[],[f31,f2867])).

fof(f3185,plain,
    ( spl3_61
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f3155,f2865,f67,f62,f52,f3182])).

fof(f3155,plain,
    ( k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_60 ),
    inference(superposition,[],[f177,f2867])).

fof(f2881,plain,
    ( ~ spl3_59
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2815,f155,f76,f47,f2856])).

fof(f2856,plain,
    ( spl3_59
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f155,plain,
    ( spl3_15
  <=> k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2815,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(resolution,[],[f2744,f1412])).

fof(f2744,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),X0)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f2722,f77])).

fof(f2722,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2713,f34])).

fof(f2713,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f44,f648])).

fof(f648,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X3),X2)
        | r1_tarski(k10_relat_1(sK2,sK0),X2) )
    | ~ spl3_15 ),
    inference(resolution,[],[f395,f33])).

fof(f395,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK1),X1)
        | r1_tarski(k10_relat_1(sK2,sK0),X1) )
    | ~ spl3_15 ),
    inference(superposition,[],[f33,f157])).

fof(f157,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f2875,plain,
    ( ~ spl3_56
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2752,f155,f116,f76,f47,f2836])).

fof(f2836,plain,
    ( spl3_56
  <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f2752,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f49,f2744,f557])).

fof(f2873,plain,
    ( spl3_60
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2761,f155,f116,f76,f2865])).

fof(f2761,plain,
    ( k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f562,f2744,f38])).

fof(f2868,plain,
    ( spl3_60
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2769,f155,f116,f76,f2865])).

fof(f2769,plain,
    ( k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f562,f2744,f38])).

fof(f2863,plain,
    ( ~ spl3_56
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2773,f155,f116,f76,f47,f2836])).

fof(f2773,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f434])).

fof(f2862,plain,
    ( ~ spl3_57
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2774,f155,f76,f47,f2841])).

fof(f2841,plain,
    ( spl3_57
  <=> r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f2774,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f271])).

fof(f2861,plain,
    ( ~ spl3_56
    | ~ spl3_6
    | ~ spl3_15
    | spl3_21 ),
    inference(avatar_split_clause,[],[f2775,f295,f155,f76,f2836])).

fof(f2775,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_15
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f2744,f793])).

fof(f2860,plain,
    ( ~ spl3_57
    | ~ spl3_6
    | ~ spl3_15
    | spl3_19 ),
    inference(avatar_split_clause,[],[f2777,f282,f155,f76,f2841])).

fof(f2777,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_15
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f2744,f392])).

fof(f2859,plain,
    ( ~ spl3_59
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2778,f155,f76,f47,f2856])).

fof(f2778,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f1412])).

fof(f2854,plain,
    ( ~ spl3_56
    | ~ spl3_6
    | spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2779,f155,f133,f76,f2836])).

fof(f2779,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | spl3_13
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f438])).

fof(f2853,plain,
    ( ~ spl3_57
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2780,f155,f116,f76,f47,f2841])).

fof(f2780,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f675])).

fof(f2852,plain,
    ( ~ spl3_57
    | ~ spl3_6
    | ~ spl3_15
    | spl3_29 ),
    inference(avatar_split_clause,[],[f2781,f872,f155,f76,f2841])).

fof(f2781,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_15
    | spl3_29 ),
    inference(unit_resulting_resolution,[],[f2744,f898])).

fof(f2850,plain,
    ( spl3_58
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2789,f155,f111,f76,f2847])).

fof(f2847,plain,
    ( spl3_58
  <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f2789,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f278])).

fof(f2845,plain,
    ( ~ spl3_56
    | ~ spl3_6
    | spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2794,f155,f133,f76,f2836])).

fof(f2794,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | spl3_13
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f190])).

fof(f2844,plain,
    ( ~ spl3_57
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2795,f155,f76,f47,f2841])).

fof(f2795,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2744,f174])).

fof(f2839,plain,
    ( ~ spl3_56
    | ~ spl3_6
    | ~ spl3_15
    | spl3_18 ),
    inference(avatar_split_clause,[],[f2797,f197,f155,f76,f2836])).

fof(f2797,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))
    | ~ spl3_6
    | ~ spl3_15
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f2744,f232])).

fof(f2747,plain,
    ( spl3_55
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2746,f155,f80,f76,f2740])).

fof(f2740,plain,
    ( spl3_55
  <=> k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f2746,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f2730,f77])).

fof(f2730,plain,
    ( k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(resolution,[],[f2713,f359])).

fof(f359,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X4,k2_xboole_0(X5,k2_relat_1(sK2)))
        | k4_xboole_0(X4,X5) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X4,X5))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f81,f34])).

fof(f2743,plain,
    ( spl3_55
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f2738,f155,f80,f76,f2740])).

fof(f2738,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f2723,f77])).

fof(f2723,plain,
    ( k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f2713,f359])).

fof(f2520,plain,
    ( spl3_53
    | ~ spl3_54
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2491,f1265,f2516,f2512])).

fof(f2512,plain,
    ( spl3_53
  <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f1265,plain,
    ( spl3_43
  <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f2491,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))
    | k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0))
    | ~ spl3_43 ),
    inference(resolution,[],[f1267,f38])).

fof(f1267,plain,
    ( r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f1265])).

fof(f2519,plain,
    ( spl3_53
    | ~ spl3_54
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2490,f1265,f2516,f2512])).

fof(f2490,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))
    | k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0))
    | ~ spl3_43 ),
    inference(resolution,[],[f1267,f38])).

fof(f2510,plain,
    ( spl3_51
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2509,f1265,f76,f2495])).

fof(f2509,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f2489,f77])).

fof(f2489,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))))
    | ~ spl3_43 ),
    inference(resolution,[],[f1267,f39])).

fof(f2508,plain,
    ( spl3_52
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2488,f1265,f2500])).

fof(f2500,plain,
    ( spl3_52
  <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f2488,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_43 ),
    inference(resolution,[],[f1267,f40])).

fof(f2506,plain,
    ( spl3_51
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2485,f1265,f76,f2495])).

fof(f2485,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(resolution,[],[f1267,f428])).

fof(f428,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k10_relat_1(sK2,X4),k10_relat_1(sK2,X3))
        | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X4),k10_relat_1(sK2,k4_xboole_0(X3,X4))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f39,f77])).

fof(f2505,plain,
    ( spl3_51
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2479,f1265,f76,f2495])).

fof(f2479,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(unit_resulting_resolution,[],[f1267,f428])).

fof(f2503,plain,
    ( spl3_52
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2482,f1265,f2500])).

fof(f2482,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_43 ),
    inference(unit_resulting_resolution,[],[f1267,f40])).

fof(f2498,plain,
    ( spl3_51
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f2493,f1265,f76,f2495])).

fof(f2493,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))
    | ~ spl3_6
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f2483,f77])).

fof(f2483,plain,
    ( k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))))
    | ~ spl3_43 ),
    inference(unit_resulting_resolution,[],[f1267,f39])).

fof(f2425,plain,
    ( ~ spl3_50
    | ~ spl3_9
    | spl3_39 ),
    inference(avatar_split_clause,[],[f2410,f1104,f111,f2422])).

fof(f2422,plain,
    ( spl3_50
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1104,plain,
    ( spl3_39
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f2410,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f1106,f280])).

fof(f280,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k4_xboole_0(X4,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
        | r1_tarski(X4,k2_relat_1(sK2)) )
    | ~ spl3_9 ),
    inference(superposition,[],[f32,f113])).

fof(f1106,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f1104])).

fof(f2420,plain,
    ( ~ spl3_49
    | ~ spl3_10
    | spl3_39 ),
    inference(avatar_split_clause,[],[f2411,f1104,f116,f2417])).

fof(f2417,plain,
    ( spl3_49
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f2411,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k2_relat_1(sK2))
    | ~ spl3_10
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f1106,f195])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k4_xboole_0(X2,sK0),k2_relat_1(sK2))
        | r1_tarski(X2,k2_relat_1(sK2)) )
    | ~ spl3_10 ),
    inference(superposition,[],[f32,f118])).

fof(f1418,plain,
    ( ~ spl3_48
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1413,f116,f47,f1415])).

fof(f1415,plain,
    ( spl3_48
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f1413,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),sK1)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f1367,f588])).

fof(f1400,plain,
    ( ~ spl3_47
    | ~ spl3_45
    | spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1380,f150,f47,f1387,f1397])).

fof(f1397,plain,
    ( spl3_47
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1387,plain,
    ( spl3_45
  <=> r1_tarski(k10_relat_1(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f1380,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | spl3_1
    | ~ spl3_14 ),
    inference(superposition,[],[f210,f152])).

fof(f1395,plain,
    ( ~ spl3_46
    | ~ spl3_45
    | spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1379,f155,f47,f1387,f1392])).

fof(f1392,plain,
    ( spl3_46
  <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1379,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))
    | spl3_1
    | ~ spl3_15 ),
    inference(superposition,[],[f210,f157])).

fof(f1390,plain,
    ( spl3_44
    | ~ spl3_45
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1378,f57,f47,f1387,f1384])).

fof(f1384,plain,
    ( spl3_44
  <=> ! [X7] : ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,sK0),X7)),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1378,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK1),sK1)
        | ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,sK0),X7)),k10_relat_1(sK2,sK1)) )
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f210,f311])).

fof(f311,plain,
    ( ! [X0] : k10_relat_1(sK2,sK1) = k2_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f142,f40])).

fof(f1273,plain,
    ( spl3_43
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1272,f150,f76,f57,f1265])).

fof(f1272,plain,
    ( r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1255,f77])).

fof(f1255,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(resolution,[],[f489,f59])).

fof(f489,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_relat_1(sK2,sK1))
        | r1_tarski(k4_xboole_0(X0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) )
    | ~ spl3_14 ),
    inference(superposition,[],[f34,f152])).

fof(f1268,plain,
    ( spl3_43
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1263,f150,f76,f57,f1265])).

fof(f1263,plain,
    ( r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1237,f77])).

fof(f1237,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f59,f489])).

fof(f1148,plain,
    ( ~ spl3_42
    | ~ spl3_2
    | spl3_35 ),
    inference(avatar_split_clause,[],[f1126,f1065,f52,f1145])).

fof(f1145,plain,
    ( spl3_42
  <=> r1_tarski(k10_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f1065,plain,
    ( spl3_35
  <=> r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f1126,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),sK0)
    | ~ spl3_2
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f54,f1093])).

fof(f1093,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK1),X0)
        | ~ r1_tarski(X0,k2_relat_1(sK2)) )
    | spl3_35 ),
    inference(superposition,[],[f1077,f39])).

fof(f1077,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X0),k2_relat_1(sK2))
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f1067,f33])).

fof(f1067,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f1065])).

fof(f1143,plain,
    ( ~ spl3_41
    | ~ spl3_10
    | spl3_35 ),
    inference(avatar_split_clause,[],[f1132,f1065,f116,f1140])).

fof(f1140,plain,
    ( spl3_41
  <=> r1_tarski(k10_relat_1(sK2,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f1132,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_10
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f562,f1093])).

fof(f1112,plain,
    ( ~ spl3_40
    | ~ spl3_9
    | spl3_37 ),
    inference(avatar_split_clause,[],[f1097,f1080,f111,f1109])).

fof(f1109,plain,
    ( spl3_40
  <=> r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1080,plain,
    ( spl3_37
  <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1097,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f1082,f280])).

fof(f1082,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f1107,plain,
    ( ~ spl3_39
    | ~ spl3_10
    | spl3_37 ),
    inference(avatar_split_clause,[],[f1098,f1080,f116,f1104])).

fof(f1098,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2))
    | ~ spl3_10
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f1082,f195])).

fof(f1088,plain,
    ( ~ spl3_38
    | ~ spl3_9
    | spl3_35 ),
    inference(avatar_split_clause,[],[f1075,f1065,f111,f1085])).

fof(f1085,plain,
    ( spl3_38
  <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1075,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f1067,f280])).

fof(f1083,plain,
    ( ~ spl3_37
    | ~ spl3_10
    | spl3_35 ),
    inference(avatar_split_clause,[],[f1076,f1065,f116,f1080])).

fof(f1076,plain,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2))
    | ~ spl3_10
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f1067,f195])).

fof(f1074,plain,
    ( spl3_36
    | ~ spl3_35
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1058,f150,f80,f1065,f1070])).

fof(f1058,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2))
    | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f355,f152])).

fof(f1073,plain,
    ( spl3_36
    | ~ spl3_35
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f1057,f155,f80,f1065,f1070])).

fof(f1057,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2))
    | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0)))
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(superposition,[],[f355,f157])).

fof(f1068,plain,
    ( spl3_34
    | ~ spl3_35
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f1056,f80,f57,f1065,f1062])).

fof(f1056,plain,
    ( ! [X7] :
        ( ~ r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2))
        | k4_xboole_0(k10_relat_1(sK2,sK0),X7) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X7))) )
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f355,f311])).

fof(f988,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f978,f116,f52,f984])).

fof(f978,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(superposition,[],[f588,f179])).

fof(f987,plain,
    ( spl3_33
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f976,f116,f52,f984])).

fof(f976,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(superposition,[],[f179,f588])).

fof(f923,plain,
    ( ~ spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f916,f885,f919])).

fof(f919,plain,
    ( spl3_32
  <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f885,plain,
    ( spl3_31
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f916,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0)))
    | spl3_31 ),
    inference(resolution,[],[f887,f34])).

fof(f887,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f885])).

fof(f922,plain,
    ( ~ spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f913,f885,f919])).

fof(f913,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0)))
    | spl3_31 ),
    inference(unit_resulting_resolution,[],[f887,f34])).

fof(f889,plain,
    ( spl3_30
    | ~ spl3_31
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f859,f845,f885,f881])).

fof(f881,plain,
    ( spl3_30
  <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f845,plain,
    ( spl3_26
  <=> r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f859,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))
    | k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_26 ),
    inference(resolution,[],[f847,f38])).

fof(f847,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f845])).

fof(f888,plain,
    ( spl3_30
    | ~ spl3_31
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f858,f845,f885,f881])).

fof(f858,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))
    | k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_26 ),
    inference(resolution,[],[f847,f38])).

fof(f879,plain,
    ( spl3_27
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f857,f845,f862])).

fof(f862,plain,
    ( spl3_27
  <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f857,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)))
    | ~ spl3_26 ),
    inference(resolution,[],[f847,f39])).

fof(f878,plain,
    ( spl3_28
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f856,f845,f867])).

fof(f867,plain,
    ( spl3_28
  <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f856,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_26 ),
    inference(resolution,[],[f847,f40])).

fof(f875,plain,
    ( ~ spl3_29
    | spl3_19
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f851,f845,f282,f872])).

fof(f851,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK0))
    | spl3_19
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f847,f392])).

fof(f870,plain,
    ( spl3_28
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f852,f845,f867])).

fof(f852,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f847,f40])).

fof(f865,plain,
    ( spl3_27
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f853,f845,f862])).

fof(f853,plain,
    ( k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)))
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f847,f39])).

fof(f849,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f842,f111,f52,f845])).

fof(f842,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f278,f54])).

fof(f848,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f826,f111,f52,f845])).

fof(f826,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f54,f278])).

fof(f655,plain,
    ( ~ spl3_25
    | ~ spl3_15
    | spl3_22 ),
    inference(avatar_split_clause,[],[f644,f493,f155,f652])).

fof(f652,plain,
    ( spl3_25
  <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f493,plain,
    ( spl3_22
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f644,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_15
    | spl3_22 ),
    inference(unit_resulting_resolution,[],[f495,f395])).

fof(f495,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f493])).

fof(f622,plain,
    ( ~ spl3_24
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f599,f116,f47,f618])).

fof(f618,plain,
    ( spl3_24
  <=> r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f599,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f271])).

fof(f621,plain,
    ( ~ spl3_24
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f606,f116,f47,f618])).

fof(f606,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2)))
    | spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f562,f174])).

fof(f501,plain,
    ( ~ spl3_22
    | spl3_23
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f488,f150,f497,f493])).

fof(f497,plain,
    ( spl3_23
  <=> k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f488,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f40,f152])).

fof(f500,plain,
    ( ~ spl3_22
    | spl3_23
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f487,f150,f497,f493])).

fof(f487,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f152,f40])).

fof(f298,plain,
    ( ~ spl3_21
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_split_clause,[],[f291,f282,f116,f295])).

fof(f291,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_10
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f284,f194])).

fof(f290,plain,
    ( ~ spl3_19
    | spl3_20
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f277,f111,f286,f282])).

fof(f286,plain,
    ( spl3_20
  <=> k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f277,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9 ),
    inference(superposition,[],[f40,f113])).

fof(f289,plain,
    ( ~ spl3_19
    | spl3_20
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f273,f111,f286,f282])).

fof(f273,plain,
    ( k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_9 ),
    inference(superposition,[],[f113,f40])).

fof(f200,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f192,f116,f47,f197])).

fof(f192,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f98,f118])).

fof(f171,plain,
    ( spl3_16
    | ~ spl3_17
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f146,f57,f167,f163])).

fof(f163,plain,
    ( spl3_16
  <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f167,plain,
    ( spl3_17
  <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f146,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f38])).

fof(f170,plain,
    ( spl3_16
    | ~ spl3_17
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f145,f57,f167,f163])).

fof(f145,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f38])).

fof(f161,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f160,f76,f57,f150])).

fof(f160,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f144,f77])).

fof(f144,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f39])).

fof(f159,plain,
    ( spl3_15
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f143,f57,f155])).

fof(f143,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f40])).

fof(f158,plain,
    ( spl3_15
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f140,f57,f155])).

fof(f140,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f59,f40])).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f148,f76,f57,f150])).

fof(f148,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f141,f77])).

fof(f141,plain,
    ( k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f59,f39])).

fof(f137,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f108,f52,f133,f129])).

fof(f129,plain,
    ( spl3_12
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f108,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | sK0 = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f38])).

fof(f136,plain,
    ( spl3_12
    | ~ spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f107,f52,f133,f129])).

fof(f107,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | sK0 = k2_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f38])).

fof(f127,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f106,f52,f111])).

fof(f106,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f39])).

fof(f126,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f105,f52,f116])).

fof(f105,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f40])).

fof(f125,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f104,f52,f67,f62,f121])).

fof(f121,plain,
    ( spl3_11
  <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f54,f31])).

fof(f124,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f100,f67,f62,f52,f121])).

fof(f100,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f69,f54,f31])).

fof(f119,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f52,f116])).

fof(f101,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f40])).

fof(f114,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f102,f52,f111])).

fof(f102,plain,
    ( k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f54,f39])).

fof(f94,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f84,f67,f62,f90])).

fof(f90,plain,
    ( spl3_8
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f45,f69,f31])).

fof(f93,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f85,f67,f62,f90])).

fof(f85,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f64,f44,f69,f31])).

fof(f82,plain,
    ( spl3_7
    | ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f72,f62,f67,f80])).

fof(f72,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X2,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2 )
    | ~ spl3_4 ),
    inference(resolution,[],[f64,f31])).

fof(f78,plain,
    ( ~ spl3_5
    | spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f74,f62,f76,f67])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f73,f43])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f71,f43])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f64,f42])).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f47])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (15933)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (15930)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (15955)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (15935)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (15938)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (15936)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (15938)Refutation not found, incomplete strategy% (15938)------------------------------
% 0.20/0.52  % (15938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15938)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15938)Memory used [KB]: 10746
% 0.20/0.52  % (15938)Time elapsed: 0.115 s
% 0.20/0.52  % (15938)------------------------------
% 0.20/0.52  % (15938)------------------------------
% 0.20/0.52  % (15943)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (15928)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (15941)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (15949)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (15940)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (15929)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (15929)Refutation not found, incomplete strategy% (15929)------------------------------
% 0.20/0.53  % (15929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15950)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (15929)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15929)Memory used [KB]: 1663
% 0.20/0.53  % (15929)Time elapsed: 0.124 s
% 0.20/0.53  % (15929)------------------------------
% 0.20/0.53  % (15929)------------------------------
% 0.20/0.53  % (15956)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (15934)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (15942)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (15948)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (15932)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (15940)Refutation not found, incomplete strategy% (15940)------------------------------
% 0.20/0.53  % (15940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15940)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15940)Memory used [KB]: 10618
% 0.20/0.53  % (15940)Time elapsed: 0.132 s
% 0.20/0.53  % (15940)------------------------------
% 0.20/0.53  % (15940)------------------------------
% 0.20/0.53  % (15947)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (15931)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (15946)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (15937)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (15957)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (15957)Refutation not found, incomplete strategy% (15957)------------------------------
% 0.20/0.54  % (15957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15957)Memory used [KB]: 1663
% 0.20/0.54  % (15957)Time elapsed: 0.001 s
% 0.20/0.54  % (15957)------------------------------
% 0.20/0.54  % (15957)------------------------------
% 0.20/0.54  % (15939)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (15956)Refutation not found, incomplete strategy% (15956)------------------------------
% 0.20/0.54  % (15956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15956)Memory used [KB]: 10746
% 0.20/0.54  % (15956)Time elapsed: 0.117 s
% 0.20/0.54  % (15956)------------------------------
% 0.20/0.54  % (15956)------------------------------
% 0.20/0.54  % (15954)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (15952)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (15953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.55  % (15951)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.55  % (15945)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.55  % (15944)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.55  % (15944)Refutation not found, incomplete strategy% (15944)------------------------------
% 1.48/0.55  % (15944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (15944)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (15944)Memory used [KB]: 10618
% 1.48/0.55  % (15944)Time elapsed: 0.160 s
% 1.48/0.55  % (15944)------------------------------
% 1.48/0.55  % (15944)------------------------------
% 2.01/0.63  % (16011)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.64  % (16012)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.01/0.65  % (15931)Refutation not found, incomplete strategy% (15931)------------------------------
% 2.01/0.65  % (15931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (15943)Refutation not found, incomplete strategy% (15943)------------------------------
% 2.26/0.66  % (15943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (16019)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.26/0.66  % (15931)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.66  
% 2.26/0.67  % (15931)Memory used [KB]: 6140
% 2.26/0.67  % (15931)Time elapsed: 0.249 s
% 2.26/0.67  % (15931)------------------------------
% 2.26/0.67  % (15931)------------------------------
% 2.26/0.67  % (16017)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.26/0.67  % (16023)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.26/0.67  % (15928)Refutation not found, incomplete strategy% (15928)------------------------------
% 2.26/0.67  % (15928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  % (16017)Refutation not found, incomplete strategy% (16017)------------------------------
% 2.26/0.68  % (16017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  % (16017)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.68  
% 2.26/0.68  % (16017)Memory used [KB]: 6140
% 2.26/0.68  % (16017)Time elapsed: 0.113 s
% 2.26/0.68  % (16017)------------------------------
% 2.26/0.68  % (16017)------------------------------
% 2.26/0.68  % (15928)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.68  
% 2.26/0.68  % (15928)Memory used [KB]: 1663
% 2.26/0.68  % (15928)Time elapsed: 0.267 s
% 2.26/0.68  % (15928)------------------------------
% 2.26/0.68  % (15928)------------------------------
% 2.26/0.68  % (16020)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.26/0.68  % (15943)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.68  
% 2.26/0.68  % (15943)Memory used [KB]: 6140
% 2.26/0.68  % (15943)Time elapsed: 0.261 s
% 2.26/0.68  % (15943)------------------------------
% 2.26/0.68  % (15943)------------------------------
% 3.01/0.79  % (15952)Time limit reached!
% 3.01/0.79  % (15952)------------------------------
% 3.01/0.79  % (15952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.79  % (15952)Termination reason: Time limit
% 3.01/0.79  
% 3.01/0.79  % (15952)Memory used [KB]: 13944
% 3.01/0.79  % (15952)Time elapsed: 0.400 s
% 3.01/0.79  % (15952)------------------------------
% 3.01/0.79  % (15952)------------------------------
% 3.01/0.81  % (15930)Time limit reached!
% 3.01/0.81  % (15930)------------------------------
% 3.01/0.81  % (15930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.81  % (16104)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.01/0.81  % (16098)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.01/0.82  % (16108)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.01/0.82  % (16105)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.01/0.82  % (15930)Termination reason: Time limit
% 3.01/0.82  
% 3.01/0.82  % (15930)Memory used [KB]: 7547
% 3.01/0.82  % (15930)Time elapsed: 0.406 s
% 3.01/0.82  % (15930)------------------------------
% 3.01/0.82  % (15930)------------------------------
% 3.56/0.91  % (15942)Time limit reached!
% 3.56/0.91  % (15942)------------------------------
% 3.56/0.91  % (15942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.91  % (15942)Termination reason: Time limit
% 3.56/0.91  % (15942)Termination phase: Saturation
% 3.56/0.91  
% 3.56/0.91  % (15942)Memory used [KB]: 5245
% 3.56/0.91  % (15942)Time elapsed: 0.525 s
% 3.56/0.91  % (15942)------------------------------
% 3.56/0.91  % (15942)------------------------------
% 3.95/0.93  % (16135)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.95/0.94  % (15934)Time limit reached!
% 3.95/0.94  % (15934)------------------------------
% 3.95/0.94  % (15934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.95  % (15934)Termination reason: Time limit
% 3.95/0.95  
% 3.95/0.95  % (15934)Memory used [KB]: 15863
% 3.95/0.95  % (15934)Time elapsed: 0.512 s
% 3.95/0.95  % (15934)------------------------------
% 3.95/0.95  % (15934)------------------------------
% 3.95/0.95  % (16142)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.13/1.01  % (15935)Time limit reached!
% 4.13/1.01  % (15935)------------------------------
% 4.13/1.01  % (15935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/1.02  % (15935)Termination reason: Time limit
% 4.13/1.02  % (15935)Termination phase: Saturation
% 4.13/1.02  
% 4.13/1.02  % (15935)Memory used [KB]: 7419
% 4.13/1.02  % (15935)Time elapsed: 0.600 s
% 4.13/1.02  % (15935)------------------------------
% 4.13/1.02  % (15935)------------------------------
% 4.49/1.05  % (16194)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 5.67/1.09  % (16199)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 6.19/1.16  % (16200)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.40/1.22  % (15936)Refutation found. Thanks to Tanya!
% 6.40/1.22  % SZS status Theorem for theBenchmark
% 6.40/1.22  % SZS output start Proof for theBenchmark
% 6.40/1.22  fof(f8203,plain,(
% 6.40/1.22    $false),
% 6.40/1.22    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f70,f78,f82,f93,f94,f114,f119,f124,f125,f126,f127,f136,f137,f153,f158,f159,f161,f170,f171,f200,f289,f290,f298,f500,f501,f621,f622,f655,f848,f849,f865,f870,f875,f878,f879,f888,f889,f922,f923,f987,f988,f1068,f1073,f1074,f1083,f1088,f1107,f1112,f1143,f1148,f1268,f1273,f1390,f1395,f1400,f1418,f2420,f2425,f2498,f2503,f2505,f2506,f2508,f2510,f2519,f2520,f2743,f2747,f2839,f2844,f2845,f2850,f2852,f2853,f2854,f2859,f2860,f2861,f2862,f2863,f2868,f2873,f2875,f2881,f3185,f3209,f3305,f3345,f3771,f4203,f6315,f6316,f6317,f6318,f6332,f6333,f6358,f6359,f6360,f6361,f6362,f6367,f6505,f6551,f6552,f6701,f6702,f6763,f6764,f6765,f6766,f6767,f6772,f7115,f7120,f7378,f7383,f7388,f7393,f7398,f7399,f7400,f7404,f7406,f7407,f7412,f7413,f7422,f7424,f7425,f7426,f7427,f7428,f7429,f7430,f7431,f7432,f7433,f7434,f7435,f7440,f7441,f7442,f7443,f7448,f7449,f7450,f7451,f7457,f7466,f7469,f7478,f7479,f7480,f7481,f7484,f7493,f7494,f7883,f7884,f7888,f7889,f8062,f8067,f8101,f8109,f8115,f8148,f8153,f8158,f8172,f8173,f8202])).
% 6.40/1.22  fof(f8202,plain,(
% 6.40/1.22    spl3_98),
% 6.40/1.22    inference(avatar_contradiction_clause,[],[f8197])).
% 6.40/1.22  fof(f8197,plain,(
% 6.40/1.22    $false | spl3_98),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f45,f8171,f33])).
% 6.40/1.22  fof(f33,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 6.40/1.22    inference(cnf_transformation,[],[f19])).
% 6.40/1.22  fof(f19,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 6.40/1.22    inference(ennf_transformation,[],[f3])).
% 6.40/1.22  fof(f3,axiom,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 6.40/1.22  fof(f8171,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl3_98),
% 6.40/1.22    inference(avatar_component_clause,[],[f8169])).
% 6.40/1.22  fof(f8169,plain,(
% 6.40/1.22    spl3_98 <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 6.40/1.22  fof(f45,plain,(
% 6.40/1.22    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.40/1.22    inference(equality_resolution,[],[f36])).
% 6.40/1.22  fof(f36,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.40/1.22    inference(cnf_transformation,[],[f1])).
% 6.40/1.22  fof(f1,axiom,(
% 6.40/1.22    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.40/1.22  fof(f8173,plain,(
% 6.40/1.22    ~spl3_98 | spl3_95),
% 6.40/1.22    inference(avatar_split_clause,[],[f8166,f8145,f8169])).
% 6.40/1.22  fof(f8145,plain,(
% 6.40/1.22    spl3_95 <=> r1_tarski(k4_xboole_0(sK0,sK0),sK1)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 6.40/1.22  fof(f8166,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl3_95),
% 6.40/1.22    inference(resolution,[],[f8147,f34])).
% 6.40/1.22  fof(f34,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 6.40/1.22    inference(cnf_transformation,[],[f20])).
% 6.40/1.22  fof(f20,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.40/1.22    inference(ennf_transformation,[],[f6])).
% 6.40/1.22  fof(f6,axiom,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 6.40/1.22  fof(f8147,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK0),sK1) | spl3_95),
% 6.40/1.22    inference(avatar_component_clause,[],[f8145])).
% 6.40/1.22  fof(f8172,plain,(
% 6.40/1.22    ~spl3_98 | spl3_95),
% 6.40/1.22    inference(avatar_split_clause,[],[f8163,f8145,f8169])).
% 6.40/1.22  fof(f8163,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl3_95),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f8147,f34])).
% 6.40/1.22  fof(f8158,plain,(
% 6.40/1.22    spl3_97 | ~spl3_90 | ~spl3_94),
% 6.40/1.22    inference(avatar_split_clause,[],[f8141,f8112,f8059,f8155])).
% 6.40/1.22  fof(f8155,plain,(
% 6.40/1.22    spl3_97 <=> k4_xboole_0(sK0,sK0) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 6.40/1.22  fof(f8059,plain,(
% 6.40/1.22    spl3_90 <=> k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 6.40/1.22  fof(f8112,plain,(
% 6.40/1.22    spl3_94 <=> k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 6.40/1.22  fof(f8141,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK0) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_90 | ~spl3_94)),
% 6.40/1.22    inference(backward_demodulation,[],[f8061,f8114])).
% 6.40/1.22  fof(f8114,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) | ~spl3_94),
% 6.40/1.22    inference(avatar_component_clause,[],[f8112])).
% 6.40/1.22  fof(f8061,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_90),
% 6.40/1.22    inference(avatar_component_clause,[],[f8059])).
% 6.40/1.22  fof(f8153,plain,(
% 6.40/1.22    ~spl3_96 | spl3_71 | ~spl3_94),
% 6.40/1.22    inference(avatar_split_clause,[],[f8131,f8112,f6548,f8150])).
% 6.40/1.22  fof(f8150,plain,(
% 6.40/1.22    spl3_96 <=> r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 6.40/1.22  fof(f6548,plain,(
% 6.40/1.22    spl3_71 <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 6.40/1.22  fof(f8131,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,k2_relat_1(sK2))) | (spl3_71 | ~spl3_94)),
% 6.40/1.22    inference(backward_demodulation,[],[f6550,f8114])).
% 6.40/1.22  fof(f6550,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) | spl3_71),
% 6.40/1.22    inference(avatar_component_clause,[],[f6548])).
% 6.40/1.22  fof(f8148,plain,(
% 6.40/1.22    ~spl3_95 | spl3_67 | ~spl3_94),
% 6.40/1.22    inference(avatar_split_clause,[],[f8123,f8112,f6312,f8145])).
% 6.40/1.22  fof(f6312,plain,(
% 6.40/1.22    spl3_67 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK1)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 6.40/1.22  fof(f8123,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK0),sK1) | (spl3_67 | ~spl3_94)),
% 6.40/1.22    inference(backward_demodulation,[],[f6314,f8114])).
% 6.40/1.22  fof(f6314,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl3_67),
% 6.40/1.22    inference(avatar_component_clause,[],[f6312])).
% 6.40/1.22  fof(f8115,plain,(
% 6.40/1.22    spl3_94 | ~spl3_61 | ~spl3_91),
% 6.40/1.22    inference(avatar_split_clause,[],[f8110,f8064,f3182,f8112])).
% 6.40/1.22  fof(f3182,plain,(
% 6.40/1.22    spl3_61 <=> k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 6.40/1.22  fof(f8064,plain,(
% 6.40/1.22    spl3_91 <=> k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 6.40/1.22  fof(f8110,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) | (~spl3_61 | ~spl3_91)),
% 6.40/1.22    inference(backward_demodulation,[],[f3184,f8066])).
% 6.40/1.22  fof(f8066,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | ~spl3_91),
% 6.40/1.22    inference(avatar_component_clause,[],[f8064])).
% 6.40/1.22  fof(f3184,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | ~spl3_61),
% 6.40/1.22    inference(avatar_component_clause,[],[f3182])).
% 6.40/1.22  fof(f8109,plain,(
% 6.40/1.22    ~spl3_4 | ~spl3_5 | spl3_93 | ~spl3_6 | ~spl3_10 | ~spl3_61),
% 6.40/1.22    inference(avatar_split_clause,[],[f8105,f3182,f116,f76,f8107,f67,f62])).
% 6.40/1.22  fof(f62,plain,(
% 6.40/1.22    spl3_4 <=> v1_funct_1(sK2)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 6.40/1.22  fof(f67,plain,(
% 6.40/1.22    spl3_5 <=> v1_relat_1(sK2)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 6.40/1.22  fof(f8107,plain,(
% 6.40/1.22    spl3_93 <=> ! [X90] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X90,X90) | ~r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 6.40/1.22  fof(f76,plain,(
% 6.40/1.22    spl3_6 <=> ! [X1,X0] : k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 6.40/1.22  fof(f116,plain,(
% 6.40/1.22    spl3_10 <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 6.40/1.22  fof(f8105,plain,(
% 6.40/1.22    ( ! [X90] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X90,X90) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2))) ) | (~spl3_6 | ~spl3_10 | ~spl3_61)),
% 6.40/1.22    inference(forward_demodulation,[],[f8050,f3184])).
% 6.40/1.22  fof(f8050,plain,(
% 6.40/1.22    ( ! [X90] : (k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(X90,X90) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k4_xboole_0(X90,X90),k2_relat_1(sK2))) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(superposition,[],[f31,f6877])).
% 6.40/1.22  fof(f6877,plain,(
% 6.40/1.22    ( ! [X0] : (k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(X0,X0))) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f562,f6826,f38])).
% 6.40/1.22  fof(f38,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 6.40/1.22    inference(cnf_transformation,[],[f1])).
% 6.40/1.22  fof(f6826,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X0,X0)),X1)) ) | ~spl3_6),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f44,f1192])).
% 6.40/1.22  fof(f1192,plain,(
% 6.40/1.22    ( ! [X6,X4,X7,X5] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,X4),X7),k2_xboole_0(k10_relat_1(sK2,X5),X6)) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X4,X5)),X6)) ) | ~spl3_6),
% 6.40/1.22    inference(resolution,[],[f430,f33])).
% 6.40/1.22  fof(f430,plain,(
% 6.40/1.22    ( ! [X10,X8,X9] : (~r1_tarski(k10_relat_1(sK2,X8),k2_xboole_0(k10_relat_1(sK2,X9),X10)) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X8,X9)),X10)) ) | ~spl3_6),
% 6.40/1.22    inference(superposition,[],[f34,f77])).
% 6.40/1.22  fof(f77,plain,(
% 6.40/1.22    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1))) ) | ~spl3_6),
% 6.40/1.22    inference(avatar_component_clause,[],[f76])).
% 6.40/1.22  fof(f44,plain,(
% 6.40/1.22    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.40/1.22    inference(equality_resolution,[],[f37])).
% 6.40/1.22  fof(f37,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.40/1.22    inference(cnf_transformation,[],[f1])).
% 6.40/1.22  fof(f562,plain,(
% 6.40/1.22    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k2_relat_1(sK2)),X0)) ) | ~spl3_10),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f552,f34])).
% 6.40/1.22  fof(f552,plain,(
% 6.40/1.22    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0))) ) | ~spl3_10),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f44,f252])).
% 6.40/1.22  fof(f252,plain,(
% 6.40/1.22    ( ! [X2,X3] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X3),X2) | r1_tarski(sK0,X2)) ) | ~spl3_10),
% 6.40/1.22    inference(resolution,[],[f194,f33])).
% 6.40/1.22  fof(f194,plain,(
% 6.40/1.22    ( ! [X1] : (~r1_tarski(k2_relat_1(sK2),X1) | r1_tarski(sK0,X1)) ) | ~spl3_10),
% 6.40/1.22    inference(superposition,[],[f33,f118])).
% 6.40/1.22  fof(f118,plain,(
% 6.40/1.22    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_10),
% 6.40/1.22    inference(avatar_component_clause,[],[f116])).
% 6.40/1.22  fof(f31,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 6.40/1.22    inference(cnf_transformation,[],[f17])).
% 6.40/1.22  fof(f17,plain,(
% 6.40/1.22    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.40/1.22    inference(flattening,[],[f16])).
% 6.40/1.22  fof(f16,plain,(
% 6.40/1.22    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.40/1.22    inference(ennf_transformation,[],[f11])).
% 6.40/1.22  fof(f11,axiom,(
% 6.40/1.22    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 6.40/1.22  fof(f8101,plain,(
% 6.40/1.22    ~spl3_4 | ~spl3_5 | spl3_92 | ~spl3_6 | ~spl3_10 | ~spl3_60),
% 6.40/1.22    inference(avatar_split_clause,[],[f8097,f2865,f116,f76,f8099,f67,f62])).
% 6.40/1.22  fof(f8099,plain,(
% 6.40/1.22    spl3_92 <=> ! [X86,X87] : k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(X86,X86)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 6.40/1.22  fof(f2865,plain,(
% 6.40/1.22    spl3_60 <=> k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 6.40/1.22  fof(f8097,plain,(
% 6.40/1.22    ( ! [X87,X86] : (k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(X86,X86))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)) ) | (~spl3_6 | ~spl3_10 | ~spl3_60)),
% 6.40/1.22    inference(forward_demodulation,[],[f8096,f43])).
% 6.40/1.22  fof(f43,plain,(
% 6.40/1.22    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.40/1.22    inference(cnf_transformation,[],[f9])).
% 6.40/1.22  fof(f9,axiom,(
% 6.40/1.22    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.40/1.22  fof(f8096,plain,(
% 6.40/1.22    ( ! [X87,X86] : (k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k10_relat_1(sK2,k4_xboole_0(X87,k4_xboole_0(sK0,sK1))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)) ) | (~spl3_6 | ~spl3_10 | ~spl3_60)),
% 6.40/1.22    inference(forward_demodulation,[],[f8095,f3161])).
% 6.40/1.22  fof(f3161,plain,(
% 6.40/1.22    ( ! [X5] : (k10_relat_1(sK2,k4_xboole_0(X5,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k10_relat_1(sK2,X5),k4_xboole_0(sK0,k2_relat_1(sK2)))) ) | (~spl3_6 | ~spl3_60)),
% 6.40/1.22    inference(superposition,[],[f77,f2867])).
% 6.40/1.22  fof(f2867,plain,(
% 6.40/1.22    k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | ~spl3_60),
% 6.40/1.22    inference(avatar_component_clause,[],[f2865])).
% 6.40/1.22  fof(f8095,plain,(
% 6.40/1.22    ( ! [X87,X86] : (k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k4_xboole_0(k10_relat_1(sK2,X87),k4_xboole_0(sK0,k2_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(forward_demodulation,[],[f8048,f43])).
% 6.40/1.22  fof(f8048,plain,(
% 6.40/1.22    ( ! [X87,X86] : (k10_relat_1(sK2,k6_subset_1(X87,k4_xboole_0(X86,X86))) = k6_subset_1(k10_relat_1(sK2,X87),k4_xboole_0(sK0,k2_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(superposition,[],[f42,f6877])).
% 6.40/1.22  fof(f42,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 6.40/1.22    inference(cnf_transformation,[],[f25])).
% 6.40/1.22  fof(f25,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 6.40/1.22    inference(flattening,[],[f24])).
% 6.40/1.22  fof(f24,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 6.40/1.22    inference(ennf_transformation,[],[f10])).
% 6.40/1.22  fof(f10,axiom,(
% 6.40/1.22    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 6.40/1.22  fof(f8067,plain,(
% 6.40/1.22    spl3_91 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10),
% 6.40/1.22    inference(avatar_split_clause,[],[f8011,f116,f76,f67,f62,f52,f8064])).
% 6.40/1.22  fof(f52,plain,(
% 6.40/1.22    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 6.40/1.22  fof(f8011,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK0) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(superposition,[],[f177,f6877])).
% 6.40/1.22  fof(f177,plain,(
% 6.40/1.22    ( ! [X0] : (k4_xboole_0(sK0,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,X0)))) ) | (~spl3_2 | ~spl3_4 | ~spl3_5)),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f64,f69,f103,f31])).
% 6.40/1.22  fof(f103,plain,(
% 6.40/1.22    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f54,f35])).
% 6.40/1.22  fof(f35,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 6.40/1.22    inference(cnf_transformation,[],[f21])).
% 6.40/1.22  fof(f21,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 6.40/1.22    inference(ennf_transformation,[],[f2])).
% 6.40/1.22  fof(f2,axiom,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 6.40/1.22  fof(f54,plain,(
% 6.40/1.22    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 6.40/1.22    inference(avatar_component_clause,[],[f52])).
% 6.40/1.22  fof(f69,plain,(
% 6.40/1.22    v1_relat_1(sK2) | ~spl3_5),
% 6.40/1.22    inference(avatar_component_clause,[],[f67])).
% 6.40/1.22  fof(f64,plain,(
% 6.40/1.22    v1_funct_1(sK2) | ~spl3_4),
% 6.40/1.22    inference(avatar_component_clause,[],[f62])).
% 6.40/1.22  fof(f8062,plain,(
% 6.40/1.22    spl3_90 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10 | ~spl3_61),
% 6.40/1.22    inference(avatar_split_clause,[],[f8057,f3182,f116,f76,f67,f62,f8059])).
% 6.40/1.22  fof(f8057,plain,(
% 6.40/1.22    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10 | ~spl3_61)),
% 6.40/1.22    inference(forward_demodulation,[],[f8010,f3184])).
% 6.40/1.22  fof(f8010,plain,(
% 6.40/1.22    k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(k2_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(superposition,[],[f86,f6877])).
% 6.40/1.22  fof(f86,plain,(
% 6.40/1.22    ( ! [X0] : (k4_xboole_0(k2_relat_1(sK2),X0) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k2_relat_1(sK2),X0)))) ) | (~spl3_4 | ~spl3_5)),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f64,f41,f69,f31])).
% 6.40/1.22  fof(f41,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.40/1.22    inference(cnf_transformation,[],[f5])).
% 6.40/1.22  fof(f5,axiom,(
% 6.40/1.22    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.40/1.22  fof(f7889,plain,(
% 6.40/1.22    spl3_89 | ~spl3_88 | ~spl3_2 | ~spl3_14),
% 6.40/1.22    inference(avatar_split_clause,[],[f7872,f150,f52,f7880,f7886])).
% 6.40/1.22  fof(f7886,plain,(
% 6.40/1.22    spl3_89 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k10_relat_1(sK2,sK1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 6.40/1.22  fof(f7880,plain,(
% 6.40/1.22    spl3_88 <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 6.40/1.22  fof(f150,plain,(
% 6.40/1.22    spl3_14 <=> k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 6.40/1.22  fof(f7872,plain,(
% 6.40/1.22    ( ! [X2] : (~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(k4_xboole_0(sK0,X2),k10_relat_1(sK2,sK1))) ) | (~spl3_2 | ~spl3_14)),
% 6.40/1.22    inference(superposition,[],[f1315,f323])).
% 6.40/1.22  fof(f323,plain,(
% 6.40/1.22    ( ! [X0,X1] : (k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k4_xboole_0(sK0,X0),X1)))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f180,f39])).
% 6.40/1.22  fof(f39,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 6.40/1.22    inference(cnf_transformation,[],[f22])).
% 6.40/1.22  fof(f22,plain,(
% 6.40/1.22    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 6.40/1.22    inference(ennf_transformation,[],[f8])).
% 6.40/1.22  fof(f8,axiom,(
% 6.40/1.22    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 6.40/1.22  fof(f180,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k2_relat_1(sK2))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f103,f35])).
% 6.40/1.22  fof(f1315,plain,(
% 6.40/1.22    ( ! [X2,X3] : (~r1_tarski(k2_xboole_0(k4_xboole_0(X2,k10_relat_1(sK2,sK0)),X3),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(X2,k10_relat_1(sK2,sK1))) ) | ~spl3_14),
% 6.40/1.22    inference(resolution,[],[f491,f33])).
% 6.40/1.22  fof(f491,plain,(
% 6.40/1.22    ( ! [X2] : (~r1_tarski(k4_xboole_0(X2,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(X2,k10_relat_1(sK2,sK1))) ) | ~spl3_14),
% 6.40/1.22    inference(superposition,[],[f32,f152])).
% 6.40/1.22  fof(f152,plain,(
% 6.40/1.22    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_14),
% 6.40/1.22    inference(avatar_component_clause,[],[f150])).
% 6.40/1.22  fof(f32,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.40/1.22    inference(cnf_transformation,[],[f18])).
% 6.40/1.22  fof(f18,plain,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.40/1.22    inference(ennf_transformation,[],[f7])).
% 6.40/1.22  fof(f7,axiom,(
% 6.40/1.22    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.40/1.22  fof(f7888,plain,(
% 6.40/1.22    spl3_89 | ~spl3_88 | ~spl3_2 | ~spl3_14),
% 6.40/1.22    inference(avatar_split_clause,[],[f7870,f150,f52,f7880,f7886])).
% 6.40/1.22  fof(f7870,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(k4_xboole_0(sK0,X0),k10_relat_1(sK2,sK1))) ) | (~spl3_2 | ~spl3_14)),
% 6.40/1.22    inference(superposition,[],[f1315,f322])).
% 6.40/1.22  fof(f322,plain,(
% 6.40/1.22    ( ! [X0,X1] : (k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k2_relat_1(sK2))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f180,f40])).
% 6.40/1.22  fof(f40,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 6.40/1.22    inference(cnf_transformation,[],[f23])).
% 6.40/1.22  fof(f23,plain,(
% 6.40/1.22    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.40/1.22    inference(ennf_transformation,[],[f4])).
% 6.40/1.22  fof(f4,axiom,(
% 6.40/1.22    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.40/1.22    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 6.40/1.22  fof(f7884,plain,(
% 6.40/1.22    spl3_87 | ~spl3_88 | ~spl3_2 | ~spl3_14),
% 6.40/1.22    inference(avatar_split_clause,[],[f7867,f150,f52,f7880,f7876])).
% 6.40/1.22  fof(f7876,plain,(
% 6.40/1.22    spl3_87 <=> r1_tarski(sK0,k10_relat_1(sK2,sK1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 6.40/1.22  fof(f7867,plain,(
% 6.40/1.22    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(sK0,k10_relat_1(sK2,sK1)) | (~spl3_2 | ~spl3_14)),
% 6.40/1.22    inference(superposition,[],[f1315,f179])).
% 6.40/1.22  fof(f179,plain,(
% 6.40/1.22    ( ! [X0] : (k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,X0)))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f103,f39])).
% 6.40/1.22  fof(f7883,plain,(
% 6.40/1.22    spl3_87 | ~spl3_88 | ~spl3_2 | ~spl3_14),
% 6.40/1.22    inference(avatar_split_clause,[],[f7866,f150,f52,f7880,f7876])).
% 6.40/1.22  fof(f7866,plain,(
% 6.40/1.22    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | r1_tarski(sK0,k10_relat_1(sK2,sK1)) | (~spl3_2 | ~spl3_14)),
% 6.40/1.22    inference(superposition,[],[f1315,f178])).
% 6.40/1.22  fof(f178,plain,(
% 6.40/1.22    ( ! [X0] : (k2_relat_1(sK2) = k2_xboole_0(k4_xboole_0(sK0,X0),k2_relat_1(sK2))) ) | ~spl3_2),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f103,f40])).
% 6.40/1.22  fof(f7494,plain,(
% 6.40/1.22    ~spl3_77 | ~spl3_6 | ~spl3_10 | spl3_67),
% 6.40/1.22    inference(avatar_split_clause,[],[f7373,f6312,f116,f76,f7375])).
% 6.40/1.22  fof(f7375,plain,(
% 6.40/1.22    spl3_77 <=> r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 6.40/1.22  fof(f7373,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_67)),
% 6.40/1.22    inference(resolution,[],[f7206,f6421])).
% 6.40/1.22  fof(f6421,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),X0)) ) | spl3_67),
% 6.40/1.22    inference(superposition,[],[f6324,f39])).
% 6.40/1.22  fof(f6324,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),sK1)) ) | spl3_67),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f6314,f33])).
% 6.40/1.22  fof(f7206,plain,(
% 6.40/1.22    ( ! [X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X1)) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(forward_demodulation,[],[f7054,f6877])).
% 6.40/1.22  fof(f7054,plain,(
% 6.40/1.22    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X0))),X1)) ) | ~spl3_6),
% 6.40/1.22    inference(superposition,[],[f6826,f77])).
% 6.40/1.22  fof(f7493,plain,(
% 6.40/1.22    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.22    inference(avatar_split_clause,[],[f7372,f116,f76,f47,f7380])).
% 6.40/1.22  fof(f7380,plain,(
% 6.40/1.22    spl3_78 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 6.40/1.22  fof(f47,plain,(
% 6.40/1.22    spl3_1 <=> r1_tarski(sK0,sK1)),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 6.40/1.22  fof(f7372,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(resolution,[],[f7206,f6302])).
% 6.40/1.22  fof(f6302,plain,(
% 6.40/1.22    ( ! [X3] : (~r1_tarski(X3,sK1) | ~r1_tarski(k4_xboole_0(sK0,X3),sK1)) ) | spl3_1),
% 6.40/1.22    inference(resolution,[],[f1374,f45])).
% 6.40/1.22  fof(f1374,plain,(
% 6.40/1.22    ( ! [X2,X3] : (~r1_tarski(X3,sK1) | ~r1_tarski(k4_xboole_0(sK0,X2),X3) | ~r1_tarski(X2,X3)) ) | spl3_1),
% 6.40/1.22    inference(superposition,[],[f210,f40])).
% 6.40/1.22  fof(f210,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),sK1) | ~r1_tarski(k4_xboole_0(sK0,X0),X1)) ) | spl3_1),
% 6.40/1.22    inference(resolution,[],[f174,f32])).
% 6.40/1.22  fof(f174,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) ) | spl3_1),
% 6.40/1.22    inference(superposition,[],[f98,f39])).
% 6.40/1.22  fof(f98,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f49,f33])).
% 6.40/1.22  fof(f49,plain,(
% 6.40/1.22    ~r1_tarski(sK0,sK1) | spl3_1),
% 6.40/1.22    inference(avatar_component_clause,[],[f47])).
% 6.40/1.22  fof(f7484,plain,(
% 6.40/1.22    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_68),
% 6.40/1.22    inference(avatar_split_clause,[],[f7343,f6329,f116,f76,f7409])).
% 6.40/1.22  fof(f7409,plain,(
% 6.40/1.22    spl3_82 <=> r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 6.40/1.22  fof(f6329,plain,(
% 6.40/1.22    spl3_68 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK1))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 6.40/1.22  fof(f7343,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_68)),
% 6.40/1.22    inference(resolution,[],[f7206,f6451])).
% 6.40/1.22  fof(f6451,plain,(
% 6.40/1.22    ( ! [X2] : (~r1_tarski(X2,k2_xboole_0(sK1,sK1)) | ~r1_tarski(sK0,X2)) ) | spl3_68),
% 6.40/1.22    inference(superposition,[],[f6350,f39])).
% 6.40/1.22  fof(f6350,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k2_xboole_0(sK1,sK1))) ) | spl3_68),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f6331,f33])).
% 6.40/1.22  fof(f6331,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | spl3_68),
% 6.40/1.22    inference(avatar_component_clause,[],[f6329])).
% 6.40/1.22  fof(f7481,plain,(
% 6.40/1.22    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.22    inference(avatar_split_clause,[],[f7336,f116,f76,f47,f7380])).
% 6.40/1.22  fof(f7336,plain,(
% 6.40/1.22    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(resolution,[],[f7206,f1412])).
% 6.40/1.22  fof(f1412,plain,(
% 6.40/1.22    ( ! [X1] : (~r1_tarski(X1,k4_xboole_0(sK0,X1)) | ~r1_tarski(k4_xboole_0(sK0,X1),sK1)) ) | spl3_1),
% 6.40/1.22    inference(superposition,[],[f1367,f40])).
% 6.40/1.22  fof(f1367,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),sK1)) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f44,f210])).
% 6.40/1.22  fof(f7480,plain,(
% 6.40/1.22    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_29),
% 6.40/1.22    inference(avatar_split_clause,[],[f7334,f872,f116,f76,f7409])).
% 6.40/1.22  fof(f872,plain,(
% 6.40/1.22    spl3_29 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK0))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 6.40/1.22  fof(f7334,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_29)),
% 6.40/1.22    inference(resolution,[],[f7206,f1362])).
% 6.40/1.22  fof(f1362,plain,(
% 6.40/1.22    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(k4_xboole_0(sK0,sK0),X3)) | ~r1_tarski(sK0,X2)) ) | spl3_29),
% 6.40/1.22    inference(superposition,[],[f966,f39])).
% 6.40/1.22  fof(f966,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,sK0),X1))) ) | spl3_29),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f939,f33])).
% 6.40/1.22  fof(f939,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK0,sK0),X0))) ) | spl3_29),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f41,f898])).
% 6.40/1.22  fof(f898,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k4_xboole_0(sK0,sK0))) ) | spl3_29),
% 6.40/1.22    inference(superposition,[],[f892,f39])).
% 6.40/1.22  fof(f892,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK0,sK0))) ) | spl3_29),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f874,f33])).
% 6.40/1.22  fof(f874,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k4_xboole_0(sK0,sK0)) | spl3_29),
% 6.40/1.22    inference(avatar_component_clause,[],[f872])).
% 6.40/1.22  fof(f7479,plain,(
% 6.40/1.22    ~spl3_82 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.22    inference(avatar_split_clause,[],[f7333,f116,f76,f47,f7409])).
% 6.40/1.22  fof(f7333,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.22    inference(resolution,[],[f7206,f1235])).
% 6.40/1.22  fof(f1235,plain,(
% 6.40/1.22    ( ! [X6,X4,X5] : (~r1_tarski(X4,k4_xboole_0(k4_xboole_0(sK1,X5),X6)) | ~r1_tarski(sK0,X4)) ) | spl3_1),
% 6.40/1.22    inference(superposition,[],[f456,f39])).
% 6.40/1.22  fof(f456,plain,(
% 6.40/1.22    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK1,X1),X2))) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f447,f33])).
% 6.40/1.22  fof(f447,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK1,X0),X1))) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f41,f271])).
% 6.40/1.22  fof(f271,plain,(
% 6.40/1.22    ( ! [X2,X1] : (~r1_tarski(sK0,X1) | ~r1_tarski(X1,k4_xboole_0(sK1,X2))) ) | spl3_1),
% 6.40/1.22    inference(superposition,[],[f214,f39])).
% 6.40/1.22  fof(f214,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK1,X1))) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f205,f33])).
% 6.40/1.22  fof(f205,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(sK1,X0))) ) | spl3_1),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f41,f174])).
% 6.40/1.22  fof(f7478,plain,(
% 6.40/1.22    ~spl3_82 | ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_19),
% 6.40/1.22    inference(avatar_split_clause,[],[f7332,f282,f116,f111,f76,f52,f7409])).
% 6.40/1.22  fof(f111,plain,(
% 6.40/1.22    spl3_9 <=> k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 6.40/1.22  fof(f282,plain,(
% 6.40/1.22    spl3_19 <=> r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.40/1.22    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 6.40/1.22  fof(f7332,plain,(
% 6.40/1.22    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_19)),
% 6.40/1.22    inference(resolution,[],[f7206,f1575])).
% 6.40/1.22  fof(f1575,plain,(
% 6.40/1.22    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(k4_xboole_0(sK0,X3),sK0)) | ~r1_tarski(sK0,X2)) ) | (~spl3_2 | ~spl3_9 | spl3_19)),
% 6.40/1.22    inference(superposition,[],[f1569,f39])).
% 6.40/1.22  fof(f1569,plain,(
% 6.40/1.22    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,X1),sK0))) ) | (~spl3_2 | ~spl3_9 | spl3_19)),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f1554,f33])).
% 6.40/1.22  fof(f1554,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,k4_xboole_0(k4_xboole_0(sK0,X0),sK0))) ) | (~spl3_2 | ~spl3_9 | spl3_19)),
% 6.40/1.22    inference(unit_resulting_resolution,[],[f827,f392])).
% 6.40/1.22  fof(f392,plain,(
% 6.40/1.22    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k4_xboole_0(k2_relat_1(sK2),sK0))) ) | spl3_19),
% 6.40/1.23    inference(superposition,[],[f292,f39])).
% 6.40/1.23  fof(f292,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),sK0))) ) | spl3_19),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f284,f33])).
% 6.40/1.23  fof(f284,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | spl3_19),
% 6.40/1.23    inference(avatar_component_clause,[],[f282])).
% 6.40/1.23  fof(f827,plain,(
% 6.40/1.23    ( ! [X0] : (r1_tarski(k4_xboole_0(k4_xboole_0(sK0,X0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))) ) | (~spl3_2 | ~spl3_9)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f103,f278])).
% 6.40/1.23  fof(f278,plain,(
% 6.40/1.23    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK2)) | r1_tarski(k4_xboole_0(X2,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))) ) | ~spl3_9),
% 6.40/1.23    inference(superposition,[],[f34,f113])).
% 6.40/1.23  fof(f113,plain,(
% 6.40/1.23    k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_9),
% 6.40/1.23    inference(avatar_component_clause,[],[f111])).
% 6.40/1.23  fof(f7469,plain,(
% 6.40/1.23    spl3_86 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7219,f116,f76,f7454])).
% 6.40/1.23  fof(f7454,plain,(
% 6.40/1.23    spl3_86 <=> k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 6.40/1.23  fof(f7219,plain,(
% 6.40/1.23    k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f7206,f38])).
% 6.40/1.23  fof(f7466,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7462,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7390,plain,(
% 6.40/1.23    spl3_80 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 6.40/1.23  fof(f7462,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(backward_demodulation,[],[f7309,f7226])).
% 6.40/1.23  fof(f7226,plain,(
% 6.40/1.23    ( ! [X0] : (k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) = k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X0)) ) | (~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f41,f7206,f38])).
% 6.40/1.23  fof(f7309,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),X0)),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))) ) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f41,f7206,f1374])).
% 6.40/1.23  fof(f7457,plain,(
% 6.40/1.23    spl3_86 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7227,f116,f76,f7454])).
% 6.40/1.23  fof(f7227,plain,(
% 6.40/1.23    k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f7206,f38])).
% 6.40/1.23  fof(f7451,plain,(
% 6.40/1.23    ~spl3_79 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7231,f116,f76,f47,f7385])).
% 6.40/1.23  fof(f7385,plain,(
% 6.40/1.23    spl3_79 <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 6.40/1.23  fof(f7231,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f49,f7206,f557])).
% 6.40/1.23  fof(f557,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2),X0) | r1_tarski(sK0,X1) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 6.40/1.23    inference(superposition,[],[f252,f39])).
% 6.40/1.23  fof(f7450,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7233,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7233,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).
% 6.40/1.23  fof(f7449,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7234,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7234,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).
% 6.40/1.23  fof(f7448,plain,(
% 6.40/1.23    ~spl3_85 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7236,f116,f76,f47,f7445])).
% 6.40/1.23  fof(f7445,plain,(
% 6.40/1.23    spl3_85 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 6.40/1.23  fof(f7236,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k4_xboole_0(sK0,k2_relat_1(sK2))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).
% 6.40/1.23  fof(f7443,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7237,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7237,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f7206,f1374])).
% 6.40/1.23  fof(f7442,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7239,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7239,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).
% 6.40/1.23  fof(f7441,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7240,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7240,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).
% 6.40/1.23  fof(f7440,plain,(
% 6.40/1.23    ~spl3_84 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7241,f116,f76,f47,f7437])).
% 6.40/1.23  fof(f7437,plain,(
% 6.40/1.23    spl3_84 <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1)),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 6.40/1.23  fof(f7241,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f1741,f7206,f1374])).
% 6.40/1.23  fof(f1741,plain,(
% 6.40/1.23    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_relat_1(sK2),X0))) ) | ~spl3_10),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f1725,f34])).
% 6.40/1.23  fof(f1725,plain,(
% 6.40/1.23    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,k4_xboole_0(k2_relat_1(sK2),X0)))) ) | ~spl3_10),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f251])).
% 6.40/1.23  fof(f251,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(k2_relat_1(sK2),X0),X1) | r1_tarski(sK0,k2_xboole_0(X0,X1))) ) | ~spl3_10),
% 6.40/1.23    inference(resolution,[],[f194,f32])).
% 6.40/1.23  fof(f7435,plain,(
% 6.40/1.23    ~spl3_82 | ~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_19),
% 6.40/1.23    inference(avatar_split_clause,[],[f7251,f282,f116,f111,f76,f52,f7409])).
% 6.40/1.23  fof(f7251,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_2 | ~spl3_6 | ~spl3_9 | ~spl3_10 | spl3_19)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f1575])).
% 6.40/1.23  fof(f7434,plain,(
% 6.40/1.23    ~spl3_82 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7252,f116,f76,f47,f7409])).
% 6.40/1.23  fof(f7252,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f1235])).
% 6.40/1.23  fof(f7433,plain,(
% 6.40/1.23    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_29),
% 6.40/1.23    inference(avatar_split_clause,[],[f7253,f872,f116,f76,f7409])).
% 6.40/1.23  fof(f7253,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_29)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f1362])).
% 6.40/1.23  fof(f7432,plain,(
% 6.40/1.23    ~spl3_79 | ~spl3_6 | ~spl3_10 | spl3_21),
% 6.40/1.23    inference(avatar_split_clause,[],[f7254,f295,f116,f76,f7385])).
% 6.40/1.23  fof(f295,plain,(
% 6.40/1.23    spl3_21 <=> r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 6.40/1.23  fof(f7254,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_21)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f793])).
% 6.40/1.23  fof(f793,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(X0,k4_xboole_0(k2_relat_1(sK2),sK0))) ) | spl3_21),
% 6.40/1.23    inference(superposition,[],[f299,f39])).
% 6.40/1.23  fof(f299,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(k2_relat_1(sK2),sK0))) ) | spl3_21),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f297,f33])).
% 6.40/1.23  fof(f297,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0)) | spl3_21),
% 6.40/1.23    inference(avatar_component_clause,[],[f295])).
% 6.40/1.23  fof(f7431,plain,(
% 6.40/1.23    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_19),
% 6.40/1.23    inference(avatar_split_clause,[],[f7256,f282,f116,f76,f7409])).
% 6.40/1.23  fof(f7256,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_19)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f392])).
% 6.40/1.23  fof(f7430,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7257,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7257,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f1412])).
% 6.40/1.23  fof(f7429,plain,(
% 6.40/1.23    ~spl3_79 | ~spl3_6 | ~spl3_10 | spl3_13),
% 6.40/1.23    inference(avatar_split_clause,[],[f7259,f133,f116,f76,f7385])).
% 6.40/1.23  fof(f133,plain,(
% 6.40/1.23    spl3_13 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 6.40/1.23  fof(f7259,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_13)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f438])).
% 6.40/1.23  fof(f438,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(X0,k4_xboole_0(sK0,X1))) ) | spl3_13),
% 6.40/1.23    inference(superposition,[],[f266,f39])).
% 6.40/1.23  fof(f266,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(sK0,X1))) ) | spl3_13),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f259,f33])).
% 6.40/1.23  fof(f259,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),k4_xboole_0(sK0,X0))) ) | spl3_13),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f41,f190])).
% 6.40/1.23  fof(f190,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(X0,sK0)) ) | spl3_13),
% 6.40/1.23    inference(superposition,[],[f138,f39])).
% 6.40/1.23  fof(f138,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),sK0)) ) | spl3_13),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f135,f33])).
% 6.40/1.23  fof(f135,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_13),
% 6.40/1.23    inference(avatar_component_clause,[],[f133])).
% 6.40/1.23  fof(f7428,plain,(
% 6.40/1.23    ~spl3_82 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7260,f116,f76,f47,f7409])).
% 6.40/1.23  fof(f7260,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f675])).
% 6.40/1.23  fof(f675,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,k4_xboole_0(sK0,k2_relat_1(sK2)))) ) | (spl3_1 | ~spl3_10)),
% 6.40/1.23    inference(superposition,[],[f604,f39])).
% 6.40/1.23  fof(f604,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k4_xboole_0(sK0,k2_relat_1(sK2)))) ) | (spl3_1 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f211])).
% 6.40/1.23  fof(f211,plain,(
% 6.40/1.23    ( ! [X2,X3] : (~r1_tarski(X2,sK1) | ~r1_tarski(k2_xboole_0(sK0,X3),X2)) ) | spl3_1),
% 6.40/1.23    inference(resolution,[],[f174,f33])).
% 6.40/1.23  fof(f7427,plain,(
% 6.40/1.23    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_29),
% 6.40/1.23    inference(avatar_split_clause,[],[f7262,f872,f116,f76,f7409])).
% 6.40/1.23  fof(f7262,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_29)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f898])).
% 6.40/1.23  fof(f7426,plain,(
% 6.40/1.23    ~spl3_79 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7266,f116,f76,f47,f7385])).
% 6.40/1.23  fof(f7266,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f434])).
% 6.40/1.23  fof(f434,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(X0,k4_xboole_0(sK1,X1))) ) | (spl3_1 | ~spl3_10)),
% 6.40/1.23    inference(superposition,[],[f255,f39])).
% 6.40/1.23  fof(f255,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),k4_xboole_0(sK1,X1))) ) | (spl3_1 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f248,f33])).
% 6.40/1.23  fof(f248,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),k4_xboole_0(sK1,X0))) ) | (spl3_1 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f205,f194])).
% 6.40/1.23  fof(f7425,plain,(
% 6.40/1.23    ~spl3_82 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7267,f116,f76,f47,f7409])).
% 6.40/1.23  fof(f7267,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f271])).
% 6.40/1.23  fof(f7424,plain,(
% 6.40/1.23    ~spl3_82 | ~spl3_6 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f7271,f6329,f116,f76,f7409])).
% 6.40/1.23  fof(f7271,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f6451])).
% 6.40/1.23  fof(f7422,plain,(
% 6.40/1.23    spl3_83 | ~spl3_6 | ~spl3_9 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7277,f116,f111,f76,f7419])).
% 6.40/1.23  fof(f7419,plain,(
% 6.40/1.23    spl3_83 <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 6.40/1.23  fof(f7277,plain,(
% 6.40/1.23    r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_6 | ~spl3_9 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f278])).
% 6.40/1.23  fof(f7413,plain,(
% 6.40/1.23    ~spl3_79 | ~spl3_6 | ~spl3_10 | spl3_13),
% 6.40/1.23    inference(avatar_split_clause,[],[f7290,f133,f116,f76,f7385])).
% 6.40/1.23  fof(f7290,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_13)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f190])).
% 6.40/1.23  fof(f7412,plain,(
% 6.40/1.23    ~spl3_82 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7297,f116,f76,f47,f7409])).
% 6.40/1.23  fof(f7297,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f174])).
% 6.40/1.23  fof(f7407,plain,(
% 6.40/1.23    ~spl3_79 | ~spl3_6 | ~spl3_10 | spl3_18),
% 6.40/1.23    inference(avatar_split_clause,[],[f7299,f197,f116,f76,f7385])).
% 6.40/1.23  fof(f197,plain,(
% 6.40/1.23    spl3_18 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 6.40/1.23  fof(f7299,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_18)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f232])).
% 6.40/1.23  fof(f232,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r1_tarski(X0,sK1)) ) | spl3_18),
% 6.40/1.23    inference(superposition,[],[f201,f39])).
% 6.40/1.23  fof(f201,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k2_xboole_0(k2_relat_1(sK2),X0),sK1)) ) | spl3_18),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f199,f33])).
% 6.40/1.23  fof(f199,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_18),
% 6.40/1.23    inference(avatar_component_clause,[],[f197])).
% 6.40/1.23  fof(f7406,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7405,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7405,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(forward_demodulation,[],[f7304,f596])).
% 6.40/1.23  fof(f596,plain,(
% 6.40/1.23    ( ! [X0] : (k4_xboole_0(sK0,k2_relat_1(sK2)) = k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0)) ) | ~spl3_10),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f41,f562,f38])).
% 6.40/1.23  fof(f7304,plain,(
% 6.40/1.23    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))) ) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f427,f7206,f1374])).
% 6.40/1.23  fof(f427,plain,(
% 6.40/1.23    ( ! [X2,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(X1,X2)),k10_relat_1(sK2,X1))) ) | ~spl3_6),
% 6.40/1.23    inference(superposition,[],[f41,f77])).
% 6.40/1.23  fof(f7404,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7403,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7403,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(forward_demodulation,[],[f7402,f596])).
% 6.40/1.23  fof(f7402,plain,(
% 6.40/1.23    ( ! [X1] : (~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X1))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))) ) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(forward_demodulation,[],[f7305,f596])).
% 6.40/1.23  fof(f7305,plain,(
% 6.40/1.23    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0),X1))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))) ) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f955,f7206,f1374])).
% 6.40/1.23  fof(f955,plain,(
% 6.40/1.23    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(X0,X1),X2)),k10_relat_1(sK2,X0))) ) | ~spl3_6),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f427,f429])).
% 6.40/1.23  fof(f429,plain,(
% 6.40/1.23    ( ! [X6,X7,X5] : (~r1_tarski(k10_relat_1(sK2,X5),X7) | r1_tarski(k10_relat_1(sK2,k4_xboole_0(X5,X6)),X7)) ) | ~spl3_6),
% 6.40/1.23    inference(superposition,[],[f35,f77])).
% 6.40/1.23  fof(f7400,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7307,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7307,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f7206,f1374])).
% 6.40/1.23  fof(f7399,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7308,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7308,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f7206,f1374])).
% 6.40/1.23  fof(f7398,plain,(
% 6.40/1.23    ~spl3_81 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7310,f116,f76,f47,f7395])).
% 6.40/1.23  fof(f7395,plain,(
% 6.40/1.23    spl3_81 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 6.40/1.23  fof(f7310,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).
% 6.40/1.23  fof(f7393,plain,(
% 6.40/1.23    ~spl3_80 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7311,f116,f76,f47,f7390])).
% 6.40/1.23  fof(f7311,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f7206,f1374])).
% 6.40/1.23  fof(f7388,plain,(
% 6.40/1.23    ~spl3_79 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7312,f116,f76,f47,f7385])).
% 6.40/1.23  fof(f7312,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f7206,f1374])).
% 6.40/1.23  fof(f7383,plain,(
% 6.40/1.23    ~spl3_78 | spl3_1 | ~spl3_6 | ~spl3_10),
% 6.40/1.23    inference(avatar_split_clause,[],[f7320,f116,f76,f47,f7380])).
% 6.40/1.23  fof(f7320,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_10)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f6302])).
% 6.40/1.23  fof(f7378,plain,(
% 6.40/1.23    ~spl3_77 | ~spl3_6 | ~spl3_10 | spl3_67),
% 6.40/1.23    inference(avatar_split_clause,[],[f7321,f6312,f116,f76,f7375])).
% 6.40/1.23  fof(f7321,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_6 | ~spl3_10 | spl3_67)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f7206,f6421])).
% 6.40/1.23  fof(f7120,plain,(
% 6.40/1.23    ~spl3_76 | ~spl3_6 | ~spl3_10 | spl3_54),
% 6.40/1.23    inference(avatar_split_clause,[],[f7101,f2516,f116,f76,f7117])).
% 6.40/1.23  fof(f7117,plain,(
% 6.40/1.23    spl3_76 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 6.40/1.23  fof(f2516,plain,(
% 6.40/1.23    spl3_54 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 6.40/1.23  fof(f7101,plain,(
% 6.40/1.23    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_6 | ~spl3_10 | spl3_54)),
% 6.40/1.23    inference(backward_demodulation,[],[f2518,f6877])).
% 6.40/1.23  fof(f2518,plain,(
% 6.40/1.23    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))) | spl3_54),
% 6.40/1.23    inference(avatar_component_clause,[],[f2516])).
% 6.40/1.23  fof(f7115,plain,(
% 6.40/1.23    spl3_75 | ~spl3_6 | ~spl3_10 | ~spl3_51),
% 6.40/1.23    inference(avatar_split_clause,[],[f7099,f2495,f116,f76,f7112])).
% 6.40/1.23  fof(f7112,plain,(
% 6.40/1.23    spl3_75 <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 6.40/1.23  fof(f2495,plain,(
% 6.40/1.23    spl3_51 <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 6.40/1.23  fof(f7099,plain,(
% 6.40/1.23    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | (~spl3_6 | ~spl3_10 | ~spl3_51)),
% 6.40/1.23    inference(backward_demodulation,[],[f2497,f6877])).
% 6.40/1.23  fof(f2497,plain,(
% 6.40/1.23    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | ~spl3_51),
% 6.40/1.23    inference(avatar_component_clause,[],[f2495])).
% 6.40/1.23  fof(f6772,plain,(
% 6.40/1.23    ~spl3_74 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6740,f6698,f116,f6769])).
% 6.40/1.23  fof(f6769,plain,(
% 6.40/1.23    spl3_74 <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 6.40/1.23  fof(f6698,plain,(
% 6.40/1.23    spl3_72 <=> r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 6.40/1.23  fof(f6740,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6700,f251])).
% 6.40/1.23  fof(f6700,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | spl3_72),
% 6.40/1.23    inference(avatar_component_clause,[],[f6698])).
% 6.40/1.23  fof(f6767,plain,(
% 6.40/1.23    ~spl3_73 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6743,f6698,f116,f6760])).
% 6.40/1.23  fof(f6760,plain,(
% 6.40/1.23    spl3_73 <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2))))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 6.40/1.23  fof(f6743,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f6700,f557])).
% 6.40/1.23  fof(f6766,plain,(
% 6.40/1.23    ~spl3_73 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6744,f6698,f116,f6760])).
% 6.40/1.23  fof(f6744,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f6700,f557])).
% 6.40/1.23  fof(f6765,plain,(
% 6.40/1.23    ~spl3_73 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6747,f6698,f116,f6760])).
% 6.40/1.23  fof(f6747,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f6700,f557])).
% 6.40/1.23  fof(f6764,plain,(
% 6.40/1.23    ~spl3_73 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6748,f6698,f116,f6760])).
% 6.40/1.23  fof(f6748,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f6700,f557])).
% 6.40/1.23  fof(f6763,plain,(
% 6.40/1.23    ~spl3_73 | ~spl3_10 | spl3_72),
% 6.40/1.23    inference(avatar_split_clause,[],[f6753,f6698,f116,f6760])).
% 6.40/1.23  fof(f6753,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | (~spl3_10 | spl3_72)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6700,f194])).
% 6.40/1.23  fof(f6702,plain,(
% 6.40/1.23    ~spl3_72 | spl3_71),
% 6.40/1.23    inference(avatar_split_clause,[],[f6695,f6548,f6698])).
% 6.40/1.23  fof(f6695,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | spl3_71),
% 6.40/1.23    inference(resolution,[],[f6550,f34])).
% 6.40/1.23  fof(f6701,plain,(
% 6.40/1.23    ~spl3_72 | spl3_71),
% 6.40/1.23    inference(avatar_split_clause,[],[f6692,f6548,f6698])).
% 6.40/1.23  fof(f6692,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_relat_1(sK2)))) | spl3_71),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6550,f34])).
% 6.40/1.23  fof(f6552,plain,(
% 6.40/1.23    ~spl3_71 | ~spl3_10 | spl3_67),
% 6.40/1.23    inference(avatar_split_clause,[],[f6546,f6312,f116,f6548])).
% 6.40/1.23  fof(f6546,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_10 | spl3_67)),
% 6.40/1.23    inference(resolution,[],[f6421,f562])).
% 6.40/1.23  fof(f6551,plain,(
% 6.40/1.23    ~spl3_71 | ~spl3_10 | spl3_67),
% 6.40/1.23    inference(avatar_split_clause,[],[f6526,f6312,f116,f6548])).
% 6.40/1.23  fof(f6526,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_10 | spl3_67)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f562,f6421])).
% 6.40/1.23  fof(f6505,plain,(
% 6.40/1.23    spl3_34 | spl3_66 | ~spl3_3 | ~spl3_7),
% 6.40/1.23    inference(avatar_split_clause,[],[f6500,f80,f57,f4201,f1062])).
% 6.40/1.23  fof(f1062,plain,(
% 6.40/1.23    spl3_34 <=> ! [X7] : k4_xboole_0(k10_relat_1(sK2,sK0),X7) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X7)))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 6.40/1.23  fof(f4201,plain,(
% 6.40/1.23    spl3_66 <=> ! [X12] : ~r1_tarski(k2_xboole_0(X12,k10_relat_1(sK2,sK1)),k2_relat_1(sK2))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 6.40/1.23  fof(f57,plain,(
% 6.40/1.23    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 6.40/1.23  fof(f80,plain,(
% 6.40/1.23    spl3_7 <=> ! [X2] : (~r1_tarski(X2,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2)),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 6.40/1.23  fof(f6500,plain,(
% 6.40/1.23    ( ! [X39,X40] : (~r1_tarski(k2_xboole_0(X39,k10_relat_1(sK2,sK1)),k2_relat_1(sK2)) | k4_xboole_0(k10_relat_1(sK2,sK0),X40) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X40)))) ) | (~spl3_3 | ~spl3_7)),
% 6.40/1.23    inference(superposition,[],[f1160,f503])).
% 6.40/1.23  fof(f503,plain,(
% 6.40/1.23    ( ! [X0] : (k2_xboole_0(X0,k10_relat_1(sK2,sK1)) = k2_xboole_0(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1)))) ) | ~spl3_3),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f310,f40])).
% 6.40/1.23  fof(f310,plain,(
% 6.40/1.23    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(X0,k10_relat_1(sK2,sK1)))) ) | ~spl3_3),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f142,f32])).
% 6.40/1.23  fof(f142,plain,(
% 6.40/1.23    ( ! [X0] : (r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))) ) | ~spl3_3),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f59,f35])).
% 6.40/1.23  fof(f59,plain,(
% 6.40/1.23    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 6.40/1.23    inference(avatar_component_clause,[],[f57])).
% 6.40/1.23  fof(f1160,plain,(
% 6.40/1.23    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X2),k2_relat_1(sK2)) | k4_xboole_0(X0,X1) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X1)))) ) | ~spl3_7),
% 6.40/1.23    inference(resolution,[],[f358,f33])).
% 6.40/1.23  fof(f358,plain,(
% 6.40/1.23    ( ! [X2,X3] : (~r1_tarski(X2,k2_relat_1(sK2)) | k4_xboole_0(X2,X3) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X2,X3)))) ) | ~spl3_7),
% 6.40/1.23    inference(resolution,[],[f81,f35])).
% 6.40/1.23  fof(f81,plain,(
% 6.40/1.23    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2) ) | ~spl3_7),
% 6.40/1.23    inference(avatar_component_clause,[],[f80])).
% 6.40/1.23  fof(f6367,plain,(
% 6.40/1.23    ~spl3_70 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6335,f6329,f116,f6364])).
% 6.40/1.23  fof(f6364,plain,(
% 6.40/1.23    spl3_70 <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),sK1)),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 6.40/1.23  fof(f6335,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK1),sK1) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6331,f251])).
% 6.40/1.23  fof(f6362,plain,(
% 6.40/1.23    ~spl3_69 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6338,f6329,f116,f6355])).
% 6.40/1.23  fof(f6355,plain,(
% 6.40/1.23    spl3_69 <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1))),
% 6.40/1.23    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 6.40/1.23  fof(f6338,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f6331,f557])).
% 6.40/1.23  fof(f6361,plain,(
% 6.40/1.23    ~spl3_69 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6339,f6329,f116,f6355])).
% 6.40/1.23  fof(f6339,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f6331,f557])).
% 6.40/1.23  fof(f6360,plain,(
% 6.40/1.23    ~spl3_69 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6342,f6329,f116,f6355])).
% 6.40/1.23  fof(f6342,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f6331,f557])).
% 6.40/1.23  fof(f6359,plain,(
% 6.40/1.23    ~spl3_69 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6343,f6329,f116,f6355])).
% 6.40/1.23  fof(f6343,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f6331,f557])).
% 6.40/1.23  fof(f6358,plain,(
% 6.40/1.23    ~spl3_69 | ~spl3_10 | spl3_68),
% 6.40/1.23    inference(avatar_split_clause,[],[f6348,f6329,f116,f6355])).
% 6.40/1.23  fof(f6348,plain,(
% 6.40/1.23    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK1,sK1)) | (~spl3_10 | spl3_68)),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6331,f194])).
% 6.40/1.23  fof(f6333,plain,(
% 6.40/1.23    ~spl3_68 | spl3_67),
% 6.40/1.23    inference(avatar_split_clause,[],[f6326,f6312,f6329])).
% 6.40/1.23  fof(f6326,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | spl3_67),
% 6.40/1.23    inference(resolution,[],[f6314,f34])).
% 6.40/1.23  fof(f6332,plain,(
% 6.40/1.23    ~spl3_68 | spl3_67),
% 6.40/1.23    inference(avatar_split_clause,[],[f6323,f6312,f6329])).
% 6.40/1.23  fof(f6323,plain,(
% 6.40/1.23    ~r1_tarski(sK0,k2_xboole_0(sK1,sK1)) | spl3_67),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f6314,f34])).
% 6.40/1.23  fof(f6318,plain,(
% 6.40/1.23    ~spl3_67 | spl3_1),
% 6.40/1.23    inference(avatar_split_clause,[],[f6078,f47,f6312])).
% 6.40/1.23  fof(f6078,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl3_1),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f45,f1374])).
% 6.40/1.23  fof(f6317,plain,(
% 6.40/1.23    ~spl3_67 | spl3_1),
% 6.40/1.23    inference(avatar_split_clause,[],[f6079,f47,f6312])).
% 6.40/1.23  fof(f6079,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl3_1),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f44,f45,f1374])).
% 6.40/1.23  fof(f6316,plain,(
% 6.40/1.23    ~spl3_67 | spl3_1),
% 6.40/1.23    inference(avatar_split_clause,[],[f6082,f47,f6312])).
% 6.40/1.23  fof(f6082,plain,(
% 6.40/1.23    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl3_1),
% 6.40/1.23    inference(unit_resulting_resolution,[],[f45,f44,f1374])).
% 6.40/1.23  fof(f6315,plain,(
% 6.40/1.23    ~spl3_67 | spl3_1),
% 6.40/1.23    inference(avatar_split_clause,[],[f6083,f47,f6312])).
% 6.81/1.25  fof(f6083,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(sK0,sK1),sK1) | spl3_1),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f44,f44,f1374])).
% 6.81/1.25  fof(f4203,plain,(
% 6.81/1.25    spl3_36 | spl3_66 | ~spl3_3 | ~spl3_7),
% 6.81/1.25    inference(avatar_split_clause,[],[f4196,f80,f57,f4201,f1070])).
% 6.81/1.25  fof(f1070,plain,(
% 6.81/1.25    spl3_36 <=> k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 6.81/1.25  fof(f4196,plain,(
% 6.81/1.25    ( ! [X12] : (~r1_tarski(k2_xboole_0(X12,k10_relat_1(sK2,sK1)),k2_relat_1(sK2)) | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0)))) ) | (~spl3_3 | ~spl3_7)),
% 6.81/1.25    inference(superposition,[],[f355,f503])).
% 6.81/1.25  fof(f355,plain,(
% 6.81/1.25    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_7),
% 6.81/1.25    inference(resolution,[],[f81,f33])).
% 6.81/1.25  fof(f3771,plain,(
% 6.81/1.25    ~spl3_65 | spl3_1 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f3766,f116,f47,f3768])).
% 6.81/1.25  fof(f3768,plain,(
% 6.81/1.25    spl3_65 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 6.81/1.25  fof(f3766,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),k4_xboole_0(sK0,k2_relat_1(sK2))) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(superposition,[],[f2701,f588])).
% 6.81/1.25  fof(f588,plain,(
% 6.81/1.25    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,k2_relat_1(sK2)),X0) = X0) ) | ~spl3_10),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f40])).
% 6.81/1.25  fof(f2701,plain,(
% 6.81/1.25    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),k4_xboole_0(sK0,k2_relat_1(sK2)))) ) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f1520])).
% 6.81/1.25  fof(f1520,plain,(
% 6.81/1.25    ( ! [X0,X1] : (~r1_tarski(X1,sK1) | ~r1_tarski(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),X1)) ) | spl3_1),
% 6.81/1.25    inference(superposition,[],[f1409,f39])).
% 6.81/1.25  fof(f1409,plain,(
% 6.81/1.25    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(X0,k4_xboole_0(sK0,X0)),X1),sK1)) ) | spl3_1),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1367,f33])).
% 6.81/1.25  fof(f3345,plain,(
% 6.81/1.25    spl3_64 | ~spl3_6 | ~spl3_33),
% 6.81/1.25    inference(avatar_split_clause,[],[f3335,f984,f76,f3342])).
% 6.81/1.25  fof(f3342,plain,(
% 6.81/1.25    spl3_64 <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k2_xboole_0(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 6.81/1.25  fof(f984,plain,(
% 6.81/1.25    spl3_33 <=> k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 6.81/1.25  fof(f3335,plain,(
% 6.81/1.25    k10_relat_1(sK2,k2_relat_1(sK2)) = k2_xboole_0(k10_relat_1(sK2,k2_relat_1(sK2)),k10_relat_1(sK2,k2_relat_1(sK2))) | (~spl3_6 | ~spl3_33)),
% 6.81/1.25    inference(superposition,[],[f524,f986])).
% 6.81/1.25  fof(f986,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))) | ~spl3_33),
% 6.81/1.25    inference(avatar_component_clause,[],[f984])).
% 6.81/1.25  fof(f524,plain,(
% 6.81/1.25    ( ! [X0,X1] : (k10_relat_1(sK2,X0) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(X0,X1)),k10_relat_1(sK2,X0))) ) | ~spl3_6),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f427,f40])).
% 6.81/1.25  fof(f3305,plain,(
% 6.81/1.25    spl3_63 | ~spl3_6 | ~spl3_60),
% 6.81/1.25    inference(avatar_split_clause,[],[f3293,f2865,f76,f3302])).
% 6.81/1.25  fof(f3302,plain,(
% 6.81/1.25    spl3_63 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k10_relat_1(sK2,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 6.81/1.25  fof(f3293,plain,(
% 6.81/1.25    r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))),k10_relat_1(sK2,k10_relat_1(sK2,sK0))) | (~spl3_6 | ~spl3_60)),
% 6.81/1.25    inference(superposition,[],[f532,f2867])).
% 6.81/1.25  fof(f532,plain,(
% 6.81/1.25    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X0,X1))),k10_relat_1(sK2,k10_relat_1(sK2,X0)))) ) | ~spl3_6),
% 6.81/1.25    inference(superposition,[],[f427,f77])).
% 6.81/1.25  fof(f3209,plain,(
% 6.81/1.25    ~spl3_62 | ~spl3_4 | ~spl3_5 | spl3_61 | ~spl3_60),
% 6.81/1.25    inference(avatar_split_clause,[],[f3179,f2865,f3182,f67,f62,f3206])).
% 6.81/1.25  fof(f3206,plain,(
% 6.81/1.25    spl3_62 <=> r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 6.81/1.25  fof(f3179,plain,(
% 6.81/1.25    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r1_tarski(k4_xboole_0(sK0,sK1),k2_relat_1(sK2)) | ~spl3_60),
% 6.81/1.25    inference(superposition,[],[f31,f2867])).
% 6.81/1.25  fof(f3185,plain,(
% 6.81/1.25    spl3_61 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_60),
% 6.81/1.25    inference(avatar_split_clause,[],[f3155,f2865,f67,f62,f52,f3182])).
% 6.81/1.25  fof(f3155,plain,(
% 6.81/1.25    k4_xboole_0(sK0,sK1) = k9_relat_1(sK2,k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_60)),
% 6.81/1.25    inference(superposition,[],[f177,f2867])).
% 6.81/1.25  fof(f2881,plain,(
% 6.81/1.25    ~spl3_59 | spl3_1 | ~spl3_6 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2815,f155,f76,f47,f2856])).
% 6.81/1.25  fof(f2856,plain,(
% 6.81/1.25    spl3_59 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 6.81/1.25  fof(f155,plain,(
% 6.81/1.25    spl3_15 <=> k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 6.81/1.25  fof(f2815,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_15)),
% 6.81/1.25    inference(resolution,[],[f2744,f1412])).
% 6.81/1.25  fof(f2744,plain,(
% 6.81/1.25    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),X0)) ) | (~spl3_6 | ~spl3_15)),
% 6.81/1.25    inference(forward_demodulation,[],[f2722,f77])).
% 6.81/1.25  fof(f2722,plain,(
% 6.81/1.25    ( ! [X0] : (r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),X0)) ) | ~spl3_15),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2713,f34])).
% 6.81/1.25  fof(f2713,plain,(
% 6.81/1.25    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))) ) | ~spl3_15),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f44,f648])).
% 6.81/1.25  fof(f648,plain,(
% 6.81/1.25    ( ! [X2,X3] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X3),X2) | r1_tarski(k10_relat_1(sK2,sK0),X2)) ) | ~spl3_15),
% 6.81/1.25    inference(resolution,[],[f395,f33])).
% 6.81/1.25  fof(f395,plain,(
% 6.81/1.25    ( ! [X1] : (~r1_tarski(k10_relat_1(sK2,sK1),X1) | r1_tarski(k10_relat_1(sK2,sK0),X1)) ) | ~spl3_15),
% 6.81/1.25    inference(superposition,[],[f33,f157])).
% 6.81/1.25  fof(f157,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_15),
% 6.81/1.25    inference(avatar_component_clause,[],[f155])).
% 6.81/1.25  fof(f2875,plain,(
% 6.81/1.25    ~spl3_56 | spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2752,f155,f116,f76,f47,f2836])).
% 6.81/1.25  fof(f2836,plain,(
% 6.81/1.25    spl3_56 <=> r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 6.81/1.25  fof(f2752,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f49,f2744,f557])).
% 6.81/1.25  fof(f2873,plain,(
% 6.81/1.25    spl3_60 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2761,f155,f116,f76,f2865])).
% 6.81/1.25  fof(f2761,plain,(
% 6.81/1.25    k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_10 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f2744,f38])).
% 6.81/1.25  fof(f2868,plain,(
% 6.81/1.25    spl3_60 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2769,f155,f116,f76,f2865])).
% 6.81/1.25  fof(f2769,plain,(
% 6.81/1.25    k4_xboole_0(sK0,k2_relat_1(sK2)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) | (~spl3_6 | ~spl3_10 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f2744,f38])).
% 6.81/1.25  fof(f2863,plain,(
% 6.81/1.25    ~spl3_56 | spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2773,f155,f116,f76,f47,f2836])).
% 6.81/1.25  fof(f2773,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f434])).
% 6.81/1.25  fof(f2862,plain,(
% 6.81/1.25    ~spl3_57 | spl3_1 | ~spl3_6 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2774,f155,f76,f47,f2841])).
% 6.81/1.25  fof(f2841,plain,(
% 6.81/1.25    spl3_57 <=> r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 6.81/1.25  fof(f2774,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_6 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f271])).
% 6.81/1.25  fof(f2861,plain,(
% 6.81/1.25    ~spl3_56 | ~spl3_6 | ~spl3_15 | spl3_21),
% 6.81/1.25    inference(avatar_split_clause,[],[f2775,f295,f155,f76,f2836])).
% 6.81/1.25  fof(f2775,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | ~spl3_15 | spl3_21)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f793])).
% 6.81/1.25  fof(f2860,plain,(
% 6.81/1.25    ~spl3_57 | ~spl3_6 | ~spl3_15 | spl3_19),
% 6.81/1.25    inference(avatar_split_clause,[],[f2777,f282,f155,f76,f2841])).
% 6.81/1.25  fof(f2777,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | ~spl3_15 | spl3_19)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f392])).
% 6.81/1.25  fof(f2859,plain,(
% 6.81/1.25    ~spl3_59 | spl3_1 | ~spl3_6 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2778,f155,f76,f47,f2856])).
% 6.81/1.25  fof(f2778,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))),sK1) | (spl3_1 | ~spl3_6 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f1412])).
% 6.81/1.25  fof(f2854,plain,(
% 6.81/1.25    ~spl3_56 | ~spl3_6 | spl3_13 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2779,f155,f133,f76,f2836])).
% 6.81/1.25  fof(f2779,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | spl3_13 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f438])).
% 6.81/1.25  fof(f2853,plain,(
% 6.81/1.25    ~spl3_57 | spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2780,f155,f116,f76,f47,f2841])).
% 6.81/1.25  fof(f2780,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_6 | ~spl3_10 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f675])).
% 6.81/1.25  fof(f2852,plain,(
% 6.81/1.25    ~spl3_57 | ~spl3_6 | ~spl3_15 | spl3_29),
% 6.81/1.25    inference(avatar_split_clause,[],[f2781,f872,f155,f76,f2841])).
% 6.81/1.25  fof(f2781,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | ~spl3_15 | spl3_29)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f898])).
% 6.81/1.25  fof(f2850,plain,(
% 6.81/1.25    spl3_58 | ~spl3_6 | ~spl3_9 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2789,f155,f111,f76,f2847])).
% 6.81/1.25  fof(f2847,plain,(
% 6.81/1.25    spl3_58 <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 6.81/1.25  fof(f2789,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK1)),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_6 | ~spl3_9 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f278])).
% 6.81/1.25  fof(f2845,plain,(
% 6.81/1.25    ~spl3_56 | ~spl3_6 | spl3_13 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2794,f155,f133,f76,f2836])).
% 6.81/1.25  fof(f2794,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | spl3_13 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f190])).
% 6.81/1.25  fof(f2844,plain,(
% 6.81/1.25    ~spl3_57 | spl3_1 | ~spl3_6 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2795,f155,f76,f47,f2841])).
% 6.81/1.25  fof(f2795,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (spl3_1 | ~spl3_6 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f174])).
% 6.81/1.25  fof(f2839,plain,(
% 6.81/1.25    ~spl3_56 | ~spl3_6 | ~spl3_15 | spl3_18),
% 6.81/1.25    inference(avatar_split_clause,[],[f2797,f197,f155,f76,f2836])).
% 6.81/1.25  fof(f2797,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k10_relat_1(sK2,k4_xboole_0(sK0,sK1))) | (~spl3_6 | ~spl3_15 | spl3_18)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2744,f232])).
% 6.81/1.25  fof(f2747,plain,(
% 6.81/1.25    spl3_55 | ~spl3_6 | ~spl3_7 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2746,f155,f80,f76,f2740])).
% 6.81/1.25  fof(f2740,plain,(
% 6.81/1.25    spl3_55 <=> k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1))))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 6.81/1.25  fof(f2746,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))) | (~spl3_6 | ~spl3_7 | ~spl3_15)),
% 6.81/1.25    inference(forward_demodulation,[],[f2730,f77])).
% 6.81/1.25  fof(f2730,plain,(
% 6.81/1.25    k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) | (~spl3_7 | ~spl3_15)),
% 6.81/1.25    inference(resolution,[],[f2713,f359])).
% 6.81/1.25  fof(f359,plain,(
% 6.81/1.25    ( ! [X4,X5] : (~r1_tarski(X4,k2_xboole_0(X5,k2_relat_1(sK2))) | k4_xboole_0(X4,X5) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(X4,X5)))) ) | ~spl3_7),
% 6.81/1.25    inference(resolution,[],[f81,f34])).
% 6.81/1.25  fof(f2743,plain,(
% 6.81/1.25    spl3_55 | ~spl3_6 | ~spl3_7 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f2738,f155,f80,f76,f2740])).
% 6.81/1.25  fof(f2738,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(sK0,sK1)))) | (~spl3_6 | ~spl3_7 | ~spl3_15)),
% 6.81/1.25    inference(forward_demodulation,[],[f2723,f77])).
% 6.81/1.25  fof(f2723,plain,(
% 6.81/1.25    k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) | (~spl3_7 | ~spl3_15)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f2713,f359])).
% 6.81/1.25  fof(f2520,plain,(
% 6.81/1.25    spl3_53 | ~spl3_54 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2491,f1265,f2516,f2512])).
% 6.81/1.25  fof(f2512,plain,(
% 6.81/1.25    spl3_53 <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 6.81/1.25  fof(f1265,plain,(
% 6.81/1.25    spl3_43 <=> r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 6.81/1.25  fof(f2491,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))) | k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0)) | ~spl3_43),
% 6.81/1.25    inference(resolution,[],[f1267,f38])).
% 6.81/1.25  fof(f1267,plain,(
% 6.81/1.25    r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_43),
% 6.81/1.25    inference(avatar_component_clause,[],[f1265])).
% 6.81/1.25  fof(f2519,plain,(
% 6.81/1.25    spl3_53 | ~spl3_54 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2490,f1265,f2516,f2512])).
% 6.81/1.25  fof(f2490,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0))) | k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k10_relat_1(sK2,k4_xboole_0(sK0,sK0)) | ~spl3_43),
% 6.81/1.25    inference(resolution,[],[f1267,f38])).
% 6.81/1.25  fof(f2510,plain,(
% 6.81/1.25    spl3_51 | ~spl3_6 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2509,f1265,f76,f2495])).
% 6.81/1.25  fof(f2509,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | (~spl3_6 | ~spl3_43)),
% 6.81/1.25    inference(forward_demodulation,[],[f2489,f77])).
% 6.81/1.25  fof(f2489,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))) | ~spl3_43),
% 6.81/1.25    inference(resolution,[],[f1267,f39])).
% 6.81/1.25  fof(f2508,plain,(
% 6.81/1.25    spl3_52 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2488,f1265,f2500])).
% 6.81/1.25  fof(f2500,plain,(
% 6.81/1.25    spl3_52 <=> k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 6.81/1.25  fof(f2488,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_43),
% 6.81/1.25    inference(resolution,[],[f1267,f40])).
% 6.81/1.25  fof(f2506,plain,(
% 6.81/1.25    spl3_51 | ~spl3_6 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2485,f1265,f76,f2495])).
% 6.81/1.25  fof(f2485,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | (~spl3_6 | ~spl3_43)),
% 6.81/1.25    inference(resolution,[],[f1267,f428])).
% 6.81/1.25  fof(f428,plain,(
% 6.81/1.25    ( ! [X4,X3] : (~r1_tarski(k10_relat_1(sK2,X4),k10_relat_1(sK2,X3)) | k10_relat_1(sK2,X3) = k2_xboole_0(k10_relat_1(sK2,X4),k10_relat_1(sK2,k4_xboole_0(X3,X4)))) ) | ~spl3_6),
% 6.81/1.25    inference(superposition,[],[f39,f77])).
% 6.81/1.25  fof(f2505,plain,(
% 6.81/1.25    spl3_51 | ~spl3_6 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2479,f1265,f76,f2495])).
% 6.81/1.25  fof(f2479,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | (~spl3_6 | ~spl3_43)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1267,f428])).
% 6.81/1.25  fof(f2503,plain,(
% 6.81/1.25    spl3_52 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2482,f1265,f2500])).
% 6.81/1.25  fof(f2482,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_43),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1267,f40])).
% 6.81/1.25  fof(f2498,plain,(
% 6.81/1.25    spl3_51 | ~spl3_6 | ~spl3_43),
% 6.81/1.25    inference(avatar_split_clause,[],[f2493,f1265,f76,f2495])).
% 6.81/1.25  fof(f2493,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK0)))) | (~spl3_6 | ~spl3_43)),
% 6.81/1.25    inference(forward_demodulation,[],[f2483,f77])).
% 6.81/1.25  fof(f2483,plain,(
% 6.81/1.25    k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) = k2_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k10_relat_1(sK2,k4_xboole_0(sK1,sK0)),k10_relat_1(sK2,k4_xboole_0(sK0,sK0)))) | ~spl3_43),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1267,f39])).
% 6.81/1.25  fof(f2425,plain,(
% 6.81/1.25    ~spl3_50 | ~spl3_9 | spl3_39),
% 6.81/1.25    inference(avatar_split_clause,[],[f2410,f1104,f111,f2422])).
% 6.81/1.25  fof(f2422,plain,(
% 6.81/1.25    spl3_50 <=> r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 6.81/1.25  fof(f1104,plain,(
% 6.81/1.25    spl3_39 <=> r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 6.81/1.25  fof(f2410,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_9 | spl3_39)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1106,f280])).
% 6.81/1.25  fof(f280,plain,(
% 6.81/1.25    ( ! [X4] : (~r1_tarski(k4_xboole_0(X4,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | r1_tarski(X4,k2_relat_1(sK2))) ) | ~spl3_9),
% 6.81/1.25    inference(superposition,[],[f32,f113])).
% 6.81/1.25  fof(f1106,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2)) | spl3_39),
% 6.81/1.25    inference(avatar_component_clause,[],[f1104])).
% 6.81/1.25  fof(f2420,plain,(
% 6.81/1.25    ~spl3_49 | ~spl3_10 | spl3_39),
% 6.81/1.25    inference(avatar_split_clause,[],[f2411,f1104,f116,f2417])).
% 6.81/1.25  fof(f2417,plain,(
% 6.81/1.25    spl3_49 <=> r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k2_relat_1(sK2))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 6.81/1.25  fof(f2411,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),sK0),k2_relat_1(sK2)) | (~spl3_10 | spl3_39)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1106,f195])).
% 6.81/1.25  fof(f195,plain,(
% 6.81/1.25    ( ! [X2] : (~r1_tarski(k4_xboole_0(X2,sK0),k2_relat_1(sK2)) | r1_tarski(X2,k2_relat_1(sK2))) ) | ~spl3_10),
% 6.81/1.25    inference(superposition,[],[f32,f118])).
% 6.81/1.25  fof(f1418,plain,(
% 6.81/1.25    ~spl3_48 | spl3_1 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f1413,f116,f47,f1415])).
% 6.81/1.25  fof(f1415,plain,(
% 6.81/1.25    spl3_48 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),sK1)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 6.81/1.25  fof(f1413,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))),sK1) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(superposition,[],[f1367,f588])).
% 6.81/1.25  fof(f1400,plain,(
% 6.81/1.25    ~spl3_47 | ~spl3_45 | spl3_1 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f1380,f150,f47,f1387,f1397])).
% 6.81/1.25  fof(f1397,plain,(
% 6.81/1.25    spl3_47 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 6.81/1.25  fof(f1387,plain,(
% 6.81/1.25    spl3_45 <=> r1_tarski(k10_relat_1(sK2,sK1),sK1)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 6.81/1.25  fof(f1380,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),sK1) | ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (spl3_1 | ~spl3_14)),
% 6.81/1.25    inference(superposition,[],[f210,f152])).
% 6.81/1.25  fof(f1395,plain,(
% 6.81/1.25    ~spl3_46 | ~spl3_45 | spl3_1 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f1379,f155,f47,f1387,f1392])).
% 6.81/1.25  fof(f1392,plain,(
% 6.81/1.25    spl3_46 <=> r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 6.81/1.25  fof(f1379,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),sK1) | ~r1_tarski(k4_xboole_0(sK0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,sK1)) | (spl3_1 | ~spl3_15)),
% 6.81/1.25    inference(superposition,[],[f210,f157])).
% 6.81/1.25  fof(f1390,plain,(
% 6.81/1.25    spl3_44 | ~spl3_45 | spl3_1 | ~spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f1378,f57,f47,f1387,f1384])).
% 6.81/1.25  fof(f1384,plain,(
% 6.81/1.25    spl3_44 <=> ! [X7] : ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,sK0),X7)),k10_relat_1(sK2,sK1))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 6.81/1.25  fof(f1378,plain,(
% 6.81/1.25    ( ! [X7] : (~r1_tarski(k10_relat_1(sK2,sK1),sK1) | ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(k10_relat_1(sK2,sK0),X7)),k10_relat_1(sK2,sK1))) ) | (spl3_1 | ~spl3_3)),
% 6.81/1.25    inference(superposition,[],[f210,f311])).
% 6.81/1.25  fof(f311,plain,(
% 6.81/1.25    ( ! [X0] : (k10_relat_1(sK2,sK1) = k2_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))) ) | ~spl3_3),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f142,f40])).
% 6.81/1.25  fof(f1273,plain,(
% 6.81/1.25    spl3_43 | ~spl3_3 | ~spl3_6 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f1272,f150,f76,f57,f1265])).
% 6.81/1.25  fof(f1272,plain,(
% 6.81/1.25    r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_6 | ~spl3_14)),
% 6.81/1.25    inference(forward_demodulation,[],[f1255,f77])).
% 6.81/1.25  fof(f1255,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_14)),
% 6.81/1.25    inference(resolution,[],[f489,f59])).
% 6.81/1.25  fof(f489,plain,(
% 6.81/1.25    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK2,sK1)) | r1_tarski(k4_xboole_0(X0,k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))) ) | ~spl3_14),
% 6.81/1.25    inference(superposition,[],[f34,f152])).
% 6.81/1.25  fof(f1268,plain,(
% 6.81/1.25    spl3_43 | ~spl3_3 | ~spl3_6 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f1263,f150,f76,f57,f1265])).
% 6.81/1.25  fof(f1263,plain,(
% 6.81/1.25    r1_tarski(k10_relat_1(sK2,k4_xboole_0(sK0,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_6 | ~spl3_14)),
% 6.81/1.25    inference(forward_demodulation,[],[f1237,f77])).
% 6.81/1.25  fof(f1237,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0)),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_14)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f59,f489])).
% 6.81/1.25  fof(f1148,plain,(
% 6.81/1.25    ~spl3_42 | ~spl3_2 | spl3_35),
% 6.81/1.25    inference(avatar_split_clause,[],[f1126,f1065,f52,f1145])).
% 6.81/1.25  fof(f1145,plain,(
% 6.81/1.25    spl3_42 <=> r1_tarski(k10_relat_1(sK2,sK1),sK0)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 6.81/1.25  fof(f1065,plain,(
% 6.81/1.25    spl3_35 <=> r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 6.81/1.25  fof(f1126,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),sK0) | (~spl3_2 | spl3_35)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f54,f1093])).
% 6.81/1.25  fof(f1093,plain,(
% 6.81/1.25    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK1),X0) | ~r1_tarski(X0,k2_relat_1(sK2))) ) | spl3_35),
% 6.81/1.25    inference(superposition,[],[f1077,f39])).
% 6.81/1.25  fof(f1077,plain,(
% 6.81/1.25    ( ! [X0] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK1),X0),k2_relat_1(sK2))) ) | spl3_35),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1067,f33])).
% 6.81/1.25  fof(f1067,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2)) | spl3_35),
% 6.81/1.25    inference(avatar_component_clause,[],[f1065])).
% 6.81/1.25  fof(f1143,plain,(
% 6.81/1.25    ~spl3_41 | ~spl3_10 | spl3_35),
% 6.81/1.25    inference(avatar_split_clause,[],[f1132,f1065,f116,f1140])).
% 6.81/1.25  fof(f1140,plain,(
% 6.81/1.25    spl3_41 <=> r1_tarski(k10_relat_1(sK2,sK1),k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 6.81/1.25  fof(f1132,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_10 | spl3_35)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f1093])).
% 6.81/1.25  fof(f1112,plain,(
% 6.81/1.25    ~spl3_40 | ~spl3_9 | spl3_37),
% 6.81/1.25    inference(avatar_split_clause,[],[f1097,f1080,f111,f1109])).
% 6.81/1.25  fof(f1109,plain,(
% 6.81/1.25    spl3_40 <=> r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 6.81/1.25  fof(f1080,plain,(
% 6.81/1.25    spl3_37 <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 6.81/1.25  fof(f1097,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_9 | spl3_37)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1082,f280])).
% 6.81/1.25  fof(f1082,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2)) | spl3_37),
% 6.81/1.25    inference(avatar_component_clause,[],[f1080])).
% 6.81/1.25  fof(f1107,plain,(
% 6.81/1.25    ~spl3_39 | ~spl3_10 | spl3_37),
% 6.81/1.25    inference(avatar_split_clause,[],[f1098,f1080,f116,f1104])).
% 6.81/1.25  fof(f1098,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),sK0),k2_relat_1(sK2)) | (~spl3_10 | spl3_37)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1082,f195])).
% 6.81/1.25  fof(f1088,plain,(
% 6.81/1.25    ~spl3_38 | ~spl3_9 | spl3_35),
% 6.81/1.25    inference(avatar_split_clause,[],[f1075,f1065,f111,f1085])).
% 6.81/1.25  fof(f1085,plain,(
% 6.81/1.25    spl3_38 <=> r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 6.81/1.25  fof(f1075,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_9 | spl3_35)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1067,f280])).
% 6.81/1.25  fof(f1083,plain,(
% 6.81/1.25    ~spl3_37 | ~spl3_10 | spl3_35),
% 6.81/1.25    inference(avatar_split_clause,[],[f1076,f1065,f116,f1080])).
% 6.81/1.25  fof(f1076,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k10_relat_1(sK2,sK1),sK0),k2_relat_1(sK2)) | (~spl3_10 | spl3_35)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f1067,f195])).
% 6.81/1.25  fof(f1074,plain,(
% 6.81/1.25    spl3_36 | ~spl3_35 | ~spl3_7 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f1058,f150,f80,f1065,f1070])).
% 6.81/1.25  fof(f1058,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2)) | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0))) | (~spl3_7 | ~spl3_14)),
% 6.81/1.25    inference(superposition,[],[f355,f152])).
% 6.81/1.25  fof(f1073,plain,(
% 6.81/1.25    spl3_36 | ~spl3_35 | ~spl3_7 | ~spl3_15),
% 6.81/1.25    inference(avatar_split_clause,[],[f1057,f155,f80,f1065,f1070])).
% 6.81/1.25  fof(f1057,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2)) | k10_relat_1(sK2,sK0) = k9_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,sK0))) | (~spl3_7 | ~spl3_15)),
% 6.81/1.25    inference(superposition,[],[f355,f157])).
% 6.81/1.25  fof(f1068,plain,(
% 6.81/1.25    spl3_34 | ~spl3_35 | ~spl3_3 | ~spl3_7),
% 6.81/1.25    inference(avatar_split_clause,[],[f1056,f80,f57,f1065,f1062])).
% 6.81/1.25  fof(f1056,plain,(
% 6.81/1.25    ( ! [X7] : (~r1_tarski(k10_relat_1(sK2,sK1),k2_relat_1(sK2)) | k4_xboole_0(k10_relat_1(sK2,sK0),X7) = k9_relat_1(sK2,k10_relat_1(sK2,k4_xboole_0(k10_relat_1(sK2,sK0),X7)))) ) | (~spl3_3 | ~spl3_7)),
% 6.81/1.25    inference(superposition,[],[f355,f311])).
% 6.81/1.25  fof(f988,plain,(
% 6.81/1.25    spl3_33 | ~spl3_2 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f978,f116,f52,f984])).
% 6.81/1.25  fof(f978,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_2 | ~spl3_10)),
% 6.81/1.25    inference(superposition,[],[f588,f179])).
% 6.81/1.25  fof(f987,plain,(
% 6.81/1.25    spl3_33 | ~spl3_2 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f976,f116,f52,f984])).
% 6.81/1.25  fof(f976,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(sK0,k2_relat_1(sK2))) | (~spl3_2 | ~spl3_10)),
% 6.81/1.25    inference(superposition,[],[f179,f588])).
% 6.81/1.25  fof(f923,plain,(
% 6.81/1.25    ~spl3_32 | spl3_31),
% 6.81/1.25    inference(avatar_split_clause,[],[f916,f885,f919])).
% 6.81/1.25  fof(f919,plain,(
% 6.81/1.25    spl3_32 <=> r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 6.81/1.25  fof(f885,plain,(
% 6.81/1.25    spl3_31 <=> r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 6.81/1.25  fof(f916,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | spl3_31),
% 6.81/1.25    inference(resolution,[],[f887,f34])).
% 6.81/1.25  fof(f887,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)) | spl3_31),
% 6.81/1.25    inference(avatar_component_clause,[],[f885])).
% 6.81/1.25  fof(f922,plain,(
% 6.81/1.25    ~spl3_32 | spl3_31),
% 6.81/1.25    inference(avatar_split_clause,[],[f913,f885,f919])).
% 6.81/1.25  fof(f913,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k2_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | spl3_31),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f887,f34])).
% 6.81/1.25  fof(f889,plain,(
% 6.81/1.25    spl3_30 | ~spl3_31 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f859,f845,f885,f881])).
% 6.81/1.25  fof(f881,plain,(
% 6.81/1.25    spl3_30 <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 6.81/1.25  fof(f845,plain,(
% 6.81/1.25    spl3_26 <=> r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 6.81/1.25  fof(f859,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)) | k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0) | ~spl3_26),
% 6.81/1.25    inference(resolution,[],[f847,f38])).
% 6.81/1.25  fof(f847,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_26),
% 6.81/1.25    inference(avatar_component_clause,[],[f845])).
% 6.81/1.25  fof(f888,plain,(
% 6.81/1.25    spl3_30 | ~spl3_31 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f858,f845,f885,f881])).
% 6.81/1.25  fof(f858,plain,(
% 6.81/1.25    ~r1_tarski(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)) | k4_xboole_0(k2_relat_1(sK2),sK0) = k4_xboole_0(sK0,sK0) | ~spl3_26),
% 6.81/1.25    inference(resolution,[],[f847,f38])).
% 6.81/1.25  fof(f879,plain,(
% 6.81/1.25    spl3_27 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f857,f845,f862])).
% 6.81/1.25  fof(f862,plain,(
% 6.81/1.25    spl3_27 <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 6.81/1.25  fof(f857,plain,(
% 6.81/1.25    k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))) | ~spl3_26),
% 6.81/1.25    inference(resolution,[],[f847,f39])).
% 6.81/1.25  fof(f878,plain,(
% 6.81/1.25    spl3_28 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f856,f845,f867])).
% 6.81/1.25  fof(f867,plain,(
% 6.81/1.25    spl3_28 <=> k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 6.81/1.25  fof(f856,plain,(
% 6.81/1.25    k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_26),
% 6.81/1.25    inference(resolution,[],[f847,f40])).
% 6.81/1.25  fof(f875,plain,(
% 6.81/1.25    ~spl3_29 | spl3_19 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f851,f845,f282,f872])).
% 6.81/1.25  fof(f851,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k4_xboole_0(sK0,sK0)) | (spl3_19 | ~spl3_26)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f847,f392])).
% 6.81/1.25  fof(f870,plain,(
% 6.81/1.25    spl3_28 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f852,f845,f867])).
% 6.81/1.25  fof(f852,plain,(
% 6.81/1.25    k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_26),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f847,f40])).
% 6.81/1.25  fof(f865,plain,(
% 6.81/1.25    spl3_27 | ~spl3_26),
% 6.81/1.25    inference(avatar_split_clause,[],[f853,f845,f862])).
% 6.81/1.25  fof(f853,plain,(
% 6.81/1.25    k4_xboole_0(k2_relat_1(sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(k2_relat_1(sK2),sK0),k4_xboole_0(sK0,sK0))) | ~spl3_26),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f847,f39])).
% 6.81/1.25  fof(f849,plain,(
% 6.81/1.25    spl3_26 | ~spl3_2 | ~spl3_9),
% 6.81/1.25    inference(avatar_split_clause,[],[f842,f111,f52,f845])).
% 6.81/1.25  fof(f842,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_2 | ~spl3_9)),
% 6.81/1.25    inference(resolution,[],[f278,f54])).
% 6.81/1.25  fof(f848,plain,(
% 6.81/1.25    spl3_26 | ~spl3_2 | ~spl3_9),
% 6.81/1.25    inference(avatar_split_clause,[],[f826,f111,f52,f845])).
% 6.81/1.25  fof(f826,plain,(
% 6.81/1.25    r1_tarski(k4_xboole_0(sK0,sK0),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_2 | ~spl3_9)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f54,f278])).
% 6.81/1.25  fof(f655,plain,(
% 6.81/1.25    ~spl3_25 | ~spl3_15 | spl3_22),
% 6.81/1.25    inference(avatar_split_clause,[],[f644,f493,f155,f652])).
% 6.81/1.25  fof(f652,plain,(
% 6.81/1.25    spl3_25 <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 6.81/1.25  fof(f493,plain,(
% 6.81/1.25    spl3_22 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 6.81/1.25  fof(f644,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_15 | spl3_22)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f495,f395])).
% 6.81/1.25  fof(f495,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | spl3_22),
% 6.81/1.25    inference(avatar_component_clause,[],[f493])).
% 6.81/1.25  fof(f622,plain,(
% 6.81/1.25    ~spl3_24 | spl3_1 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f599,f116,f47,f618])).
% 6.81/1.25  fof(f618,plain,(
% 6.81/1.25    spl3_24 <=> r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 6.81/1.25  fof(f599,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f271])).
% 6.81/1.25  fof(f621,plain,(
% 6.81/1.25    ~spl3_24 | spl3_1 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f606,f116,f47,f618])).
% 6.81/1.25  fof(f606,plain,(
% 6.81/1.25    ~r1_tarski(sK0,k4_xboole_0(sK0,k2_relat_1(sK2))) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f562,f174])).
% 6.81/1.25  fof(f501,plain,(
% 6.81/1.25    ~spl3_22 | spl3_23 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f488,f150,f497,f493])).
% 6.81/1.25  fof(f497,plain,(
% 6.81/1.25    spl3_23 <=> k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 6.81/1.25  fof(f488,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_14),
% 6.81/1.25    inference(superposition,[],[f40,f152])).
% 6.81/1.25  fof(f500,plain,(
% 6.81/1.25    ~spl3_22 | spl3_23 | ~spl3_14),
% 6.81/1.25    inference(avatar_split_clause,[],[f487,f150,f497,f493])).
% 6.81/1.25  fof(f487,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k4_xboole_0(sK1,sK0)) | ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | ~spl3_14),
% 6.81/1.25    inference(superposition,[],[f152,f40])).
% 6.81/1.25  fof(f298,plain,(
% 6.81/1.25    ~spl3_21 | ~spl3_10 | spl3_19),
% 6.81/1.25    inference(avatar_split_clause,[],[f291,f282,f116,f295])).
% 6.81/1.25  fof(f291,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),sK0)) | (~spl3_10 | spl3_19)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f284,f194])).
% 6.81/1.25  fof(f290,plain,(
% 6.81/1.25    ~spl3_19 | spl3_20 | ~spl3_9),
% 6.81/1.25    inference(avatar_split_clause,[],[f277,f111,f286,f282])).
% 6.81/1.25  fof(f286,plain,(
% 6.81/1.25    spl3_20 <=> k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 6.81/1.25  fof(f277,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0) | ~r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_9),
% 6.81/1.25    inference(superposition,[],[f40,f113])).
% 6.81/1.25  fof(f289,plain,(
% 6.81/1.25    ~spl3_19 | spl3_20 | ~spl3_9),
% 6.81/1.25    inference(avatar_split_clause,[],[f273,f111,f286,f282])).
% 6.81/1.25  fof(f273,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k4_xboole_0(k2_relat_1(sK2),sK0) | ~r1_tarski(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_9),
% 6.81/1.25    inference(superposition,[],[f113,f40])).
% 6.81/1.25  fof(f200,plain,(
% 6.81/1.25    ~spl3_18 | spl3_1 | ~spl3_10),
% 6.81/1.25    inference(avatar_split_clause,[],[f192,f116,f47,f197])).
% 6.81/1.25  fof(f192,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),sK1) | (spl3_1 | ~spl3_10)),
% 6.81/1.25    inference(superposition,[],[f98,f118])).
% 6.81/1.25  fof(f171,plain,(
% 6.81/1.25    spl3_16 | ~spl3_17 | ~spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f146,f57,f167,f163])).
% 6.81/1.25  fof(f163,plain,(
% 6.81/1.25    spl3_16 <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 6.81/1.25  fof(f167,plain,(
% 6.81/1.25    spl3_17 <=> r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 6.81/1.25  fof(f146,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)) | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) | ~spl3_3),
% 6.81/1.25    inference(resolution,[],[f59,f38])).
% 6.81/1.25  fof(f170,plain,(
% 6.81/1.25    spl3_16 | ~spl3_17 | ~spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f145,f57,f167,f163])).
% 6.81/1.25  fof(f145,plain,(
% 6.81/1.25    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)) | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) | ~spl3_3),
% 6.81/1.25    inference(resolution,[],[f59,f38])).
% 6.81/1.25  fof(f161,plain,(
% 6.81/1.25    spl3_14 | ~spl3_3 | ~spl3_6),
% 6.81/1.25    inference(avatar_split_clause,[],[f160,f76,f57,f150])).
% 6.81/1.25  fof(f160,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_6)),
% 6.81/1.25    inference(forward_demodulation,[],[f144,f77])).
% 6.81/1.25  fof(f144,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))) | ~spl3_3),
% 6.81/1.25    inference(resolution,[],[f59,f39])).
% 6.81/1.25  fof(f159,plain,(
% 6.81/1.25    spl3_15 | ~spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f143,f57,f155])).
% 6.81/1.25  fof(f143,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 6.81/1.25    inference(resolution,[],[f59,f40])).
% 6.81/1.25  fof(f158,plain,(
% 6.81/1.25    spl3_15 | ~spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f140,f57,f155])).
% 6.81/1.25  fof(f140,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f59,f40])).
% 6.81/1.25  fof(f153,plain,(
% 6.81/1.25    spl3_14 | ~spl3_3 | ~spl3_6),
% 6.81/1.25    inference(avatar_split_clause,[],[f148,f76,f57,f150])).
% 6.81/1.25  fof(f148,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k4_xboole_0(sK1,sK0))) | (~spl3_3 | ~spl3_6)),
% 6.81/1.25    inference(forward_demodulation,[],[f141,f77])).
% 6.81/1.25  fof(f141,plain,(
% 6.81/1.25    k10_relat_1(sK2,sK1) = k2_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))) | ~spl3_3),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f59,f39])).
% 6.81/1.25  fof(f137,plain,(
% 6.81/1.25    spl3_12 | ~spl3_13 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f108,f52,f133,f129])).
% 6.81/1.25  fof(f129,plain,(
% 6.81/1.25    spl3_12 <=> sK0 = k2_relat_1(sK2)),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 6.81/1.25  fof(f108,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),sK0) | sK0 = k2_relat_1(sK2) | ~spl3_2),
% 6.81/1.25    inference(resolution,[],[f54,f38])).
% 6.81/1.25  fof(f136,plain,(
% 6.81/1.25    spl3_12 | ~spl3_13 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f107,f52,f133,f129])).
% 6.81/1.25  fof(f107,plain,(
% 6.81/1.25    ~r1_tarski(k2_relat_1(sK2),sK0) | sK0 = k2_relat_1(sK2) | ~spl3_2),
% 6.81/1.25    inference(resolution,[],[f54,f38])).
% 6.81/1.25  fof(f127,plain,(
% 6.81/1.25    spl3_9 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f106,f52,f111])).
% 6.81/1.25  fof(f106,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_2),
% 6.81/1.25    inference(resolution,[],[f54,f39])).
% 6.81/1.25  fof(f126,plain,(
% 6.81/1.25    spl3_10 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f105,f52,f116])).
% 6.81/1.25  fof(f105,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 6.81/1.25    inference(resolution,[],[f54,f40])).
% 6.81/1.25  fof(f125,plain,(
% 6.81/1.25    spl3_11 | ~spl3_4 | ~spl3_5 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f104,f52,f67,f62,f121])).
% 6.81/1.25  fof(f121,plain,(
% 6.81/1.25    spl3_11 <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 6.81/1.25  fof(f104,plain,(
% 6.81/1.25    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~spl3_2),
% 6.81/1.25    inference(resolution,[],[f54,f31])).
% 6.81/1.25  fof(f124,plain,(
% 6.81/1.25    spl3_11 | ~spl3_2 | ~spl3_4 | ~spl3_5),
% 6.81/1.25    inference(avatar_split_clause,[],[f100,f67,f62,f52,f121])).
% 6.81/1.25  fof(f100,plain,(
% 6.81/1.25    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl3_2 | ~spl3_4 | ~spl3_5)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f64,f69,f54,f31])).
% 6.81/1.25  fof(f119,plain,(
% 6.81/1.25    spl3_10 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f101,f52,f116])).
% 6.81/1.25  fof(f101,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k2_xboole_0(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f54,f40])).
% 6.81/1.25  fof(f114,plain,(
% 6.81/1.25    spl3_9 | ~spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f102,f52,f111])).
% 6.81/1.25  fof(f102,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k2_xboole_0(sK0,k4_xboole_0(k2_relat_1(sK2),sK0)) | ~spl3_2),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f54,f39])).
% 6.81/1.25  fof(f94,plain,(
% 6.81/1.25    spl3_8 | ~spl3_4 | ~spl3_5),
% 6.81/1.25    inference(avatar_split_clause,[],[f84,f67,f62,f90])).
% 6.81/1.25  fof(f90,plain,(
% 6.81/1.25    spl3_8 <=> k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2)))),
% 6.81/1.25    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 6.81/1.25  fof(f84,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) | (~spl3_4 | ~spl3_5)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f64,f45,f69,f31])).
% 6.81/1.25  fof(f93,plain,(
% 6.81/1.25    spl3_8 | ~spl3_4 | ~spl3_5),
% 6.81/1.25    inference(avatar_split_clause,[],[f85,f67,f62,f90])).
% 6.81/1.25  fof(f85,plain,(
% 6.81/1.25    k2_relat_1(sK2) = k9_relat_1(sK2,k10_relat_1(sK2,k2_relat_1(sK2))) | (~spl3_4 | ~spl3_5)),
% 6.81/1.25    inference(unit_resulting_resolution,[],[f64,f44,f69,f31])).
% 6.81/1.25  fof(f82,plain,(
% 6.81/1.25    spl3_7 | ~spl3_5 | ~spl3_4),
% 6.81/1.25    inference(avatar_split_clause,[],[f72,f62,f67,f80])).
% 6.81/1.25  fof(f72,plain,(
% 6.81/1.25    ( ! [X2] : (~v1_relat_1(sK2) | ~r1_tarski(X2,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2) ) | ~spl3_4),
% 6.81/1.25    inference(resolution,[],[f64,f31])).
% 6.81/1.25  fof(f78,plain,(
% 6.81/1.25    ~spl3_5 | spl3_6 | ~spl3_4),
% 6.81/1.25    inference(avatar_split_clause,[],[f74,f62,f76,f67])).
% 6.81/1.25  fof(f74,plain,(
% 6.81/1.25    ( ! [X0,X1] : (k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k4_xboole_0(X0,X1)) | ~v1_relat_1(sK2)) ) | ~spl3_4),
% 6.81/1.25    inference(forward_demodulation,[],[f73,f43])).
% 6.81/1.25  fof(f73,plain,(
% 6.81/1.25    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k4_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl3_4),
% 6.81/1.25    inference(forward_demodulation,[],[f71,f43])).
% 6.81/1.25  fof(f71,plain,(
% 6.81/1.25    ( ! [X0,X1] : (~v1_relat_1(sK2) | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_4),
% 6.81/1.25    inference(resolution,[],[f64,f42])).
% 6.81/1.25  fof(f70,plain,(
% 6.81/1.25    spl3_5),
% 6.81/1.25    inference(avatar_split_clause,[],[f26,f67])).
% 6.81/1.25  fof(f26,plain,(
% 6.81/1.25    v1_relat_1(sK2)),
% 6.81/1.25    inference(cnf_transformation,[],[f15])).
% 6.81/1.25  fof(f15,plain,(
% 6.81/1.25    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 6.81/1.25    inference(flattening,[],[f14])).
% 6.81/1.25  fof(f14,plain,(
% 6.81/1.25    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 6.81/1.25    inference(ennf_transformation,[],[f13])).
% 6.81/1.25  fof(f13,negated_conjecture,(
% 6.81/1.25    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 6.81/1.25    inference(negated_conjecture,[],[f12])).
% 6.81/1.25  fof(f12,conjecture,(
% 6.81/1.25    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 6.81/1.25    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 6.81/1.25  fof(f65,plain,(
% 6.81/1.25    spl3_4),
% 6.81/1.25    inference(avatar_split_clause,[],[f27,f62])).
% 6.81/1.25  fof(f27,plain,(
% 6.81/1.25    v1_funct_1(sK2)),
% 6.81/1.25    inference(cnf_transformation,[],[f15])).
% 6.81/1.25  fof(f60,plain,(
% 6.81/1.25    spl3_3),
% 6.81/1.25    inference(avatar_split_clause,[],[f28,f57])).
% 6.81/1.25  fof(f28,plain,(
% 6.81/1.25    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 6.81/1.25    inference(cnf_transformation,[],[f15])).
% 6.81/1.25  fof(f55,plain,(
% 6.81/1.25    spl3_2),
% 6.81/1.25    inference(avatar_split_clause,[],[f29,f52])).
% 6.81/1.25  fof(f29,plain,(
% 6.81/1.25    r1_tarski(sK0,k2_relat_1(sK2))),
% 6.81/1.25    inference(cnf_transformation,[],[f15])).
% 6.81/1.25  fof(f50,plain,(
% 6.81/1.25    ~spl3_1),
% 6.81/1.25    inference(avatar_split_clause,[],[f30,f47])).
% 6.81/1.25  fof(f30,plain,(
% 6.81/1.25    ~r1_tarski(sK0,sK1)),
% 6.81/1.25    inference(cnf_transformation,[],[f15])).
% 6.81/1.25  % SZS output end Proof for theBenchmark
% 6.81/1.25  % (15936)------------------------------
% 6.81/1.25  % (15936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.81/1.25  % (15936)Termination reason: Refutation
% 6.81/1.25  
% 6.81/1.25  % (15936)Memory used [KB]: 10362
% 6.81/1.25  % (15936)Time elapsed: 0.811 s
% 6.81/1.25  % (15936)------------------------------
% 6.81/1.25  % (15936)------------------------------
% 6.81/1.25  % (15927)Success in time 0.885 s
%------------------------------------------------------------------------------

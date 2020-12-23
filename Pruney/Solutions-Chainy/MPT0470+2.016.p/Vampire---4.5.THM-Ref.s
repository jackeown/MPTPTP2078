%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 317 expanded)
%              Number of leaves         :   44 ( 133 expanded)
%              Depth                    :    8
%              Number of atoms          :  450 ( 787 expanded)
%              Number of equality atoms :   86 ( 137 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f68,f93,f105,f118,f123,f138,f158,f215,f227,f258,f293,f319,f341,f407,f419,f506,f606,f642,f695,f833,f910,f1054,f1720,f1805,f2077,f2097,f2261,f2262])).

fof(f2262,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) != k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | k1_xboole_0 != k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2261,plain,
    ( spl1_116
    | ~ spl1_112 ),
    inference(avatar_split_clause,[],[f2111,f2070,f2258])).

fof(f2258,plain,
    ( spl1_116
  <=> k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_116])])).

fof(f2070,plain,
    ( spl1_112
  <=> v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_112])])).

fof(f2111,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_112 ),
    inference(resolution,[],[f2072,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2072,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_112 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f2097,plain,
    ( ~ spl1_9
    | ~ spl1_69
    | spl1_113 ),
    inference(avatar_contradiction_clause,[],[f2096])).

fof(f2096,plain,
    ( $false
    | ~ spl1_9
    | ~ spl1_69
    | spl1_113 ),
    inference(subsumption_resolution,[],[f2095,f1042])).

fof(f1042,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_69 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1041,plain,
    ( spl1_69
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_69])])).

fof(f2095,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_9
    | spl1_113 ),
    inference(subsumption_resolution,[],[f2092,f113])).

fof(f113,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f2092,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_113 ),
    inference(resolution,[],[f2076,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2076,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | spl1_113 ),
    inference(avatar_component_clause,[],[f2074])).

fof(f2074,plain,
    ( spl1_113
  <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_113])])).

fof(f2077,plain,
    ( spl1_112
    | ~ spl1_113
    | ~ spl1_2
    | ~ spl1_43 ),
    inference(avatar_split_clause,[],[f658,f639,f55,f2074,f2070])).

fof(f55,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f639,plain,
    ( spl1_43
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).

fof(f658,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_43 ),
    inference(subsumption_resolution,[],[f656,f57])).

fof(f57,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f656,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_43 ),
    inference(superposition,[],[f42,f641])).

fof(f641,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_43 ),
    inference(avatar_component_clause,[],[f639])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f1805,plain,
    ( spl1_98
    | ~ spl1_97 ),
    inference(avatar_split_clause,[],[f1740,f1717,f1802])).

fof(f1802,plain,
    ( spl1_98
  <=> k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_98])])).

fof(f1717,plain,
    ( spl1_97
  <=> v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_97])])).

fof(f1740,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl1_97 ),
    inference(resolution,[],[f1719,f37])).

fof(f1719,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_97 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f1720,plain,
    ( spl1_97
    | ~ spl1_2
    | ~ spl1_25
    | ~ spl1_63 ),
    inference(avatar_split_clause,[],[f1675,f892,f338,f55,f1717])).

fof(f338,plain,
    ( spl1_25
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f892,plain,
    ( spl1_63
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_63])])).

fof(f1675,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_25
    | ~ spl1_63 ),
    inference(subsumption_resolution,[],[f353,f893])).

fof(f893,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_63 ),
    inference(avatar_component_clause,[],[f892])).

fof(f353,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_25 ),
    inference(subsumption_resolution,[],[f351,f57])).

fof(f351,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_25 ),
    inference(superposition,[],[f42,f340])).

fof(f340,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_25 ),
    inference(avatar_component_clause,[],[f338])).

fof(f1054,plain,
    ( ~ spl1_9
    | spl1_69 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | ~ spl1_9
    | spl1_69 ),
    inference(subsumption_resolution,[],[f1050,f113])).

fof(f1050,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_69 ),
    inference(resolution,[],[f1043,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f1043,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl1_69 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f910,plain,
    ( ~ spl1_9
    | ~ spl1_22
    | spl1_63 ),
    inference(avatar_contradiction_clause,[],[f909])).

fof(f909,plain,
    ( $false
    | ~ spl1_9
    | ~ spl1_22
    | spl1_63 ),
    inference(subsumption_resolution,[],[f908,f275])).

fof(f275,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl1_22
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f908,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9
    | spl1_63 ),
    inference(subsumption_resolution,[],[f905,f113])).

fof(f905,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_63 ),
    inference(resolution,[],[f894,f43])).

fof(f894,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | spl1_63 ),
    inference(avatar_component_clause,[],[f892])).

fof(f833,plain,
    ( spl1_55
    | ~ spl1_9
    | ~ spl1_32 ),
    inference(avatar_split_clause,[],[f443,f417,f112,f830])).

fof(f830,plain,
    ( spl1_55
  <=> k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_55])])).

fof(f417,plain,
    ( spl1_32
  <=> ! [X2] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f443,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_9
    | ~ spl1_32 ),
    inference(resolution,[],[f418,f113])).

fof(f418,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0) )
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f417])).

fof(f695,plain,
    ( spl1_49
    | ~ spl1_1
    | ~ spl1_30 ),
    inference(avatar_split_clause,[],[f434,f392,f50,f692])).

fof(f692,plain,
    ( spl1_49
  <=> k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_49])])).

fof(f50,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f392,plain,
    ( spl1_30
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f434,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_30 ),
    inference(resolution,[],[f393,f52])).

fof(f52,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) )
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f392])).

fof(f642,plain,
    ( spl1_43
    | ~ spl1_9
    | ~ spl1_42 ),
    inference(avatar_split_clause,[],[f618,f604,f112,f639])).

fof(f604,plain,
    ( spl1_42
  <=> ! [X1] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).

fof(f618,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl1_9
    | ~ spl1_42 ),
    inference(resolution,[],[f605,f113])).

fof(f605,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0)) )
    | ~ spl1_42 ),
    inference(avatar_component_clause,[],[f604])).

fof(f606,plain,
    ( spl1_42
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f146,f131,f604])).

fof(f131,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f146,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0))
        | ~ v1_relat_1(X1) )
    | ~ spl1_11 ),
    inference(resolution,[],[f132,f38])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f506,plain,
    ( spl1_36
    | ~ spl1_1
    | ~ spl1_24 ),
    inference(avatar_split_clause,[],[f336,f317,f50,f503])).

fof(f503,plain,
    ( spl1_36
  <=> k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f317,plain,
    ( spl1_24
  <=> ! [X2] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f336,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ spl1_1
    | ~ spl1_24 ),
    inference(resolution,[],[f318,f52])).

fof(f318,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))) )
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f317])).

fof(f419,plain,
    ( spl1_32
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f170,f112,f102,f417])).

fof(f102,plain,
    ( spl1_8
  <=> k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f170,plain,
    ( ! [X2] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0)
        | ~ v1_relat_1(X2) )
    | ~ spl1_8
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f166,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f166,plain,
    ( ! [X2] :
        ( k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(k1_xboole_0)))
        | ~ v1_relat_1(X2) )
    | ~ spl1_9 ),
    inference(resolution,[],[f98,f113])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k4_relat_1(k5_relat_1(k4_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(X3)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f407,plain,
    ( spl1_30
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f159,f55,f392])).

fof(f159,plain,
    ( ! [X0] :
        ( k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_2 ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k4_relat_1(k5_relat_1(X1,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f341,plain,
    ( spl1_25
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f308,f274,f131,f338])).

fof(f308,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl1_11
    | ~ spl1_22 ),
    inference(resolution,[],[f275,f132])).

fof(f319,plain,
    ( spl1_24
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f150,f112,f317])).

fof(f150,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))) )
    | ~ spl1_9 ),
    inference(resolution,[],[f79,f113])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f43,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f293,plain,
    ( ~ spl1_1
    | spl1_22 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl1_1
    | spl1_22 ),
    inference(subsumption_resolution,[],[f289,f52])).

fof(f289,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_22 ),
    inference(resolution,[],[f276,f38])).

fof(f276,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_22 ),
    inference(avatar_component_clause,[],[f274])).

fof(f258,plain,
    ( spl1_7
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f235,f208,f90])).

fof(f90,plain,
    ( spl1_7
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f208,plain,
    ( spl1_17
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f235,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_17 ),
    inference(resolution,[],[f210,f37])).

fof(f210,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f227,plain,
    ( ~ spl1_1
    | ~ spl1_9
    | spl1_18 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_9
    | spl1_18 ),
    inference(subsumption_resolution,[],[f225,f52])).

fof(f225,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_9
    | spl1_18 ),
    inference(subsumption_resolution,[],[f222,f113])).

fof(f222,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl1_18 ),
    inference(resolution,[],[f214,f43])).

fof(f214,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl1_18
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f215,plain,
    ( spl1_17
    | ~ spl1_18
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f164,f155,f55,f212,f208])).

fof(f155,plain,
    ( spl1_13
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f164,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_13 ),
    inference(superposition,[],[f42,f157])).

fof(f157,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl1_13
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f148,f131,f50,f155])).

fof(f148,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_1
    | ~ spl1_11 ),
    inference(resolution,[],[f132,f52])).

fof(f138,plain,
    ( spl1_11
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f129,f116,f131])).

fof(f116,plain,
    ( spl1_10
  <=> ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f129,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl1_10 ),
    inference(subsumption_resolution,[],[f128,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f128,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X1,k1_xboole_0)))
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0)) )
    | ~ spl1_10 ),
    inference(resolution,[],[f117,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f117,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( ~ spl1_2
    | spl1_9 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl1_2
    | spl1_9 ),
    inference(subsumption_resolution,[],[f120,f57])).

fof(f120,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_9 ),
    inference(resolution,[],[f114,f36])).

fof(f114,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f118,plain,
    ( ~ spl1_9
    | spl1_10
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f95,f65,f116,f112])).

fof(f65,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f95,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_4 ),
    inference(superposition,[],[f40,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f105,plain,
    ( spl1_8
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f96,f55,f102])).

fof(f96,plain,
    ( k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl1_2 ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f39,f36])).

fof(f93,plain,
    ( ~ spl1_6
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f31,f90,f86])).

fof(f86,plain,
    ( spl1_6
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f31,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f68,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f58,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:36:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.49  % (7073)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.50  % (7081)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.52  % (7066)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.52  % (7067)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (7071)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (7086)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.53  % (7074)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (7069)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (7064)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (7079)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (7075)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.54  % (7080)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.54  % (7078)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.54  % (7077)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.54  % (7070)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.54  % (7085)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.54  % (7082)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (7087)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  % (7072)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.55  % (7088)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.55  % (7068)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.56  % (7083)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.56  % (7076)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.56  % (7063)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.50/0.57  % (7065)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.50/0.57  % (7084)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.05/0.64  % (7065)Refutation found. Thanks to Tanya!
% 2.05/0.64  % SZS status Theorem for theBenchmark
% 2.05/0.65  % SZS output start Proof for theBenchmark
% 2.05/0.65  fof(f2263,plain,(
% 2.05/0.65    $false),
% 2.05/0.65    inference(avatar_sat_refutation,[],[f53,f58,f68,f93,f105,f118,f123,f138,f158,f215,f227,f258,f293,f319,f341,f407,f419,f506,f606,f642,f695,f833,f910,f1054,f1720,f1805,f2077,f2097,f2261,f2262])).
% 2.05/0.65  fof(f2262,plain,(
% 2.05/0.65    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) | k1_xboole_0 != k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) != k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | k1_xboole_0 != k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 2.05/0.65    introduced(theory_tautology_sat_conflict,[])).
% 2.05/0.65  fof(f2261,plain,(
% 2.05/0.65    spl1_116 | ~spl1_112),
% 2.05/0.65    inference(avatar_split_clause,[],[f2111,f2070,f2258])).
% 2.05/0.65  fof(f2258,plain,(
% 2.05/0.65    spl1_116 <=> k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_116])])).
% 2.05/0.65  fof(f2070,plain,(
% 2.05/0.65    spl1_112 <=> v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_112])])).
% 2.05/0.65  fof(f2111,plain,(
% 2.05/0.65    k1_xboole_0 = k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) | ~spl1_112),
% 2.05/0.65    inference(resolution,[],[f2072,f37])).
% 2.05/0.65  fof(f37,plain,(
% 2.05/0.65    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  fof(f17,plain,(
% 2.05/0.65    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f2])).
% 2.05/0.65  fof(f2,axiom,(
% 2.05/0.65    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.05/0.65  fof(f2072,plain,(
% 2.05/0.65    v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl1_112),
% 2.05/0.65    inference(avatar_component_clause,[],[f2070])).
% 2.05/0.65  fof(f2097,plain,(
% 2.05/0.65    ~spl1_9 | ~spl1_69 | spl1_113),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f2096])).
% 2.05/0.65  fof(f2096,plain,(
% 2.05/0.65    $false | (~spl1_9 | ~spl1_69 | spl1_113)),
% 2.05/0.65    inference(subsumption_resolution,[],[f2095,f1042])).
% 2.05/0.65  fof(f1042,plain,(
% 2.05/0.65    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_69),
% 2.05/0.65    inference(avatar_component_clause,[],[f1041])).
% 2.05/0.65  fof(f1041,plain,(
% 2.05/0.65    spl1_69 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_69])])).
% 2.05/0.65  fof(f2095,plain,(
% 2.05/0.65    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | (~spl1_9 | spl1_113)),
% 2.05/0.65    inference(subsumption_resolution,[],[f2092,f113])).
% 2.05/0.65  fof(f113,plain,(
% 2.05/0.65    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 2.05/0.65    inference(avatar_component_clause,[],[f112])).
% 2.05/0.65  fof(f112,plain,(
% 2.05/0.65    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 2.05/0.65  fof(f2092,plain,(
% 2.05/0.65    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_113),
% 2.05/0.65    inference(resolution,[],[f2076,f43])).
% 2.05/0.65  fof(f43,plain,(
% 2.05/0.65    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f25])).
% 2.05/0.65  fof(f25,plain,(
% 2.05/0.65    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.05/0.65    inference(flattening,[],[f24])).
% 2.05/0.65  fof(f24,plain,(
% 2.05/0.65    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.05/0.65    inference(ennf_transformation,[],[f7])).
% 2.05/0.65  fof(f7,axiom,(
% 2.05/0.65    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.05/0.65  fof(f2076,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | spl1_113),
% 2.05/0.65    inference(avatar_component_clause,[],[f2074])).
% 2.05/0.65  fof(f2074,plain,(
% 2.05/0.65    spl1_113 <=> v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_113])])).
% 2.05/0.65  fof(f2077,plain,(
% 2.05/0.65    spl1_112 | ~spl1_113 | ~spl1_2 | ~spl1_43),
% 2.05/0.65    inference(avatar_split_clause,[],[f658,f639,f55,f2074,f2070])).
% 2.05/0.65  fof(f55,plain,(
% 2.05/0.65    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 2.05/0.65  fof(f639,plain,(
% 2.05/0.65    spl1_43 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_43])])).
% 2.05/0.65  fof(f658,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl1_2 | ~spl1_43)),
% 2.05/0.65    inference(subsumption_resolution,[],[f656,f57])).
% 2.05/0.65  fof(f57,plain,(
% 2.05/0.65    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 2.05/0.65    inference(avatar_component_clause,[],[f55])).
% 2.05/0.65  fof(f656,plain,(
% 2.05/0.65    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl1_43),
% 2.05/0.65    inference(superposition,[],[f42,f641])).
% 2.05/0.65  fof(f641,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | ~spl1_43),
% 2.05/0.65    inference(avatar_component_clause,[],[f639])).
% 2.05/0.65  fof(f42,plain,(
% 2.05/0.65    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f23])).
% 2.05/0.65  fof(f23,plain,(
% 2.05/0.65    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.05/0.65    inference(flattening,[],[f22])).
% 2.05/0.65  fof(f22,plain,(
% 2.05/0.65    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.05/0.65    inference(ennf_transformation,[],[f8])).
% 2.05/0.65  fof(f8,axiom,(
% 2.05/0.65    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 2.05/0.65  fof(f1805,plain,(
% 2.05/0.65    spl1_98 | ~spl1_97),
% 2.05/0.65    inference(avatar_split_clause,[],[f1740,f1717,f1802])).
% 2.05/0.65  fof(f1802,plain,(
% 2.05/0.65    spl1_98 <=> k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_98])])).
% 2.05/0.65  fof(f1717,plain,(
% 2.05/0.65    spl1_97 <=> v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_97])])).
% 2.05/0.65  fof(f1740,plain,(
% 2.05/0.65    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | ~spl1_97),
% 2.05/0.65    inference(resolution,[],[f1719,f37])).
% 2.05/0.65  fof(f1719,plain,(
% 2.05/0.65    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_97),
% 2.05/0.65    inference(avatar_component_clause,[],[f1717])).
% 2.05/0.65  fof(f1720,plain,(
% 2.05/0.65    spl1_97 | ~spl1_2 | ~spl1_25 | ~spl1_63),
% 2.05/0.65    inference(avatar_split_clause,[],[f1675,f892,f338,f55,f1717])).
% 2.05/0.65  fof(f338,plain,(
% 2.05/0.65    spl1_25 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 2.05/0.65  fof(f892,plain,(
% 2.05/0.65    spl1_63 <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_63])])).
% 2.05/0.65  fof(f1675,plain,(
% 2.05/0.65    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_2 | ~spl1_25 | ~spl1_63)),
% 2.05/0.65    inference(subsumption_resolution,[],[f353,f893])).
% 2.05/0.65  fof(f893,plain,(
% 2.05/0.65    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_63),
% 2.05/0.65    inference(avatar_component_clause,[],[f892])).
% 2.05/0.65  fof(f353,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_2 | ~spl1_25)),
% 2.05/0.65    inference(subsumption_resolution,[],[f351,f57])).
% 2.05/0.65  fof(f351,plain,(
% 2.05/0.65    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_25),
% 2.05/0.65    inference(superposition,[],[f42,f340])).
% 2.05/0.65  fof(f340,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl1_25),
% 2.05/0.65    inference(avatar_component_clause,[],[f338])).
% 2.05/0.65  fof(f1054,plain,(
% 2.05/0.65    ~spl1_9 | spl1_69),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f1053])).
% 2.05/0.65  fof(f1053,plain,(
% 2.05/0.65    $false | (~spl1_9 | spl1_69)),
% 2.05/0.65    inference(subsumption_resolution,[],[f1050,f113])).
% 2.05/0.65  fof(f1050,plain,(
% 2.05/0.65    ~v1_relat_1(k1_xboole_0) | spl1_69),
% 2.05/0.65    inference(resolution,[],[f1043,f38])).
% 2.05/0.65  fof(f38,plain,(
% 2.05/0.65    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f18])).
% 2.05/0.65  fof(f18,plain,(
% 2.05/0.65    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f6])).
% 2.05/0.65  fof(f6,axiom,(
% 2.05/0.65    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.05/0.65  fof(f1043,plain,(
% 2.05/0.65    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl1_69),
% 2.05/0.65    inference(avatar_component_clause,[],[f1041])).
% 2.05/0.65  fof(f910,plain,(
% 2.05/0.65    ~spl1_9 | ~spl1_22 | spl1_63),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f909])).
% 2.05/0.65  fof(f909,plain,(
% 2.05/0.65    $false | (~spl1_9 | ~spl1_22 | spl1_63)),
% 2.05/0.65    inference(subsumption_resolution,[],[f908,f275])).
% 2.05/0.65  fof(f275,plain,(
% 2.05/0.65    v1_relat_1(k4_relat_1(sK0)) | ~spl1_22),
% 2.05/0.65    inference(avatar_component_clause,[],[f274])).
% 2.05/0.65  fof(f274,plain,(
% 2.05/0.65    spl1_22 <=> v1_relat_1(k4_relat_1(sK0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 2.05/0.65  fof(f908,plain,(
% 2.05/0.65    ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_9 | spl1_63)),
% 2.05/0.65    inference(subsumption_resolution,[],[f905,f113])).
% 2.05/0.65  fof(f905,plain,(
% 2.05/0.65    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_63),
% 2.05/0.65    inference(resolution,[],[f894,f43])).
% 2.05/0.65  fof(f894,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | spl1_63),
% 2.05/0.65    inference(avatar_component_clause,[],[f892])).
% 2.05/0.65  fof(f833,plain,(
% 2.05/0.65    spl1_55 | ~spl1_9 | ~spl1_32),
% 2.05/0.65    inference(avatar_split_clause,[],[f443,f417,f112,f830])).
% 2.05/0.65  fof(f830,plain,(
% 2.05/0.65    spl1_55 <=> k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_55])])).
% 2.05/0.65  fof(f417,plain,(
% 2.05/0.65    spl1_32 <=> ! [X2] : (k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0) | ~v1_relat_1(X2))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).
% 2.05/0.65  fof(f443,plain,(
% 2.05/0.65    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl1_9 | ~spl1_32)),
% 2.05/0.65    inference(resolution,[],[f418,f113])).
% 2.05/0.65  fof(f418,plain,(
% 2.05/0.65    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0)) ) | ~spl1_32),
% 2.05/0.65    inference(avatar_component_clause,[],[f417])).
% 2.05/0.65  fof(f695,plain,(
% 2.05/0.65    spl1_49 | ~spl1_1 | ~spl1_30),
% 2.05/0.65    inference(avatar_split_clause,[],[f434,f392,f50,f692])).
% 2.05/0.65  fof(f692,plain,(
% 2.05/0.65    spl1_49 <=> k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_49])])).
% 2.05/0.65  fof(f50,plain,(
% 2.05/0.65    spl1_1 <=> v1_relat_1(sK0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 2.05/0.65  fof(f392,plain,(
% 2.05/0.65    spl1_30 <=> ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 2.05/0.65  fof(f434,plain,(
% 2.05/0.65    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) | (~spl1_1 | ~spl1_30)),
% 2.05/0.65    inference(resolution,[],[f393,f52])).
% 2.05/0.65  fof(f52,plain,(
% 2.05/0.65    v1_relat_1(sK0) | ~spl1_1),
% 2.05/0.65    inference(avatar_component_clause,[],[f50])).
% 2.05/0.65  fof(f393,plain,(
% 2.05/0.65    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0))) ) | ~spl1_30),
% 2.05/0.65    inference(avatar_component_clause,[],[f392])).
% 2.05/0.65  fof(f642,plain,(
% 2.05/0.65    spl1_43 | ~spl1_9 | ~spl1_42),
% 2.05/0.65    inference(avatar_split_clause,[],[f618,f604,f112,f639])).
% 2.05/0.65  fof(f604,plain,(
% 2.05/0.65    spl1_42 <=> ! [X1] : (k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0)) | ~v1_relat_1(X1))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).
% 2.05/0.65  fof(f618,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl1_9 | ~spl1_42)),
% 2.05/0.65    inference(resolution,[],[f605,f113])).
% 2.05/0.65  fof(f605,plain,(
% 2.05/0.65    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0))) ) | ~spl1_42),
% 2.05/0.65    inference(avatar_component_clause,[],[f604])).
% 2.05/0.65  fof(f606,plain,(
% 2.05/0.65    spl1_42 | ~spl1_11),
% 2.05/0.65    inference(avatar_split_clause,[],[f146,f131,f604])).
% 2.05/0.65  fof(f131,plain,(
% 2.05/0.65    spl1_11 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 2.05/0.65  fof(f146,plain,(
% 2.05/0.65    ( ! [X1] : (k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(X1),k1_xboole_0)) | ~v1_relat_1(X1)) ) | ~spl1_11),
% 2.05/0.65    inference(resolution,[],[f132,f38])).
% 2.05/0.65  fof(f132,plain,(
% 2.05/0.65    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl1_11),
% 2.05/0.65    inference(avatar_component_clause,[],[f131])).
% 2.05/0.65  fof(f506,plain,(
% 2.05/0.65    spl1_36 | ~spl1_1 | ~spl1_24),
% 2.05/0.65    inference(avatar_split_clause,[],[f336,f317,f50,f503])).
% 2.05/0.65  fof(f503,plain,(
% 2.05/0.65    spl1_36 <=> k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).
% 2.05/0.65  fof(f317,plain,(
% 2.05/0.65    spl1_24 <=> ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2))))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 2.05/0.65  fof(f336,plain,(
% 2.05/0.65    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) | (~spl1_1 | ~spl1_24)),
% 2.05/0.65    inference(resolution,[],[f318,f52])).
% 2.05/0.65  fof(f318,plain,(
% 2.05/0.65    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2)))) ) | ~spl1_24),
% 2.05/0.65    inference(avatar_component_clause,[],[f317])).
% 2.05/0.65  fof(f419,plain,(
% 2.05/0.65    spl1_32 | ~spl1_8 | ~spl1_9),
% 2.05/0.65    inference(avatar_split_clause,[],[f170,f112,f102,f417])).
% 2.05/0.65  fof(f102,plain,(
% 2.05/0.65    spl1_8 <=> k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 2.05/0.65  fof(f170,plain,(
% 2.05/0.65    ( ! [X2] : (k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k1_xboole_0) | ~v1_relat_1(X2)) ) | (~spl1_8 | ~spl1_9)),
% 2.05/0.65    inference(forward_demodulation,[],[f166,f104])).
% 2.05/0.65  fof(f104,plain,(
% 2.05/0.65    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_8),
% 2.05/0.65    inference(avatar_component_clause,[],[f102])).
% 2.05/0.65  fof(f166,plain,(
% 2.05/0.65    ( ! [X2] : (k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(k1_xboole_0))) | ~v1_relat_1(X2)) ) | ~spl1_9),
% 2.05/0.65    inference(resolution,[],[f98,f113])).
% 2.05/0.65  fof(f98,plain,(
% 2.05/0.65    ( ! [X2,X3] : (~v1_relat_1(X3) | k4_relat_1(k5_relat_1(k4_relat_1(X3),X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(k4_relat_1(X3))) | ~v1_relat_1(X2)) )),
% 2.05/0.65    inference(resolution,[],[f41,f38])).
% 2.05/0.65  fof(f41,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f21])).
% 2.05/0.65  fof(f21,plain,(
% 2.05/0.65    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f11])).
% 2.05/0.65  fof(f11,axiom,(
% 2.05/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 2.05/0.65  fof(f407,plain,(
% 2.05/0.65    spl1_30 | ~spl1_2),
% 2.05/0.65    inference(avatar_split_clause,[],[f159,f55,f392])).
% 2.05/0.65  fof(f159,plain,(
% 2.05/0.65    ( ! [X0] : (k4_relat_1(k5_relat_1(k1_xboole_0,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl1_2),
% 2.05/0.65    inference(resolution,[],[f97,f57])).
% 2.05/0.65  fof(f97,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~v1_xboole_0(X1) | k4_relat_1(k5_relat_1(X1,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.05/0.65    inference(resolution,[],[f41,f36])).
% 2.05/0.65  fof(f36,plain,(
% 2.05/0.65    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f16])).
% 2.05/0.65  fof(f16,plain,(
% 2.05/0.65    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f5])).
% 2.05/0.65  fof(f5,axiom,(
% 2.05/0.65    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.05/0.65  fof(f341,plain,(
% 2.05/0.65    spl1_25 | ~spl1_11 | ~spl1_22),
% 2.05/0.65    inference(avatar_split_clause,[],[f308,f274,f131,f338])).
% 2.05/0.65  fof(f308,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl1_11 | ~spl1_22)),
% 2.05/0.65    inference(resolution,[],[f275,f132])).
% 2.05/0.65  fof(f319,plain,(
% 2.05/0.65    spl1_24 | ~spl1_9),
% 2.05/0.65    inference(avatar_split_clause,[],[f150,f112,f317])).
% 2.05/0.65  fof(f150,plain,(
% 2.05/0.65    ( ! [X2] : (~v1_relat_1(X2) | k5_relat_1(k1_xboole_0,X2) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,X2)))) ) | ~spl1_9),
% 2.05/0.65    inference(resolution,[],[f79,f113])).
% 2.05/0.65  fof(f79,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 2.05/0.65    inference(resolution,[],[f43,f39])).
% 2.05/0.65  fof(f39,plain,(
% 2.05/0.65    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f19])).
% 2.05/0.65  fof(f19,plain,(
% 2.05/0.65    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.05/0.65    inference(ennf_transformation,[],[f9])).
% 2.05/0.65  fof(f9,axiom,(
% 2.05/0.65    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.05/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.05/0.65  fof(f293,plain,(
% 2.05/0.65    ~spl1_1 | spl1_22),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f292])).
% 2.05/0.65  fof(f292,plain,(
% 2.05/0.65    $false | (~spl1_1 | spl1_22)),
% 2.05/0.65    inference(subsumption_resolution,[],[f289,f52])).
% 2.05/0.65  fof(f289,plain,(
% 2.05/0.65    ~v1_relat_1(sK0) | spl1_22),
% 2.05/0.65    inference(resolution,[],[f276,f38])).
% 2.05/0.65  fof(f276,plain,(
% 2.05/0.65    ~v1_relat_1(k4_relat_1(sK0)) | spl1_22),
% 2.05/0.65    inference(avatar_component_clause,[],[f274])).
% 2.05/0.65  fof(f258,plain,(
% 2.05/0.65    spl1_7 | ~spl1_17),
% 2.05/0.65    inference(avatar_split_clause,[],[f235,f208,f90])).
% 2.05/0.65  fof(f90,plain,(
% 2.05/0.65    spl1_7 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 2.05/0.65  fof(f208,plain,(
% 2.05/0.65    spl1_17 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 2.05/0.65  fof(f235,plain,(
% 2.05/0.65    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl1_17),
% 2.05/0.65    inference(resolution,[],[f210,f37])).
% 2.05/0.65  fof(f210,plain,(
% 2.05/0.65    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_17),
% 2.05/0.65    inference(avatar_component_clause,[],[f208])).
% 2.05/0.65  fof(f227,plain,(
% 2.05/0.65    ~spl1_1 | ~spl1_9 | spl1_18),
% 2.05/0.65    inference(avatar_contradiction_clause,[],[f226])).
% 2.05/0.65  fof(f226,plain,(
% 2.05/0.65    $false | (~spl1_1 | ~spl1_9 | spl1_18)),
% 2.05/0.65    inference(subsumption_resolution,[],[f225,f52])).
% 2.05/0.65  fof(f225,plain,(
% 2.05/0.65    ~v1_relat_1(sK0) | (~spl1_9 | spl1_18)),
% 2.05/0.65    inference(subsumption_resolution,[],[f222,f113])).
% 2.05/0.65  fof(f222,plain,(
% 2.05/0.65    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl1_18),
% 2.05/0.65    inference(resolution,[],[f214,f43])).
% 2.05/0.65  fof(f214,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_18),
% 2.05/0.65    inference(avatar_component_clause,[],[f212])).
% 2.05/0.65  fof(f212,plain,(
% 2.05/0.65    spl1_18 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 2.05/0.65  fof(f215,plain,(
% 2.05/0.65    spl1_17 | ~spl1_18 | ~spl1_2 | ~spl1_13),
% 2.05/0.65    inference(avatar_split_clause,[],[f164,f155,f55,f212,f208])).
% 2.05/0.65  fof(f155,plain,(
% 2.05/0.65    spl1_13 <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 2.05/0.65  fof(f164,plain,(
% 2.05/0.65    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_2 | ~spl1_13)),
% 2.05/0.65    inference(subsumption_resolution,[],[f163,f57])).
% 2.05/0.65  fof(f163,plain,(
% 2.05/0.65    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_13),
% 2.05/0.65    inference(superposition,[],[f42,f157])).
% 2.05/0.65  fof(f157,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl1_13),
% 2.05/0.65    inference(avatar_component_clause,[],[f155])).
% 2.05/0.65  fof(f158,plain,(
% 2.05/0.65    spl1_13 | ~spl1_1 | ~spl1_11),
% 2.05/0.65    inference(avatar_split_clause,[],[f148,f131,f50,f155])).
% 2.05/0.65  fof(f148,plain,(
% 2.05/0.65    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_1 | ~spl1_11)),
% 2.05/0.65    inference(resolution,[],[f132,f52])).
% 2.05/0.65  fof(f138,plain,(
% 2.05/0.65    spl1_11 | ~spl1_10),
% 2.05/0.65    inference(avatar_split_clause,[],[f129,f116,f131])).
% 2.05/0.65  fof(f116,plain,(
% 2.05/0.65    spl1_10 <=> ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0))),
% 2.05/0.65    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 2.05/0.65  fof(f129,plain,(
% 2.05/0.65    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl1_10),
% 2.05/0.65    inference(subsumption_resolution,[],[f128,f35])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f4])).
% 2.05/0.66  fof(f4,axiom,(
% 2.05/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.05/0.66  fof(f128,plain,(
% 2.05/0.66    ( ! [X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(X1,k1_xboole_0))) | k1_xboole_0 = k2_relat_1(k5_relat_1(X1,k1_xboole_0))) ) | ~spl1_10),
% 2.05/0.66    inference(resolution,[],[f117,f46])).
% 2.05/0.66  fof(f46,plain,(
% 2.05/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f29])).
% 2.05/0.66  fof(f29,plain,(
% 2.05/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.66    inference(flattening,[],[f28])).
% 2.05/0.66  fof(f28,plain,(
% 2.05/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.66    inference(nnf_transformation,[],[f3])).
% 2.05/0.66  fof(f3,axiom,(
% 2.05/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.66  fof(f117,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_10),
% 2.05/0.66    inference(avatar_component_clause,[],[f116])).
% 2.05/0.66  fof(f123,plain,(
% 2.05/0.66    ~spl1_2 | spl1_9),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f122])).
% 2.05/0.66  fof(f122,plain,(
% 2.05/0.66    $false | (~spl1_2 | spl1_9)),
% 2.05/0.66    inference(subsumption_resolution,[],[f120,f57])).
% 2.05/0.66  fof(f120,plain,(
% 2.05/0.66    ~v1_xboole_0(k1_xboole_0) | spl1_9),
% 2.05/0.66    inference(resolution,[],[f114,f36])).
% 2.05/0.66  fof(f114,plain,(
% 2.05/0.66    ~v1_relat_1(k1_xboole_0) | spl1_9),
% 2.05/0.66    inference(avatar_component_clause,[],[f112])).
% 2.05/0.66  fof(f118,plain,(
% 2.05/0.66    ~spl1_9 | spl1_10 | ~spl1_4),
% 2.05/0.66    inference(avatar_split_clause,[],[f95,f65,f116,f112])).
% 2.05/0.66  fof(f65,plain,(
% 2.05/0.66    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 2.05/0.66  fof(f95,plain,(
% 2.05/0.66    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl1_4),
% 2.05/0.66    inference(superposition,[],[f40,f67])).
% 2.05/0.66  fof(f67,plain,(
% 2.05/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 2.05/0.66    inference(avatar_component_clause,[],[f65])).
% 2.05/0.66  fof(f40,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.05/0.66    inference(cnf_transformation,[],[f20])).
% 2.05/0.66  fof(f20,plain,(
% 2.05/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f10])).
% 2.05/0.66  fof(f10,axiom,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.05/0.66  fof(f105,plain,(
% 2.05/0.66    spl1_8 | ~spl1_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f96,f55,f102])).
% 2.05/0.66  fof(f96,plain,(
% 2.05/0.66    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) | ~spl1_2),
% 2.05/0.66    inference(resolution,[],[f71,f57])).
% 2.05/0.66  fof(f71,plain,(
% 2.05/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.05/0.66    inference(resolution,[],[f39,f36])).
% 2.05/0.66  fof(f93,plain,(
% 2.05/0.66    ~spl1_6 | ~spl1_7),
% 2.05/0.66    inference(avatar_split_clause,[],[f31,f90,f86])).
% 2.05/0.66  fof(f86,plain,(
% 2.05/0.66    spl1_6 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 2.05/0.66  fof(f31,plain,(
% 2.05/0.66    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.05/0.66    inference(cnf_transformation,[],[f27])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).
% 2.05/0.66  fof(f26,plain,(
% 2.05/0.66    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f15,plain,(
% 2.05/0.66    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 2.05/0.66    inference(ennf_transformation,[],[f14])).
% 2.05/0.66  fof(f14,negated_conjecture,(
% 2.05/0.66    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.05/0.66    inference(negated_conjecture,[],[f13])).
% 2.05/0.66  fof(f13,conjecture,(
% 2.05/0.66    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 2.05/0.66  fof(f68,plain,(
% 2.05/0.66    spl1_4),
% 2.05/0.66    inference(avatar_split_clause,[],[f34,f65])).
% 2.05/0.66  fof(f34,plain,(
% 2.05/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.05/0.66    inference(cnf_transformation,[],[f12])).
% 2.05/0.66  fof(f12,axiom,(
% 2.05/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 2.05/0.66  fof(f58,plain,(
% 2.05/0.66    spl1_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f32,f55])).
% 2.05/0.66  fof(f32,plain,(
% 2.05/0.66    v1_xboole_0(k1_xboole_0)),
% 2.05/0.66    inference(cnf_transformation,[],[f1])).
% 2.05/0.66  fof(f1,axiom,(
% 2.05/0.66    v1_xboole_0(k1_xboole_0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.05/0.66  fof(f53,plain,(
% 2.05/0.66    spl1_1),
% 2.05/0.66    inference(avatar_split_clause,[],[f30,f50])).
% 2.05/0.66  fof(f30,plain,(
% 2.05/0.66    v1_relat_1(sK0)),
% 2.05/0.66    inference(cnf_transformation,[],[f27])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (7065)------------------------------
% 2.05/0.66  % (7065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (7065)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (7065)Memory used [KB]: 7675
% 2.05/0.66  % (7065)Time elapsed: 0.201 s
% 2.05/0.66  % (7065)------------------------------
% 2.05/0.66  % (7065)------------------------------
% 2.05/0.66  % (7062)Success in time 0.281 s
%------------------------------------------------------------------------------

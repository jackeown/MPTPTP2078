%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:09 EST 2020

% Result     : Theorem 5.13s
% Output     : Refutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 492 expanded)
%              Number of leaves         :   49 ( 173 expanded)
%              Depth                    :   14
%              Number of atoms          :  624 (1590 expanded)
%              Number of equality atoms :   70 ( 221 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f138,f143,f148,f153,f159,f369,f432,f1979,f2028,f2038,f2186,f2241,f2281,f2365,f2517])).

fof(f2517,plain,
    ( ~ spl12_3
    | spl12_40
    | ~ spl12_47 ),
    inference(avatar_contradiction_clause,[],[f2516])).

fof(f2516,plain,
    ( $false
    | ~ spl12_3
    | spl12_40
    | ~ spl12_47 ),
    inference(subsumption_resolution,[],[f2515,f142])).

fof(f142,plain,
    ( v1_relat_1(sK1)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f2515,plain,
    ( ~ v1_relat_1(sK1)
    | spl12_40
    | ~ spl12_47 ),
    inference(subsumption_resolution,[],[f2500,f2280])).

fof(f2280,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl12_40 ),
    inference(avatar_component_clause,[],[f2278])).

fof(f2278,plain,
    ( spl12_40
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f2500,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_47 ),
    inference(resolution,[],[f2384,f232])).

fof(f232,plain,(
    ! [X4] :
      ( r1_tarski(k1_relat_1(X4),k3_relat_1(X4))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f116,f115])).

fof(f115,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f80,f114])).

fof(f114,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f91,f92])).

fof(f92,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f80,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f89,f114])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2384,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK1),X0)
        | r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl12_47 ),
    inference(resolution,[],[f2364,f1854])).

fof(f1854,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X3)
      | r1_tarski(X4,X2)
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f119,f508])).

fof(f508,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f502,f125])).

fof(f125,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f502,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f169,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f110,f114])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f169,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),X2)
      | k3_tarski(k1_enumset1(X2,X2,X3)) = X2 ) ),
    inference(resolution,[],[f99,f116])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f108,f114])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f2364,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f2362,plain,
    ( spl12_47
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f2365,plain,
    ( spl12_47
    | ~ spl12_23 ),
    inference(avatar_split_clause,[],[f2340,f2035,f2362])).

fof(f2035,plain,
    ( spl12_23
  <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f2340,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_23 ),
    inference(trivial_inequality_removal,[],[f2332])).

fof(f2332,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_23 ),
    inference(superposition,[],[f118,f2037])).

fof(f2037,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f104,f90])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2281,plain,
    ( ~ spl12_40
    | spl12_1
    | ~ spl12_4
    | ~ spl12_37 ),
    inference(avatar_split_clause,[],[f2276,f2238,f145,f130,f2278])).

fof(f130,plain,
    ( spl12_1
  <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f145,plain,
    ( spl12_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f2238,plain,
    ( spl12_37
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f2276,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f2275,f147])).

fof(f147,plain,
    ( v1_relat_1(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f2275,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | spl12_1
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f2272,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f2272,plain,
    ( r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ spl12_37 ),
    inference(resolution,[],[f2240,f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | r1_tarski(k3_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f121,f115])).

fof(f2240,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f2238])).

fof(f2241,plain,
    ( spl12_37
    | ~ spl12_3
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f2236,f2183,f140,f2238])).

fof(f2183,plain,
    ( spl12_32
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f2236,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f2223,f142])).

fof(f2223,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_32 ),
    inference(resolution,[],[f2185,f231])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k2_relat_1(X2))
      | r1_tarski(X3,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f119,f115])).

fof(f2185,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f2183])).

fof(f2186,plain,
    ( spl12_32
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f2161,f2025,f2183])).

fof(f2025,plain,
    ( spl12_22
  <=> k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f2161,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_22 ),
    inference(trivial_inequality_removal,[],[f2153])).

fof(f2153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_22 ),
    inference(superposition,[],[f118,f2027])).

fof(f2027,plain,
    ( k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f2025])).

fof(f2038,plain,
    ( spl12_23
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_9
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f2033,f1976,f341,f145,f140,f2035])).

fof(f341,plain,
    ( spl12_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f1976,plain,
    ( spl12_19
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f2033,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_9
    | ~ spl12_19 ),
    inference(forward_demodulation,[],[f2032,f343])).

fof(f343,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f341])).

fof(f2032,plain,
    ( k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_9
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f2031,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2031,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)))
    | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_9
    | ~ spl12_19 ),
    inference(forward_demodulation,[],[f2030,f343])).

fof(f2030,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)))
    | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f2029,f142])).

fof(f2029,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)))
    | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f1998,f147])).

fof(f1998,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_19 ),
    inference(superposition,[],[f260,f1978])).

fof(f1978,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f1976])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k1_relat_1(X1),k1_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f99])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(f2028,plain,
    ( spl12_22
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_11
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f2023,f1976,f404,f145,f140,f2025])).

fof(f404,plain,
    ( spl12_11
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f2023,plain,
    ( k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_11
    | ~ spl12_19 ),
    inference(forward_demodulation,[],[f2022,f406])).

fof(f406,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f404])).

fof(f2022,plain,
    ( k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_11
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f2021,f78])).

fof(f2021,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_11
    | ~ spl12_19 ),
    inference(forward_demodulation,[],[f2020,f406])).

fof(f2020,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f2019,f142])).

fof(f2019,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_4
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f1997,f147])).

fof(f1997,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))
    | ~ v1_relat_1(sK0)
    | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_19 ),
    inference(superposition,[],[f247,f1978])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k2_relat_1(X1),k2_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | k2_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k2_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f81,f99])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f1979,plain,
    ( spl12_19
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f1954,f135,f1976])).

fof(f135,plain,
    ( spl12_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1954,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ spl12_2 ),
    inference(resolution,[],[f1930,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f99,f78])).

fof(f1930,plain,
    ( ! [X1] : r1_tarski(k6_subset_1(sK0,sK1),X1)
    | ~ spl12_2 ),
    inference(resolution,[],[f1911,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f109,f90,f114])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1911,plain,
    ( ! [X0] : r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,X0)))
    | ~ spl12_2 ),
    inference(resolution,[],[f1906,f116])).

fof(f1906,plain,
    ( ! [X120] :
        ( ~ r1_tarski(sK1,X120)
        | r1_tarski(sK0,X120) )
    | ~ spl12_2 ),
    inference(resolution,[],[f1854,f137])).

fof(f137,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f432,plain,
    ( spl12_11
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f429,f156,f404])).

fof(f156,plain,
    ( spl12_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f429,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl12_6 ),
    inference(resolution,[],[f401,f191])).

fof(f191,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(sK3(sK2(X1)),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f162,f84])).

fof(f84,plain,(
    ! [X0] : r2_hidden(X0,sK3(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK3(X0))
          | r2_tarski(X2,sK3(X0))
          | ~ r1_tarski(X2,sK3(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK4(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK4(X0,X3),sK3(X0)) )
          | ~ r2_hidden(X3,sK3(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK3(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK3(X0)) )
      & r2_hidden(X0,sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f53,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK3(X0))
            | r2_tarski(X2,sK3(X0))
            | ~ r1_tarski(X2,sK3(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK3(X0)) )
            | ~ r2_hidden(X3,sK3(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK3(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK3(X0)) )
        & r2_hidden(X0,sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,sK3(X0)) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK4(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK4(X0,X3),sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X3),X2)
      | ~ r1_xboole_0(X2,X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f95,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f401,plain,
    ( ! [X3] : r1_xboole_0(X3,k2_relat_1(k1_xboole_0))
    | ~ spl12_6 ),
    inference(resolution,[],[f345,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f345,plain,
    ( ! [X4] : ~ r2_hidden(X4,k2_relat_1(k1_xboole_0))
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f338,f158])).

fof(f158,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f338,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f316,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f57])).

fof(f57,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK6(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f316,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f304,f128])).

fof(f128,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f304,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f215,f77])).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f215,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(sK3(sK10(X3)),X3)
      | ~ r2_hidden(X4,X3) ) ),
    inference(resolution,[],[f165,f84])).

fof(f165,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(sK10(X11),X10)
      | ~ r1_xboole_0(X10,X11)
      | ~ r2_hidden(X12,X11) ) ),
    inference(resolution,[],[f95,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK10(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK10(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f68])).

fof(f68,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK10(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK10(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f369,plain,(
    spl12_9 ),
    inference(avatar_split_clause,[],[f366,f341])).

fof(f366,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f337,f191])).

fof(f337,plain,(
    ! [X3] : r1_xboole_0(X3,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f316,f94])).

fof(f159,plain,
    ( spl12_6
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f154,f150,f156])).

fof(f150,plain,
    ( spl12_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f154,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl12_5 ),
    inference(resolution,[],[f79,f152])).

fof(f152,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f153,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f76,f150])).

fof(f76,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f148,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f72,f145])).

fof(f72,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f143,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f73,f140])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f138,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f74,f135])).

fof(f74,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f133,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f75,f130])).

fof(f75,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.54  % (10508)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.56  % (10518)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (10532)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (10524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.57  % (10510)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (10532)Refutation not found, incomplete strategy% (10532)------------------------------
% 0.20/0.57  % (10532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (10509)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.57  % (10533)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (10533)Refutation not found, incomplete strategy% (10533)------------------------------
% 0.20/0.57  % (10533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (10516)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.57  % (10533)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (10533)Memory used [KB]: 1663
% 1.44/0.57  % (10533)Time elapsed: 0.143 s
% 1.44/0.57  % (10533)------------------------------
% 1.44/0.57  % (10533)------------------------------
% 1.44/0.58  % (10522)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.58  % (10532)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.58  
% 1.44/0.58  % (10532)Memory used [KB]: 10746
% 1.44/0.58  % (10532)Time elapsed: 0.144 s
% 1.44/0.58  % (10532)------------------------------
% 1.44/0.58  % (10532)------------------------------
% 1.44/0.58  % (10527)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.58  % (10507)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.44/0.58  % (10515)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.58  % (10506)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.44/0.59  % (10505)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.59  % (10530)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.59  % (10519)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.78/0.60  % (10529)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.78/0.60  % (10526)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.78/0.60  % (10511)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.60  % (10521)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.60  % (10531)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.78/0.61  % (10523)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.78/0.61  % (10513)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.78/0.61  % (10528)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.78/0.61  % (10525)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.78/0.61  % (10514)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.78/0.61  % (10504)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.62  % (10514)Refutation not found, incomplete strategy% (10514)------------------------------
% 1.78/0.62  % (10514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.62  % (10514)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.62  
% 1.78/0.62  % (10514)Memory used [KB]: 10746
% 1.78/0.62  % (10514)Time elapsed: 0.191 s
% 1.78/0.62  % (10514)------------------------------
% 1.78/0.62  % (10514)------------------------------
% 1.78/0.62  % (10517)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.78/0.63  % (10520)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.78/0.63  % (10512)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.78/0.65  % (10520)Refutation not found, incomplete strategy% (10520)------------------------------
% 1.78/0.65  % (10520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.65  % (10520)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.65  
% 1.78/0.65  % (10520)Memory used [KB]: 10746
% 1.78/0.65  % (10520)Time elapsed: 0.203 s
% 1.78/0.65  % (10520)------------------------------
% 1.78/0.65  % (10520)------------------------------
% 2.66/0.77  % (10571)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.66/0.77  % (10572)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.66/0.80  % (10507)Refutation not found, incomplete strategy% (10507)------------------------------
% 2.66/0.80  % (10507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.81  % (10573)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.27/0.82  % (10507)Termination reason: Refutation not found, incomplete strategy
% 3.27/0.82  
% 3.27/0.82  % (10507)Memory used [KB]: 6140
% 3.27/0.82  % (10507)Time elapsed: 0.376 s
% 3.27/0.82  % (10507)------------------------------
% 3.27/0.82  % (10507)------------------------------
% 3.27/0.83  % (10573)Refutation not found, incomplete strategy% (10573)------------------------------
% 3.27/0.83  % (10573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.83  % (10573)Termination reason: Refutation not found, incomplete strategy
% 3.27/0.83  
% 3.27/0.83  % (10573)Memory used [KB]: 6140
% 3.27/0.83  % (10573)Time elapsed: 0.163 s
% 3.27/0.83  % (10573)------------------------------
% 3.27/0.83  % (10573)------------------------------
% 3.27/0.86  % (10574)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.27/0.86  % (10528)Time limit reached!
% 3.27/0.86  % (10528)------------------------------
% 3.27/0.86  % (10528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.86  % (10528)Termination reason: Time limit
% 3.27/0.86  
% 3.27/0.86  % (10528)Memory used [KB]: 12920
% 3.27/0.86  % (10528)Time elapsed: 0.432 s
% 3.27/0.86  % (10528)------------------------------
% 3.27/0.86  % (10528)------------------------------
% 3.27/0.88  % (10506)Time limit reached!
% 3.27/0.88  % (10506)------------------------------
% 3.27/0.88  % (10506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.88  % (10506)Termination reason: Time limit
% 3.27/0.88  
% 3.27/0.88  % (10506)Memory used [KB]: 6524
% 3.27/0.88  % (10506)Time elapsed: 0.413 s
% 3.27/0.88  % (10506)------------------------------
% 3.27/0.88  % (10506)------------------------------
% 3.88/0.93  % (10586)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.88/0.93  % (10510)Time limit reached!
% 3.88/0.93  % (10510)------------------------------
% 3.88/0.93  % (10510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.88/0.93  % (10510)Termination reason: Time limit
% 3.88/0.93  
% 3.88/0.93  % (10510)Memory used [KB]: 14200
% 3.88/0.93  % (10510)Time elapsed: 0.502 s
% 3.88/0.93  % (10510)------------------------------
% 3.88/0.93  % (10510)------------------------------
% 3.88/0.94  % (10518)Time limit reached!
% 3.88/0.94  % (10518)------------------------------
% 3.88/0.94  % (10518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.88/0.94  % (10518)Termination reason: Time limit
% 3.88/0.94  % (10518)Termination phase: Saturation
% 3.88/0.94  
% 3.88/0.94  % (10518)Memory used [KB]: 4861
% 3.88/0.94  % (10518)Time elapsed: 0.500 s
% 3.88/0.94  % (10518)------------------------------
% 3.88/0.94  % (10518)------------------------------
% 3.88/0.97  % (10593)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.36/0.98  % (10604)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.50/1.02  % (10616)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.13/1.04  % (10572)Refutation found. Thanks to Tanya!
% 5.13/1.04  % SZS status Theorem for theBenchmark
% 5.13/1.05  % SZS output start Proof for theBenchmark
% 5.13/1.05  fof(f2519,plain,(
% 5.13/1.05    $false),
% 5.13/1.05    inference(avatar_sat_refutation,[],[f133,f138,f143,f148,f153,f159,f369,f432,f1979,f2028,f2038,f2186,f2241,f2281,f2365,f2517])).
% 5.13/1.05  fof(f2517,plain,(
% 5.13/1.05    ~spl12_3 | spl12_40 | ~spl12_47),
% 5.13/1.05    inference(avatar_contradiction_clause,[],[f2516])).
% 5.13/1.05  fof(f2516,plain,(
% 5.13/1.05    $false | (~spl12_3 | spl12_40 | ~spl12_47)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2515,f142])).
% 5.13/1.05  fof(f142,plain,(
% 5.13/1.05    v1_relat_1(sK1) | ~spl12_3),
% 5.13/1.05    inference(avatar_component_clause,[],[f140])).
% 5.13/1.05  fof(f140,plain,(
% 5.13/1.05    spl12_3 <=> v1_relat_1(sK1)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 5.13/1.05  fof(f2515,plain,(
% 5.13/1.05    ~v1_relat_1(sK1) | (spl12_40 | ~spl12_47)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2500,f2280])).
% 5.13/1.05  fof(f2280,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl12_40),
% 5.13/1.05    inference(avatar_component_clause,[],[f2278])).
% 5.13/1.05  fof(f2278,plain,(
% 5.13/1.05    spl12_40 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).
% 5.13/1.05  fof(f2500,plain,(
% 5.13/1.05    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl12_47),
% 5.13/1.05    inference(resolution,[],[f2384,f232])).
% 5.13/1.05  fof(f232,plain,(
% 5.13/1.05    ( ! [X4] : (r1_tarski(k1_relat_1(X4),k3_relat_1(X4)) | ~v1_relat_1(X4)) )),
% 5.13/1.05    inference(superposition,[],[f116,f115])).
% 5.13/1.05  fof(f115,plain,(
% 5.13/1.05    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(definition_unfolding,[],[f80,f114])).
% 5.13/1.05  fof(f114,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 5.13/1.05    inference(definition_unfolding,[],[f91,f92])).
% 5.13/1.05  fof(f92,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f13])).
% 5.13/1.05  fof(f13,axiom,(
% 5.13/1.05    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 5.13/1.05  fof(f91,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.13/1.05    inference(cnf_transformation,[],[f14])).
% 5.13/1.05  fof(f14,axiom,(
% 5.13/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.13/1.05  fof(f80,plain,(
% 5.13/1.05    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f31])).
% 5.13/1.05  fof(f31,plain,(
% 5.13/1.05    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 5.13/1.05    inference(ennf_transformation,[],[f20])).
% 5.13/1.05  fof(f20,axiom,(
% 5.13/1.05    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 5.13/1.05  fof(f116,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 5.13/1.05    inference(definition_unfolding,[],[f89,f114])).
% 5.13/1.05  fof(f89,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 5.13/1.05    inference(cnf_transformation,[],[f11])).
% 5.13/1.05  fof(f11,axiom,(
% 5.13/1.05    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 5.13/1.05  fof(f2384,plain,(
% 5.13/1.05    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl12_47),
% 5.13/1.05    inference(resolution,[],[f2364,f1854])).
% 5.13/1.05  fof(f1854,plain,(
% 5.13/1.05    ( ! [X4,X2,X3] : (~r1_tarski(X4,X3) | r1_tarski(X4,X2) | ~r1_tarski(X3,X2)) )),
% 5.13/1.05    inference(superposition,[],[f119,f508])).
% 5.13/1.05  fof(f508,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0)) )),
% 5.13/1.05    inference(subsumption_resolution,[],[f502,f125])).
% 5.13/1.05  fof(f125,plain,(
% 5.13/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.13/1.05    inference(equality_resolution,[],[f98])).
% 5.13/1.05  fof(f98,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.13/1.05    inference(cnf_transformation,[],[f60])).
% 5.13/1.05  fof(f60,plain,(
% 5.13/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.13/1.05    inference(flattening,[],[f59])).
% 5.13/1.05  fof(f59,plain,(
% 5.13/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 5.13/1.05    inference(nnf_transformation,[],[f4])).
% 5.13/1.05  fof(f4,axiom,(
% 5.13/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.13/1.05  fof(f502,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 5.13/1.05    inference(resolution,[],[f169,f121])).
% 5.13/1.05  fof(f121,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(definition_unfolding,[],[f110,f114])).
% 5.13/1.05  fof(f110,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f44])).
% 5.13/1.05  fof(f44,plain,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 5.13/1.05    inference(flattening,[],[f43])).
% 5.13/1.05  fof(f43,plain,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 5.13/1.05    inference(ennf_transformation,[],[f12])).
% 5.13/1.05  fof(f12,axiom,(
% 5.13/1.05    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 5.13/1.05  fof(f169,plain,(
% 5.13/1.05    ( ! [X2,X3] : (~r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),X2) | k3_tarski(k1_enumset1(X2,X2,X3)) = X2) )),
% 5.13/1.05    inference(resolution,[],[f99,f116])).
% 5.13/1.05  fof(f99,plain,(
% 5.13/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f60])).
% 5.13/1.05  fof(f119,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(definition_unfolding,[],[f108,f114])).
% 5.13/1.05  fof(f108,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f41])).
% 5.13/1.05  fof(f41,plain,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 5.13/1.05    inference(ennf_transformation,[],[f6])).
% 5.13/1.05  fof(f6,axiom,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 5.13/1.05  fof(f2364,plain,(
% 5.13/1.05    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl12_47),
% 5.13/1.05    inference(avatar_component_clause,[],[f2362])).
% 5.13/1.05  fof(f2362,plain,(
% 5.13/1.05    spl12_47 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).
% 5.13/1.05  fof(f2365,plain,(
% 5.13/1.05    spl12_47 | ~spl12_23),
% 5.13/1.05    inference(avatar_split_clause,[],[f2340,f2035,f2362])).
% 5.13/1.05  fof(f2035,plain,(
% 5.13/1.05    spl12_23 <=> k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 5.13/1.05  fof(f2340,plain,(
% 5.13/1.05    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl12_23),
% 5.13/1.05    inference(trivial_inequality_removal,[],[f2332])).
% 5.13/1.05  fof(f2332,plain,(
% 5.13/1.05    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl12_23),
% 5.13/1.05    inference(superposition,[],[f118,f2037])).
% 5.13/1.05  fof(f2037,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl12_23),
% 5.13/1.05    inference(avatar_component_clause,[],[f2035])).
% 5.13/1.05  fof(f118,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 5.13/1.05    inference(definition_unfolding,[],[f104,f90])).
% 5.13/1.05  fof(f90,plain,(
% 5.13/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f17])).
% 5.13/1.05  fof(f17,axiom,(
% 5.13/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 5.13/1.05  fof(f104,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f67])).
% 5.13/1.05  fof(f67,plain,(
% 5.13/1.05    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 5.13/1.05    inference(nnf_transformation,[],[f5])).
% 5.13/1.05  fof(f5,axiom,(
% 5.13/1.05    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.13/1.05  fof(f2281,plain,(
% 5.13/1.05    ~spl12_40 | spl12_1 | ~spl12_4 | ~spl12_37),
% 5.13/1.05    inference(avatar_split_clause,[],[f2276,f2238,f145,f130,f2278])).
% 5.13/1.05  fof(f130,plain,(
% 5.13/1.05    spl12_1 <=> r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 5.13/1.05  fof(f145,plain,(
% 5.13/1.05    spl12_4 <=> v1_relat_1(sK0)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 5.13/1.05  fof(f2238,plain,(
% 5.13/1.05    spl12_37 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).
% 5.13/1.05  fof(f2276,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | (spl12_1 | ~spl12_4 | ~spl12_37)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2275,f147])).
% 5.13/1.05  fof(f147,plain,(
% 5.13/1.05    v1_relat_1(sK0) | ~spl12_4),
% 5.13/1.05    inference(avatar_component_clause,[],[f145])).
% 5.13/1.05  fof(f2275,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK0) | (spl12_1 | ~spl12_37)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2272,f132])).
% 5.13/1.05  fof(f132,plain,(
% 5.13/1.05    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | spl12_1),
% 5.13/1.05    inference(avatar_component_clause,[],[f130])).
% 5.13/1.05  fof(f2272,plain,(
% 5.13/1.05    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK0) | ~spl12_37),
% 5.13/1.05    inference(resolution,[],[f2240,f242])).
% 5.13/1.05  fof(f242,plain,(
% 5.13/1.05    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | r1_tarski(k3_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(superposition,[],[f121,f115])).
% 5.13/1.05  fof(f2240,plain,(
% 5.13/1.05    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~spl12_37),
% 5.13/1.05    inference(avatar_component_clause,[],[f2238])).
% 5.13/1.05  fof(f2241,plain,(
% 5.13/1.05    spl12_37 | ~spl12_3 | ~spl12_32),
% 5.13/1.05    inference(avatar_split_clause,[],[f2236,f2183,f140,f2238])).
% 5.13/1.05  fof(f2183,plain,(
% 5.13/1.05    spl12_32 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).
% 5.13/1.05  fof(f2236,plain,(
% 5.13/1.05    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | (~spl12_3 | ~spl12_32)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2223,f142])).
% 5.13/1.05  fof(f2223,plain,(
% 5.13/1.05    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl12_32),
% 5.13/1.05    inference(resolution,[],[f2185,f231])).
% 5.13/1.05  fof(f231,plain,(
% 5.13/1.05    ( ! [X2,X3] : (~r1_tarski(X3,k2_relat_1(X2)) | r1_tarski(X3,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 5.13/1.05    inference(superposition,[],[f119,f115])).
% 5.13/1.05  fof(f2185,plain,(
% 5.13/1.05    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_32),
% 5.13/1.05    inference(avatar_component_clause,[],[f2183])).
% 5.13/1.05  fof(f2186,plain,(
% 5.13/1.05    spl12_32 | ~spl12_22),
% 5.13/1.05    inference(avatar_split_clause,[],[f2161,f2025,f2183])).
% 5.13/1.05  fof(f2025,plain,(
% 5.13/1.05    spl12_22 <=> k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 5.13/1.05  fof(f2161,plain,(
% 5.13/1.05    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_22),
% 5.13/1.05    inference(trivial_inequality_removal,[],[f2153])).
% 5.13/1.05  fof(f2153,plain,(
% 5.13/1.05    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_22),
% 5.13/1.05    inference(superposition,[],[f118,f2027])).
% 5.13/1.05  fof(f2027,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | ~spl12_22),
% 5.13/1.05    inference(avatar_component_clause,[],[f2025])).
% 5.13/1.05  fof(f2038,plain,(
% 5.13/1.05    spl12_23 | ~spl12_3 | ~spl12_4 | ~spl12_9 | ~spl12_19),
% 5.13/1.05    inference(avatar_split_clause,[],[f2033,f1976,f341,f145,f140,f2035])).
% 5.13/1.05  fof(f341,plain,(
% 5.13/1.05    spl12_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 5.13/1.05  fof(f1976,plain,(
% 5.13/1.05    spl12_19 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 5.13/1.05  fof(f2033,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_9 | ~spl12_19)),
% 5.13/1.05    inference(forward_demodulation,[],[f2032,f343])).
% 5.13/1.05  fof(f343,plain,(
% 5.13/1.05    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl12_9),
% 5.13/1.05    inference(avatar_component_clause,[],[f341])).
% 5.13/1.05  fof(f2032,plain,(
% 5.13/1.05    k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_9 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2031,f78])).
% 5.13/1.05  fof(f78,plain,(
% 5.13/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f8])).
% 5.13/1.05  fof(f8,axiom,(
% 5.13/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.13/1.05  fof(f2031,plain,(
% 5.13/1.05    ~r1_tarski(k1_xboole_0,k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))) | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_9 | ~spl12_19)),
% 5.13/1.05    inference(forward_demodulation,[],[f2030,f343])).
% 5.13/1.05  fof(f2030,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))) | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2029,f142])).
% 5.13/1.05  fof(f2029,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))) | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl12_4 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f1998,f147])).
% 5.13/1.05  fof(f1998,plain,(
% 5.13/1.05    ~r1_tarski(k1_relat_1(k1_xboole_0),k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))) | ~v1_relat_1(sK0) | k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl12_19),
% 5.13/1.05    inference(superposition,[],[f260,f1978])).
% 5.13/1.05  fof(f1978,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl12_19),
% 5.13/1.05    inference(avatar_component_clause,[],[f1976])).
% 5.13/1.05  fof(f260,plain,(
% 5.13/1.05    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k1_relat_1(X1),k1_relat_1(X0))) | ~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(resolution,[],[f82,f99])).
% 5.13/1.05  fof(f82,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f33])).
% 5.13/1.05  fof(f33,plain,(
% 5.13/1.05    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.13/1.05    inference(ennf_transformation,[],[f21])).
% 5.13/1.05  fof(f21,axiom,(
% 5.13/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).
% 5.13/1.05  fof(f2028,plain,(
% 5.13/1.05    spl12_22 | ~spl12_3 | ~spl12_4 | ~spl12_11 | ~spl12_19),
% 5.13/1.05    inference(avatar_split_clause,[],[f2023,f1976,f404,f145,f140,f2025])).
% 5.13/1.05  fof(f404,plain,(
% 5.13/1.05    spl12_11 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 5.13/1.05  fof(f2023,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_11 | ~spl12_19)),
% 5.13/1.05    inference(forward_demodulation,[],[f2022,f406])).
% 5.13/1.05  fof(f406,plain,(
% 5.13/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl12_11),
% 5.13/1.05    inference(avatar_component_clause,[],[f404])).
% 5.13/1.05  fof(f2022,plain,(
% 5.13/1.05    k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_11 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2021,f78])).
% 5.13/1.05  fof(f2021,plain,(
% 5.13/1.05    ~r1_tarski(k1_xboole_0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_11 | ~spl12_19)),
% 5.13/1.05    inference(forward_demodulation,[],[f2020,f406])).
% 5.13/1.05  fof(f2020,plain,(
% 5.13/1.05    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | (~spl12_3 | ~spl12_4 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f2019,f142])).
% 5.13/1.05  fof(f2019,plain,(
% 5.13/1.05    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl12_4 | ~spl12_19)),
% 5.13/1.05    inference(subsumption_resolution,[],[f1997,f147])).
% 5.13/1.05  fof(f1997,plain,(
% 5.13/1.05    ~r1_tarski(k2_relat_1(k1_xboole_0),k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) | ~v1_relat_1(sK0) | k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl12_19),
% 5.13/1.05    inference(superposition,[],[f247,f1978])).
% 5.13/1.05  fof(f247,plain,(
% 5.13/1.05    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_subset_1(X1,X0)),k6_subset_1(k2_relat_1(X1),k2_relat_1(X0))) | ~v1_relat_1(X1) | k2_relat_1(k6_subset_1(X1,X0)) = k6_subset_1(k2_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(resolution,[],[f81,f99])).
% 5.13/1.05  fof(f81,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f32])).
% 5.13/1.05  fof(f32,plain,(
% 5.13/1.05    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.13/1.05    inference(ennf_transformation,[],[f23])).
% 5.13/1.05  fof(f23,axiom,(
% 5.13/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 5.13/1.05  fof(f1979,plain,(
% 5.13/1.05    spl12_19 | ~spl12_2),
% 5.13/1.05    inference(avatar_split_clause,[],[f1954,f135,f1976])).
% 5.13/1.05  fof(f135,plain,(
% 5.13/1.05    spl12_2 <=> r1_tarski(sK0,sK1)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 5.13/1.05  fof(f1954,plain,(
% 5.13/1.05    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~spl12_2),
% 5.13/1.05    inference(resolution,[],[f1930,f167])).
% 5.13/1.05  fof(f167,plain,(
% 5.13/1.05    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 5.13/1.05    inference(resolution,[],[f99,f78])).
% 5.13/1.05  fof(f1930,plain,(
% 5.13/1.05    ( ! [X1] : (r1_tarski(k6_subset_1(sK0,sK1),X1)) ) | ~spl12_2),
% 5.13/1.05    inference(resolution,[],[f1911,f120])).
% 5.13/1.05  fof(f120,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 5.13/1.05    inference(definition_unfolding,[],[f109,f90,f114])).
% 5.13/1.05  fof(f109,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 5.13/1.05    inference(cnf_transformation,[],[f42])).
% 5.13/1.05  fof(f42,plain,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 5.13/1.05    inference(ennf_transformation,[],[f9])).
% 5.13/1.05  fof(f9,axiom,(
% 5.13/1.05    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 5.13/1.05  fof(f1911,plain,(
% 5.13/1.05    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,X0)))) ) | ~spl12_2),
% 5.13/1.05    inference(resolution,[],[f1906,f116])).
% 5.13/1.05  fof(f1906,plain,(
% 5.13/1.05    ( ! [X120] : (~r1_tarski(sK1,X120) | r1_tarski(sK0,X120)) ) | ~spl12_2),
% 5.13/1.05    inference(resolution,[],[f1854,f137])).
% 5.13/1.05  fof(f137,plain,(
% 5.13/1.05    r1_tarski(sK0,sK1) | ~spl12_2),
% 5.13/1.05    inference(avatar_component_clause,[],[f135])).
% 5.13/1.05  fof(f432,plain,(
% 5.13/1.05    spl12_11 | ~spl12_6),
% 5.13/1.05    inference(avatar_split_clause,[],[f429,f156,f404])).
% 5.13/1.05  fof(f156,plain,(
% 5.13/1.05    spl12_6 <=> v1_relat_1(k1_xboole_0)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 5.13/1.05  fof(f429,plain,(
% 5.13/1.05    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl12_6),
% 5.13/1.05    inference(resolution,[],[f401,f191])).
% 5.13/1.05  fof(f191,plain,(
% 5.13/1.05    ( ! [X1] : (~r1_xboole_0(sK3(sK2(X1)),X1) | k1_xboole_0 = X1) )),
% 5.13/1.05    inference(resolution,[],[f162,f84])).
% 5.13/1.05  fof(f84,plain,(
% 5.13/1.05    ( ! [X0] : (r2_hidden(X0,sK3(X0))) )),
% 5.13/1.05    inference(cnf_transformation,[],[f54])).
% 5.13/1.05  fof(f54,plain,(
% 5.13/1.05    ! [X0] : (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : ((! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X6,X7] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0)))),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f53,f52])).
% 5.13/1.05  fof(f52,plain,(
% 5.13/1.05    ! [X0] : (? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1)) => (! [X2] : (r2_hidden(X2,sK3(X0)) | r2_tarski(X2,sK3(X0)) | ~r1_tarski(X2,sK3(X0))) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) | ~r2_hidden(X3,sK3(X0))) & ! [X7,X6] : (r2_hidden(X7,sK3(X0)) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,sK3(X0))) & r2_hidden(X0,sK3(X0))))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f53,plain,(
% 5.13/1.05    ! [X3,X0] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,sK3(X0))) => (! [X5] : (r2_hidden(X5,sK4(X0,X3)) | ~r1_tarski(X5,X3)) & r2_hidden(sK4(X0,X3),sK3(X0))))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f36,plain,(
% 5.13/1.05    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | ~r1_tarski(X7,X6) | ~r2_hidden(X6,X1)) & r2_hidden(X0,X1))),
% 5.13/1.05    inference(flattening,[],[f35])).
% 5.13/1.05  fof(f35,plain,(
% 5.13/1.05    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (? [X4] : (! [X5] : (r2_hidden(X5,X4) | ~r1_tarski(X5,X3)) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X1)) & ! [X6,X7] : (r2_hidden(X7,X1) | (~r1_tarski(X7,X6) | ~r2_hidden(X6,X1))) & r2_hidden(X0,X1))),
% 5.13/1.05    inference(ennf_transformation,[],[f26])).
% 5.13/1.05  fof(f26,plain,(
% 5.13/1.05    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : ~(! [X4] : ~(! [X5] : (r1_tarski(X5,X3) => r2_hidden(X5,X4)) & r2_hidden(X4,X1)) & r2_hidden(X3,X1)) & ! [X6,X7] : ((r1_tarski(X7,X6) & r2_hidden(X6,X1)) => r2_hidden(X7,X1)) & r2_hidden(X0,X1))),
% 5.13/1.05    inference(rectify,[],[f16])).
% 5.13/1.05  fof(f16,axiom,(
% 5.13/1.05    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : ~(! [X3] : ~(! [X4] : (r1_tarski(X4,X2) => r2_hidden(X4,X3)) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tarski)).
% 5.13/1.05  fof(f162,plain,(
% 5.13/1.05    ( ! [X2,X3] : (~r2_hidden(sK2(X3),X2) | ~r1_xboole_0(X2,X3) | k1_xboole_0 = X3) )),
% 5.13/1.05    inference(resolution,[],[f95,f83])).
% 5.13/1.05  fof(f83,plain,(
% 5.13/1.05    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 5.13/1.05    inference(cnf_transformation,[],[f51])).
% 5.13/1.05  fof(f51,plain,(
% 5.13/1.05    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f50])).
% 5.13/1.05  fof(f50,plain,(
% 5.13/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f34,plain,(
% 5.13/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 5.13/1.05    inference(ennf_transformation,[],[f3])).
% 5.13/1.05  fof(f3,axiom,(
% 5.13/1.05    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 5.13/1.05  fof(f95,plain,(
% 5.13/1.05    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f56])).
% 5.13/1.05  fof(f56,plain,(
% 5.13/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f55])).
% 5.13/1.05  fof(f55,plain,(
% 5.13/1.05    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f37,plain,(
% 5.13/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 5.13/1.05    inference(ennf_transformation,[],[f27])).
% 5.13/1.05  fof(f27,plain,(
% 5.13/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.13/1.05    inference(rectify,[],[f2])).
% 5.13/1.05  fof(f2,axiom,(
% 5.13/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 5.13/1.05  fof(f401,plain,(
% 5.13/1.05    ( ! [X3] : (r1_xboole_0(X3,k2_relat_1(k1_xboole_0))) ) | ~spl12_6),
% 5.13/1.05    inference(resolution,[],[f345,f94])).
% 5.13/1.05  fof(f94,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f56])).
% 5.13/1.05  fof(f345,plain,(
% 5.13/1.05    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(k1_xboole_0))) ) | ~spl12_6),
% 5.13/1.05    inference(subsumption_resolution,[],[f338,f158])).
% 5.13/1.05  fof(f158,plain,(
% 5.13/1.05    v1_relat_1(k1_xboole_0) | ~spl12_6),
% 5.13/1.05    inference(avatar_component_clause,[],[f156])).
% 5.13/1.05  fof(f338,plain,(
% 5.13/1.05    ( ! [X4] : (~r2_hidden(X4,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) )),
% 5.13/1.05    inference(resolution,[],[f316,f96])).
% 5.13/1.05  fof(f96,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f58])).
% 5.13/1.05  fof(f58,plain,(
% 5.13/1.05    ! [X0,X1] : (r2_hidden(sK6(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f57])).
% 5.13/1.05  fof(f57,plain,(
% 5.13/1.05    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK6(X1),k1_relat_1(X1)))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f39,plain,(
% 5.13/1.05    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.13/1.05    inference(flattening,[],[f38])).
% 5.13/1.05  fof(f38,plain,(
% 5.13/1.05    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.13/1.05    inference(ennf_transformation,[],[f22])).
% 5.13/1.05  fof(f22,axiom,(
% 5.13/1.05    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 5.13/1.05  fof(f316,plain,(
% 5.13/1.05    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 5.13/1.05    inference(resolution,[],[f304,f128])).
% 5.13/1.05  fof(f128,plain,(
% 5.13/1.05    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 5.13/1.05    inference(equality_resolution,[],[f100])).
% 5.13/1.05  fof(f100,plain,(
% 5.13/1.05    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 5.13/1.05    inference(cnf_transformation,[],[f66])).
% 5.13/1.05  fof(f66,plain,(
% 5.13/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).
% 5.13/1.05  fof(f63,plain,(
% 5.13/1.05    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f64,plain,(
% 5.13/1.05    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f65,plain,(
% 5.13/1.05    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f62,plain,(
% 5.13/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 5.13/1.05    inference(rectify,[],[f61])).
% 5.13/1.05  fof(f61,plain,(
% 5.13/1.05    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 5.13/1.05    inference(nnf_transformation,[],[f19])).
% 5.13/1.05  fof(f19,axiom,(
% 5.13/1.05    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 5.13/1.05  fof(f304,plain,(
% 5.13/1.05    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 5.13/1.05    inference(resolution,[],[f215,f77])).
% 5.13/1.05  fof(f77,plain,(
% 5.13/1.05    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f10])).
% 5.13/1.05  fof(f10,axiom,(
% 5.13/1.05    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 5.13/1.05  fof(f215,plain,(
% 5.13/1.05    ( ! [X4,X3] : (~r1_xboole_0(sK3(sK10(X3)),X3) | ~r2_hidden(X4,X3)) )),
% 5.13/1.05    inference(resolution,[],[f165,f84])).
% 5.13/1.05  fof(f165,plain,(
% 5.13/1.05    ( ! [X12,X10,X11] : (~r2_hidden(sK10(X11),X10) | ~r1_xboole_0(X10,X11) | ~r2_hidden(X12,X11)) )),
% 5.13/1.05    inference(resolution,[],[f95,f106])).
% 5.13/1.05  fof(f106,plain,(
% 5.13/1.05    ( ! [X0,X1] : (r2_hidden(sK10(X1),X1) | ~r2_hidden(X0,X1)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f69])).
% 5.13/1.05  fof(f69,plain,(
% 5.13/1.05    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK10(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK10(X1),X1)) | ~r2_hidden(X0,X1))),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f40,f68])).
% 5.13/1.05  fof(f68,plain,(
% 5.13/1.05    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK10(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK10(X1),X1)))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f40,plain,(
% 5.13/1.05    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 5.13/1.05    inference(ennf_transformation,[],[f15])).
% 5.13/1.05  fof(f15,axiom,(
% 5.13/1.05    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 5.13/1.05  fof(f369,plain,(
% 5.13/1.05    spl12_9),
% 5.13/1.05    inference(avatar_split_clause,[],[f366,f341])).
% 5.13/1.05  fof(f366,plain,(
% 5.13/1.05    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.13/1.05    inference(resolution,[],[f337,f191])).
% 5.13/1.05  fof(f337,plain,(
% 5.13/1.05    ( ! [X3] : (r1_xboole_0(X3,k1_relat_1(k1_xboole_0))) )),
% 5.13/1.05    inference(resolution,[],[f316,f94])).
% 5.13/1.05  fof(f159,plain,(
% 5.13/1.05    spl12_6 | ~spl12_5),
% 5.13/1.05    inference(avatar_split_clause,[],[f154,f150,f156])).
% 5.13/1.05  fof(f150,plain,(
% 5.13/1.05    spl12_5 <=> v1_xboole_0(k1_xboole_0)),
% 5.13/1.05    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 5.13/1.05  fof(f154,plain,(
% 5.13/1.05    v1_relat_1(k1_xboole_0) | ~spl12_5),
% 5.13/1.05    inference(resolution,[],[f79,f152])).
% 5.13/1.05  fof(f152,plain,(
% 5.13/1.05    v1_xboole_0(k1_xboole_0) | ~spl12_5),
% 5.13/1.05    inference(avatar_component_clause,[],[f150])).
% 5.13/1.05  fof(f79,plain,(
% 5.13/1.05    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 5.13/1.05    inference(cnf_transformation,[],[f30])).
% 5.13/1.05  fof(f30,plain,(
% 5.13/1.05    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 5.13/1.05    inference(ennf_transformation,[],[f18])).
% 5.13/1.05  fof(f18,axiom,(
% 5.13/1.05    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 5.13/1.05  fof(f153,plain,(
% 5.13/1.05    spl12_5),
% 5.13/1.05    inference(avatar_split_clause,[],[f76,f150])).
% 5.13/1.05  fof(f76,plain,(
% 5.13/1.05    v1_xboole_0(k1_xboole_0)),
% 5.13/1.05    inference(cnf_transformation,[],[f1])).
% 5.13/1.05  fof(f1,axiom,(
% 5.13/1.05    v1_xboole_0(k1_xboole_0)),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 5.13/1.05  fof(f148,plain,(
% 5.13/1.05    spl12_4),
% 5.13/1.05    inference(avatar_split_clause,[],[f72,f145])).
% 5.13/1.05  fof(f72,plain,(
% 5.13/1.05    v1_relat_1(sK0)),
% 5.13/1.05    inference(cnf_transformation,[],[f49])).
% 5.13/1.05  fof(f49,plain,(
% 5.13/1.05    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 5.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f48,f47])).
% 5.13/1.05  fof(f47,plain,(
% 5.13/1.05    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f48,plain,(
% 5.13/1.05    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 5.13/1.05    introduced(choice_axiom,[])).
% 5.13/1.05  fof(f29,plain,(
% 5.13/1.05    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 5.13/1.05    inference(flattening,[],[f28])).
% 5.13/1.05  fof(f28,plain,(
% 5.13/1.05    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 5.13/1.05    inference(ennf_transformation,[],[f25])).
% 5.13/1.05  fof(f25,negated_conjecture,(
% 5.13/1.05    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 5.13/1.05    inference(negated_conjecture,[],[f24])).
% 5.13/1.05  fof(f24,conjecture,(
% 5.13/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 5.13/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 5.13/1.05  fof(f143,plain,(
% 5.13/1.05    spl12_3),
% 5.13/1.05    inference(avatar_split_clause,[],[f73,f140])).
% 5.13/1.05  fof(f73,plain,(
% 5.13/1.05    v1_relat_1(sK1)),
% 5.13/1.05    inference(cnf_transformation,[],[f49])).
% 5.13/1.05  fof(f138,plain,(
% 5.13/1.05    spl12_2),
% 5.13/1.05    inference(avatar_split_clause,[],[f74,f135])).
% 5.13/1.05  fof(f74,plain,(
% 5.13/1.05    r1_tarski(sK0,sK1)),
% 5.13/1.05    inference(cnf_transformation,[],[f49])).
% 5.13/1.05  fof(f133,plain,(
% 5.13/1.05    ~spl12_1),
% 5.13/1.05    inference(avatar_split_clause,[],[f75,f130])).
% 5.13/1.05  fof(f75,plain,(
% 5.13/1.05    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 5.13/1.05    inference(cnf_transformation,[],[f49])).
% 5.13/1.05  % SZS output end Proof for theBenchmark
% 5.13/1.05  % (10572)------------------------------
% 5.13/1.05  % (10572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.05  % (10572)Termination reason: Refutation
% 5.13/1.05  
% 5.13/1.05  % (10572)Memory used [KB]: 13688
% 5.13/1.05  % (10572)Time elapsed: 0.345 s
% 5.13/1.05  % (10572)------------------------------
% 5.13/1.05  % (10572)------------------------------
% 5.13/1.06  % (10503)Success in time 0.682 s
%------------------------------------------------------------------------------

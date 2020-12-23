%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:12 EST 2020

% Result     : Theorem 4.33s
% Output     : Refutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 644 expanded)
%              Number of leaves         :   44 ( 232 expanded)
%              Depth                    :   18
%              Number of atoms          :  466 (1290 expanded)
%              Number of equality atoms :  194 ( 786 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f182,f187,f192,f762,f772,f1537,f1546,f2057,f2108,f2115,f2119,f2172,f2223,f2224,f2227,f2421,f2455])).

fof(f2455,plain,
    ( ~ spl9_13
    | spl9_18
    | ~ spl9_86 ),
    inference(avatar_contradiction_clause,[],[f2454])).

fof(f2454,plain,
    ( $false
    | ~ spl9_13
    | spl9_18
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f2453,f2069])).

fof(f2069,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f2068])).

fof(f2068,plain,
    ( spl9_86
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f2453,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl9_13
    | spl9_18 ),
    inference(subsumption_resolution,[],[f2451,f748])).

fof(f748,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl9_18
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f2451,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl9_13 ),
    inference(trivial_inequality_removal,[],[f2444])).

fof(f2444,plain,
    ( sK0 != sK0
    | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl9_13 ),
    inference(superposition,[],[f140,f663])).

fof(f663,plain,
    ( sK0 = sK7(sK0,sK2)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f661])).

fof(f661,plain,
    ( spl9_13
  <=> sK0 = sK7(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sK7(X0,X1) != X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f95,f129])).

fof(f129,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f125])).

fof(f125,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f79,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f103,f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f112,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f113,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f114,f115])).

fof(f115,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f103,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f79,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) != X0
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f2421,plain,
    ( spl9_13
    | ~ spl9_46
    | ~ spl9_87 ),
    inference(avatar_split_clause,[],[f2417,f2105,f1543,f661])).

fof(f1543,plain,
    ( spl9_46
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2105,plain,
    ( spl9_87
  <=> r2_hidden(sK7(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f2417,plain,
    ( sK0 = sK7(sK0,sK2)
    | ~ spl9_46
    | ~ spl9_87 ),
    inference(resolution,[],[f2107,f1621])).

fof(f1621,plain,
    ( ! [X34] :
        ( ~ r2_hidden(X34,sK1)
        | sK0 = X34 )
    | ~ spl9_46 ),
    inference(superposition,[],[f166,f1545])).

fof(f1545,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f1543])).

fof(f166,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f92,f129])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2107,plain,
    ( r2_hidden(sK7(sK0,sK2),sK1)
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f2105])).

fof(f2227,plain,
    ( spl9_86
    | ~ spl9_16
    | ~ spl9_85 ),
    inference(avatar_split_clause,[],[f2226,f2054,f731,f2068])).

fof(f731,plain,
    ( spl9_16
  <=> r2_hidden(sK3(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f2054,plain,
    ( spl9_85
  <=> sK0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f2226,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl9_16
    | ~ spl9_85 ),
    inference(forward_demodulation,[],[f733,f2056])).

fof(f2056,plain,
    ( sK0 = sK3(sK1)
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f2054])).

fof(f733,plain,
    ( r2_hidden(sK3(sK1),sK2)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f731])).

fof(f2224,plain,
    ( sK0 != sK3(sK2)
    | sK0 != sK3(sK1)
    | r2_hidden(sK3(sK1),sK2)
    | ~ r2_hidden(sK3(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2223,plain,
    ( spl9_90
    | ~ spl9_46
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f2218,f2110,f1543,f2220])).

fof(f2220,plain,
    ( spl9_90
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f2110,plain,
    ( spl9_88
  <=> r2_hidden(sK3(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f2218,plain,
    ( sK0 = sK3(sK2)
    | ~ spl9_46
    | ~ spl9_88 ),
    inference(resolution,[],[f2112,f1621])).

fof(f2112,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f2110])).

fof(f2172,plain,
    ( spl9_1
    | spl9_54 ),
    inference(avatar_contradiction_clause,[],[f2171])).

fof(f2171,plain,
    ( $false
    | spl9_1
    | spl9_54 ),
    inference(subsumption_resolution,[],[f2169,f176])).

fof(f176,plain,
    ( k1_xboole_0 != sK2
    | spl9_1 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl9_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2169,plain,
    ( k1_xboole_0 = sK2
    | spl9_54 ),
    inference(resolution,[],[f1660,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f1660,plain,
    ( ~ r2_hidden(sK3(sK2),sK2)
    | spl9_54 ),
    inference(avatar_component_clause,[],[f1659])).

fof(f1659,plain,
    ( spl9_54
  <=> r2_hidden(sK3(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f2119,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2115,plain,
    ( spl9_88
    | spl9_1
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f2114,f1543,f189,f174,f2110])).

fof(f189,plain,
    ( spl9_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f2114,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f2096,f176])).

fof(f2096,plain,
    ( r2_hidden(sK3(sK2),sK1)
    | k1_xboole_0 = sK2
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(resolution,[],[f1663,f73])).

fof(f1663,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f1602,f220])).

fof(f220,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f216,f76])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f216,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f202,f193])).

fof(f193,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f76,f71])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f202,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f104,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f104,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1602,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))
        | r2_hidden(X1,sK1) )
    | ~ spl9_4
    | ~ spl9_46 ),
    inference(superposition,[],[f522,f1545])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
        | r2_hidden(X0,sK1) )
    | ~ spl9_4 ),
    inference(superposition,[],[f366,f191])).

fof(f191,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f189])).

fof(f366,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))
      | r2_hidden(X4,X0) ) ),
    inference(forward_demodulation,[],[f172,f104])).

fof(f172,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f105,f127])).

fof(f127,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f83,f126])).

fof(f126,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f125])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2108,plain,
    ( spl9_87
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f2093,f1543,f657,f189,f2105])).

fof(f657,plain,
    ( spl9_12
  <=> r2_hidden(sK7(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2093,plain,
    ( r2_hidden(sK7(sK0,sK2),sK1)
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_46 ),
    inference(resolution,[],[f1663,f659])).

fof(f659,plain,
    ( r2_hidden(sK7(sK0,sK2),sK2)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f657])).

fof(f2057,plain,
    ( spl9_85
    | spl9_2
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f2052,f1543,f179,f2054])).

fof(f179,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2052,plain,
    ( sK0 = sK3(sK1)
    | spl9_2
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f2040,f181])).

fof(f181,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f2040,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1
    | ~ spl9_46 ),
    inference(resolution,[],[f1621,f73])).

fof(f1546,plain,
    ( spl9_46
    | spl9_2
    | ~ spl9_45 ),
    inference(avatar_split_clause,[],[f1541,f1534,f179,f1543])).

fof(f1534,plain,
    ( spl9_45
  <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f1541,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl9_2
    | ~ spl9_45 ),
    inference(subsumption_resolution,[],[f1538,f181])).

fof(f1538,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl9_45 ),
    inference(resolution,[],[f1536,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f96,f129,f129])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1536,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl9_45 ),
    inference(avatar_component_clause,[],[f1534])).

fof(f1537,plain,
    ( spl9_45
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f1522,f189,f1534])).

fof(f1522,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl9_4 ),
    inference(superposition,[],[f896,f191])).

fof(f896,plain,(
    ! [X10,X11] : r1_tarski(X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11))) ),
    inference(subsumption_resolution,[],[f881,f70])).

fof(f881,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 != k5_xboole_0(k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11)),k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11)))
      | r1_tarski(X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11))) ) ),
    inference(superposition,[],[f605,f137])).

fof(f137,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f82,f126,f126,f126])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f605,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f604,f216])).

fof(f604,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f148,f104])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f99,f128])).

fof(f128,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f80,f127])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f772,plain,
    ( spl9_12
    | spl9_11
    | spl9_13 ),
    inference(avatar_split_clause,[],[f767,f661,f588,f657])).

fof(f588,plain,
    ( spl9_11
  <=> k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f767,plain,
    ( r2_hidden(sK7(sK0,sK2),sK2)
    | spl9_11
    | spl9_13 ),
    inference(subsumption_resolution,[],[f763,f662])).

fof(f662,plain,
    ( sK0 != sK7(sK0,sK2)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f661])).

fof(f763,plain,
    ( sK0 = sK7(sK0,sK2)
    | r2_hidden(sK7(sK0,sK2),sK2)
    | spl9_11 ),
    inference(trivial_inequality_removal,[],[f645])).

fof(f645,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK7(sK0,sK2)
    | r2_hidden(sK7(sK0,sK2),sK2)
    | spl9_11 ),
    inference(superposition,[],[f619,f70])).

fof(f619,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k5_xboole_0(sK2,X0)
        | sK0 = sK7(sK0,X0)
        | r2_hidden(sK7(sK0,X0),X0) )
    | spl9_11 ),
    inference(superposition,[],[f589,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f94,f129])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK7(X0,X1) = X0
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f589,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl9_11 ),
    inference(avatar_component_clause,[],[f588])).

fof(f762,plain,
    ( spl9_18
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f761,f588,f747])).

fof(f761,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f728,f193])).

fof(f728,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl9_11 ),
    inference(superposition,[],[f237,f590])).

fof(f590,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f588])).

fof(f237,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f220,f220])).

fof(f192,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f132,f189])).

fof(f132,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f66,f129,f126])).

fof(f66,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f35,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f187,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f67,f184])).

fof(f184,plain,
    ( spl9_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f67,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f182,plain,(
    ~ spl9_2 ),
    inference(avatar_split_clause,[],[f68,f179])).

fof(f68,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f177,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f69,f174])).

fof(f69,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:43:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (11284)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (11300)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (11281)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (11290)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (11292)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (11283)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (11287)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (11291)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (11292)Refutation not found, incomplete strategy% (11292)------------------------------
% 0.22/0.52  % (11292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11292)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11292)Memory used [KB]: 10618
% 0.22/0.53  % (11292)Time elapsed: 0.107 s
% 0.22/0.53  % (11292)------------------------------
% 0.22/0.53  % (11292)------------------------------
% 0.22/0.54  % (11301)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (11295)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (11280)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (11293)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (11285)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (11304)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (11282)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (11305)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (11309)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (11303)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (11306)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (11294)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (11299)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (11310)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (11296)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (11307)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (11310)Refutation not found, incomplete strategy% (11310)------------------------------
% 0.22/0.55  % (11310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11310)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11310)Memory used [KB]: 1663
% 0.22/0.55  % (11310)Time elapsed: 0.002 s
% 0.22/0.55  % (11310)------------------------------
% 0.22/0.55  % (11310)------------------------------
% 0.22/0.55  % (11302)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (11296)Refutation not found, incomplete strategy% (11296)------------------------------
% 0.22/0.55  % (11296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11296)Memory used [KB]: 10746
% 0.22/0.55  % (11296)Time elapsed: 0.139 s
% 0.22/0.55  % (11296)------------------------------
% 0.22/0.55  % (11296)------------------------------
% 0.22/0.56  % (11288)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (11298)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (11297)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.58  % (11289)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.58  % (11286)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.17/0.66  % (11332)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.17/0.68  % (11333)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.68  % (11333)Refutation not found, incomplete strategy% (11333)------------------------------
% 2.17/0.68  % (11333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (11333)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (11333)Memory used [KB]: 6140
% 2.17/0.68  % (11333)Time elapsed: 0.095 s
% 2.17/0.68  % (11333)------------------------------
% 2.17/0.68  % (11333)------------------------------
% 2.17/0.68  % (11295)Refutation not found, incomplete strategy% (11295)------------------------------
% 2.17/0.68  % (11295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (11295)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (11295)Memory used [KB]: 6140
% 2.17/0.68  % (11295)Time elapsed: 0.275 s
% 2.17/0.68  % (11295)------------------------------
% 2.17/0.68  % (11295)------------------------------
% 2.17/0.68  % (11280)Refutation not found, incomplete strategy% (11280)------------------------------
% 2.17/0.68  % (11280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (11280)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (11280)Memory used [KB]: 1663
% 2.17/0.68  % (11280)Time elapsed: 0.267 s
% 2.17/0.68  % (11280)------------------------------
% 2.17/0.68  % (11280)------------------------------
% 2.17/0.69  % (11283)Refutation not found, incomplete strategy% (11283)------------------------------
% 2.17/0.69  % (11283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (11283)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (11283)Memory used [KB]: 6140
% 2.17/0.69  % (11283)Time elapsed: 0.248 s
% 2.17/0.69  % (11283)------------------------------
% 2.17/0.69  % (11283)------------------------------
% 2.17/0.73  % (11331)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.87/0.78  % (11335)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.19/0.81  % (11282)Time limit reached!
% 3.19/0.81  % (11282)------------------------------
% 3.19/0.81  % (11282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (11336)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.19/0.83  % (11282)Termination reason: Time limit
% 3.19/0.83  % (11282)Termination phase: Saturation
% 3.19/0.83  
% 3.19/0.83  % (11282)Memory used [KB]: 7291
% 3.19/0.83  % (11282)Time elapsed: 0.400 s
% 3.19/0.83  % (11282)------------------------------
% 3.19/0.83  % (11282)------------------------------
% 3.19/0.84  % (11337)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.19/0.84  % (11304)Time limit reached!
% 3.19/0.84  % (11304)------------------------------
% 3.19/0.84  % (11304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.85  % (11334)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.62/0.85  % (11304)Termination reason: Time limit
% 3.62/0.85  
% 3.62/0.85  % (11304)Memory used [KB]: 13432
% 3.62/0.85  % (11304)Time elapsed: 0.430 s
% 3.62/0.85  % (11304)------------------------------
% 3.62/0.85  % (11304)------------------------------
% 4.33/0.96  % (11338)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.33/0.96  % (11332)Refutation found. Thanks to Tanya!
% 4.33/0.96  % SZS status Theorem for theBenchmark
% 4.33/0.96  % SZS output start Proof for theBenchmark
% 4.33/0.96  fof(f2456,plain,(
% 4.33/0.96    $false),
% 4.33/0.96    inference(avatar_sat_refutation,[],[f177,f182,f187,f192,f762,f772,f1537,f1546,f2057,f2108,f2115,f2119,f2172,f2223,f2224,f2227,f2421,f2455])).
% 4.33/0.96  fof(f2455,plain,(
% 4.33/0.96    ~spl9_13 | spl9_18 | ~spl9_86),
% 4.33/0.96    inference(avatar_contradiction_clause,[],[f2454])).
% 4.33/0.96  fof(f2454,plain,(
% 4.33/0.96    $false | (~spl9_13 | spl9_18 | ~spl9_86)),
% 4.33/0.96    inference(subsumption_resolution,[],[f2453,f2069])).
% 4.33/0.96  fof(f2069,plain,(
% 4.33/0.96    r2_hidden(sK0,sK2) | ~spl9_86),
% 4.33/0.96    inference(avatar_component_clause,[],[f2068])).
% 4.33/0.96  fof(f2068,plain,(
% 4.33/0.96    spl9_86 <=> r2_hidden(sK0,sK2)),
% 4.33/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).
% 4.33/0.96  fof(f2453,plain,(
% 4.33/0.96    ~r2_hidden(sK0,sK2) | (~spl9_13 | spl9_18)),
% 4.33/0.96    inference(subsumption_resolution,[],[f2451,f748])).
% 4.33/0.96  fof(f748,plain,(
% 4.33/0.96    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl9_18),
% 4.33/0.96    inference(avatar_component_clause,[],[f747])).
% 4.33/0.96  fof(f747,plain,(
% 4.33/0.96    spl9_18 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 4.33/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 4.33/0.96  fof(f2451,plain,(
% 4.33/0.96    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK2) | ~spl9_13),
% 4.33/0.96    inference(trivial_inequality_removal,[],[f2444])).
% 4.33/0.96  fof(f2444,plain,(
% 4.33/0.96    sK0 != sK0 | sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK2) | ~spl9_13),
% 4.33/0.96    inference(superposition,[],[f140,f663])).
% 4.33/0.96  fof(f663,plain,(
% 4.33/0.96    sK0 = sK7(sK0,sK2) | ~spl9_13),
% 4.33/0.96    inference(avatar_component_clause,[],[f661])).
% 4.33/0.96  fof(f661,plain,(
% 4.33/0.96    spl9_13 <=> sK0 = sK7(sK0,sK2)),
% 4.33/0.96    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 4.33/0.96  fof(f140,plain,(
% 4.33/0.96    ( ! [X0,X1] : (sK7(X0,X1) != X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f95,f129])).
% 4.33/0.96  fof(f129,plain,(
% 4.33/0.96    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f72,f125])).
% 4.33/0.96  fof(f125,plain,(
% 4.33/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f79,f124])).
% 4.33/0.96  fof(f124,plain,(
% 4.33/0.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f103,f123])).
% 4.33/0.96  fof(f123,plain,(
% 4.33/0.96    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f112,f122])).
% 4.33/0.96  fof(f122,plain,(
% 4.33/0.96    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f113,f121])).
% 4.33/0.96  fof(f121,plain,(
% 4.33/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.33/0.96    inference(definition_unfolding,[],[f114,f115])).
% 4.33/0.96  fof(f115,plain,(
% 4.33/0.96    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.33/0.96    inference(cnf_transformation,[],[f29])).
% 4.33/0.96  fof(f29,axiom,(
% 4.33/0.96    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.33/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 4.33/0.97  fof(f114,plain,(
% 4.33/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f28])).
% 4.33/0.97  fof(f28,axiom,(
% 4.33/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.33/0.97  fof(f113,plain,(
% 4.33/0.97    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f27])).
% 4.33/0.97  fof(f27,axiom,(
% 4.33/0.97    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.33/0.97  fof(f112,plain,(
% 4.33/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f26])).
% 4.33/0.97  fof(f26,axiom,(
% 4.33/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.33/0.97  fof(f103,plain,(
% 4.33/0.97    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f25])).
% 4.33/0.97  fof(f25,axiom,(
% 4.33/0.97    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.33/0.97  fof(f79,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f24])).
% 4.33/0.97  fof(f24,axiom,(
% 4.33/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.33/0.97  fof(f72,plain,(
% 4.33/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f23])).
% 4.33/0.97  fof(f23,axiom,(
% 4.33/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.33/0.97  fof(f95,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f56])).
% 4.33/0.97  fof(f56,plain,(
% 4.33/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f54,f55])).
% 4.33/0.97  fof(f55,plain,(
% 4.33/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 4.33/0.97    introduced(choice_axiom,[])).
% 4.33/0.97  fof(f54,plain,(
% 4.33/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.33/0.97    inference(rectify,[],[f53])).
% 4.33/0.97  fof(f53,plain,(
% 4.33/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.33/0.97    inference(nnf_transformation,[],[f16])).
% 4.33/0.97  fof(f16,axiom,(
% 4.33/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 4.33/0.97  fof(f2421,plain,(
% 4.33/0.97    spl9_13 | ~spl9_46 | ~spl9_87),
% 4.33/0.97    inference(avatar_split_clause,[],[f2417,f2105,f1543,f661])).
% 4.33/0.97  fof(f1543,plain,(
% 4.33/0.97    spl9_46 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 4.33/0.97  fof(f2105,plain,(
% 4.33/0.97    spl9_87 <=> r2_hidden(sK7(sK0,sK2),sK1)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).
% 4.33/0.97  fof(f2417,plain,(
% 4.33/0.97    sK0 = sK7(sK0,sK2) | (~spl9_46 | ~spl9_87)),
% 4.33/0.97    inference(resolution,[],[f2107,f1621])).
% 4.33/0.97  fof(f1621,plain,(
% 4.33/0.97    ( ! [X34] : (~r2_hidden(X34,sK1) | sK0 = X34) ) | ~spl9_46),
% 4.33/0.97    inference(superposition,[],[f166,f1545])).
% 4.33/0.97  fof(f1545,plain,(
% 4.33/0.97    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl9_46),
% 4.33/0.97    inference(avatar_component_clause,[],[f1543])).
% 4.33/0.97  fof(f166,plain,(
% 4.33/0.97    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 4.33/0.97    inference(equality_resolution,[],[f143])).
% 4.33/0.97  fof(f143,plain,(
% 4.33/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 4.33/0.97    inference(definition_unfolding,[],[f92,f129])).
% 4.33/0.97  fof(f92,plain,(
% 4.33/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.33/0.97    inference(cnf_transformation,[],[f56])).
% 4.33/0.97  fof(f2107,plain,(
% 4.33/0.97    r2_hidden(sK7(sK0,sK2),sK1) | ~spl9_87),
% 4.33/0.97    inference(avatar_component_clause,[],[f2105])).
% 4.33/0.97  fof(f2227,plain,(
% 4.33/0.97    spl9_86 | ~spl9_16 | ~spl9_85),
% 4.33/0.97    inference(avatar_split_clause,[],[f2226,f2054,f731,f2068])).
% 4.33/0.97  fof(f731,plain,(
% 4.33/0.97    spl9_16 <=> r2_hidden(sK3(sK1),sK2)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 4.33/0.97  fof(f2054,plain,(
% 4.33/0.97    spl9_85 <=> sK0 = sK3(sK1)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).
% 4.33/0.97  fof(f2226,plain,(
% 4.33/0.97    r2_hidden(sK0,sK2) | (~spl9_16 | ~spl9_85)),
% 4.33/0.97    inference(forward_demodulation,[],[f733,f2056])).
% 4.33/0.97  fof(f2056,plain,(
% 4.33/0.97    sK0 = sK3(sK1) | ~spl9_85),
% 4.33/0.97    inference(avatar_component_clause,[],[f2054])).
% 4.33/0.97  fof(f733,plain,(
% 4.33/0.97    r2_hidden(sK3(sK1),sK2) | ~spl9_16),
% 4.33/0.97    inference(avatar_component_clause,[],[f731])).
% 4.33/0.97  fof(f2224,plain,(
% 4.33/0.97    sK0 != sK3(sK2) | sK0 != sK3(sK1) | r2_hidden(sK3(sK1),sK2) | ~r2_hidden(sK3(sK2),sK2)),
% 4.33/0.97    introduced(theory_tautology_sat_conflict,[])).
% 4.33/0.97  fof(f2223,plain,(
% 4.33/0.97    spl9_90 | ~spl9_46 | ~spl9_88),
% 4.33/0.97    inference(avatar_split_clause,[],[f2218,f2110,f1543,f2220])).
% 4.33/0.97  fof(f2220,plain,(
% 4.33/0.97    spl9_90 <=> sK0 = sK3(sK2)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).
% 4.33/0.97  fof(f2110,plain,(
% 4.33/0.97    spl9_88 <=> r2_hidden(sK3(sK2),sK1)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 4.33/0.97  fof(f2218,plain,(
% 4.33/0.97    sK0 = sK3(sK2) | (~spl9_46 | ~spl9_88)),
% 4.33/0.97    inference(resolution,[],[f2112,f1621])).
% 4.33/0.97  fof(f2112,plain,(
% 4.33/0.97    r2_hidden(sK3(sK2),sK1) | ~spl9_88),
% 4.33/0.97    inference(avatar_component_clause,[],[f2110])).
% 4.33/0.97  fof(f2172,plain,(
% 4.33/0.97    spl9_1 | spl9_54),
% 4.33/0.97    inference(avatar_contradiction_clause,[],[f2171])).
% 4.33/0.97  fof(f2171,plain,(
% 4.33/0.97    $false | (spl9_1 | spl9_54)),
% 4.33/0.97    inference(subsumption_resolution,[],[f2169,f176])).
% 4.33/0.97  fof(f176,plain,(
% 4.33/0.97    k1_xboole_0 != sK2 | spl9_1),
% 4.33/0.97    inference(avatar_component_clause,[],[f174])).
% 4.33/0.97  fof(f174,plain,(
% 4.33/0.97    spl9_1 <=> k1_xboole_0 = sK2),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 4.33/0.97  fof(f2169,plain,(
% 4.33/0.97    k1_xboole_0 = sK2 | spl9_54),
% 4.33/0.97    inference(resolution,[],[f1660,f73])).
% 4.33/0.97  fof(f73,plain,(
% 4.33/0.97    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 4.33/0.97    inference(cnf_transformation,[],[f46])).
% 4.33/0.97  fof(f46,plain,(
% 4.33/0.97    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 4.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f45])).
% 4.33/0.97  fof(f45,plain,(
% 4.33/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 4.33/0.97    introduced(choice_axiom,[])).
% 4.33/0.97  fof(f40,plain,(
% 4.33/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.33/0.97    inference(ennf_transformation,[],[f5])).
% 4.33/0.97  fof(f5,axiom,(
% 4.33/0.97    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 4.33/0.97  fof(f1660,plain,(
% 4.33/0.97    ~r2_hidden(sK3(sK2),sK2) | spl9_54),
% 4.33/0.97    inference(avatar_component_clause,[],[f1659])).
% 4.33/0.97  fof(f1659,plain,(
% 4.33/0.97    spl9_54 <=> r2_hidden(sK3(sK2),sK2)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 4.33/0.97  fof(f2119,plain,(
% 4.33/0.97    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 4.33/0.97    introduced(theory_tautology_sat_conflict,[])).
% 4.33/0.97  fof(f2115,plain,(
% 4.33/0.97    spl9_88 | spl9_1 | ~spl9_4 | ~spl9_46),
% 4.33/0.97    inference(avatar_split_clause,[],[f2114,f1543,f189,f174,f2110])).
% 4.33/0.97  fof(f189,plain,(
% 4.33/0.97    spl9_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 4.33/0.97  fof(f2114,plain,(
% 4.33/0.97    r2_hidden(sK3(sK2),sK1) | (spl9_1 | ~spl9_4 | ~spl9_46)),
% 4.33/0.97    inference(subsumption_resolution,[],[f2096,f176])).
% 4.33/0.97  fof(f2096,plain,(
% 4.33/0.97    r2_hidden(sK3(sK2),sK1) | k1_xboole_0 = sK2 | (~spl9_4 | ~spl9_46)),
% 4.33/0.97    inference(resolution,[],[f1663,f73])).
% 4.33/0.97  fof(f1663,plain,(
% 4.33/0.97    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK1)) ) | (~spl9_4 | ~spl9_46)),
% 4.33/0.97    inference(forward_demodulation,[],[f1602,f220])).
% 4.33/0.97  fof(f220,plain,(
% 4.33/0.97    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.33/0.97    inference(superposition,[],[f216,f76])).
% 4.33/0.97  fof(f76,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f1])).
% 4.33/0.97  fof(f1,axiom,(
% 4.33/0.97    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.33/0.97  fof(f216,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.33/0.97    inference(forward_demodulation,[],[f202,f193])).
% 4.33/0.97  fof(f193,plain,(
% 4.33/0.97    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 4.33/0.97    inference(superposition,[],[f76,f71])).
% 4.33/0.97  fof(f71,plain,(
% 4.33/0.97    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.33/0.97    inference(cnf_transformation,[],[f11])).
% 4.33/0.97  fof(f11,axiom,(
% 4.33/0.97    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 4.33/0.97  fof(f202,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.33/0.97    inference(superposition,[],[f104,f70])).
% 4.33/0.97  fof(f70,plain,(
% 4.33/0.97    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f14])).
% 4.33/0.97  fof(f14,axiom,(
% 4.33/0.97    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.33/0.97  fof(f104,plain,(
% 4.33/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f13])).
% 4.33/0.97  fof(f13,axiom,(
% 4.33/0.97    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.33/0.97  fof(f1602,plain,(
% 4.33/0.97    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))) | r2_hidden(X1,sK1)) ) | (~spl9_4 | ~spl9_46)),
% 4.33/0.97    inference(superposition,[],[f522,f1545])).
% 4.33/0.97  fof(f522,plain,(
% 4.33/0.97    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X0,sK1)) ) | ~spl9_4),
% 4.33/0.97    inference(superposition,[],[f366,f191])).
% 4.33/0.97  fof(f191,plain,(
% 4.33/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl9_4),
% 4.33/0.97    inference(avatar_component_clause,[],[f189])).
% 4.33/0.97  fof(f366,plain,(
% 4.33/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) | r2_hidden(X4,X0)) )),
% 4.33/0.97    inference(forward_demodulation,[],[f172,f104])).
% 4.33/0.97  fof(f172,plain,(
% 4.33/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 4.33/0.97    inference(equality_resolution,[],[f156])).
% 4.33/0.97  fof(f156,plain,(
% 4.33/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 4.33/0.97    inference(definition_unfolding,[],[f105,f127])).
% 4.33/0.97  fof(f127,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.33/0.97    inference(definition_unfolding,[],[f83,f126])).
% 4.33/0.97  fof(f126,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.33/0.97    inference(definition_unfolding,[],[f78,f125])).
% 4.33/0.97  fof(f78,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f33])).
% 4.33/0.97  fof(f33,axiom,(
% 4.33/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.33/0.97  fof(f83,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f15])).
% 4.33/0.97  fof(f15,axiom,(
% 4.33/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.33/0.97  fof(f105,plain,(
% 4.33/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 4.33/0.97    inference(cnf_transformation,[],[f65])).
% 4.33/0.97  fof(f65,plain,(
% 4.33/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f63,f64])).
% 4.33/0.97  fof(f64,plain,(
% 4.33/0.97    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 4.33/0.97    introduced(choice_axiom,[])).
% 4.33/0.97  fof(f63,plain,(
% 4.33/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.33/0.97    inference(rectify,[],[f62])).
% 4.33/0.97  fof(f62,plain,(
% 4.33/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.33/0.97    inference(flattening,[],[f61])).
% 4.33/0.97  fof(f61,plain,(
% 4.33/0.97    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 4.33/0.97    inference(nnf_transformation,[],[f2])).
% 4.33/0.97  fof(f2,axiom,(
% 4.33/0.97    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 4.33/0.97  fof(f2108,plain,(
% 4.33/0.97    spl9_87 | ~spl9_4 | ~spl9_12 | ~spl9_46),
% 4.33/0.97    inference(avatar_split_clause,[],[f2093,f1543,f657,f189,f2105])).
% 4.33/0.97  fof(f657,plain,(
% 4.33/0.97    spl9_12 <=> r2_hidden(sK7(sK0,sK2),sK2)),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 4.33/0.97  fof(f2093,plain,(
% 4.33/0.97    r2_hidden(sK7(sK0,sK2),sK1) | (~spl9_4 | ~spl9_12 | ~spl9_46)),
% 4.33/0.97    inference(resolution,[],[f1663,f659])).
% 4.33/0.97  fof(f659,plain,(
% 4.33/0.97    r2_hidden(sK7(sK0,sK2),sK2) | ~spl9_12),
% 4.33/0.97    inference(avatar_component_clause,[],[f657])).
% 4.33/0.97  fof(f2057,plain,(
% 4.33/0.97    spl9_85 | spl9_2 | ~spl9_46),
% 4.33/0.97    inference(avatar_split_clause,[],[f2052,f1543,f179,f2054])).
% 4.33/0.97  fof(f179,plain,(
% 4.33/0.97    spl9_2 <=> k1_xboole_0 = sK1),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 4.33/0.97  fof(f2052,plain,(
% 4.33/0.97    sK0 = sK3(sK1) | (spl9_2 | ~spl9_46)),
% 4.33/0.97    inference(subsumption_resolution,[],[f2040,f181])).
% 4.33/0.97  fof(f181,plain,(
% 4.33/0.97    k1_xboole_0 != sK1 | spl9_2),
% 4.33/0.97    inference(avatar_component_clause,[],[f179])).
% 4.33/0.97  fof(f2040,plain,(
% 4.33/0.97    sK0 = sK3(sK1) | k1_xboole_0 = sK1 | ~spl9_46),
% 4.33/0.97    inference(resolution,[],[f1621,f73])).
% 4.33/0.97  fof(f1546,plain,(
% 4.33/0.97    spl9_46 | spl9_2 | ~spl9_45),
% 4.33/0.97    inference(avatar_split_clause,[],[f1541,f1534,f179,f1543])).
% 4.33/0.97  fof(f1534,plain,(
% 4.33/0.97    spl9_45 <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 4.33/0.97  fof(f1541,plain,(
% 4.33/0.97    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (spl9_2 | ~spl9_45)),
% 4.33/0.97    inference(subsumption_resolution,[],[f1538,f181])).
% 4.33/0.97  fof(f1538,plain,(
% 4.33/0.97    k1_xboole_0 = sK1 | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl9_45),
% 4.33/0.97    inference(resolution,[],[f1536,f146])).
% 4.33/0.97  fof(f146,plain,(
% 4.33/0.97    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 4.33/0.97    inference(definition_unfolding,[],[f96,f129,f129])).
% 4.33/0.97  fof(f96,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f58])).
% 4.33/0.97  fof(f58,plain,(
% 4.33/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.33/0.97    inference(flattening,[],[f57])).
% 4.33/0.97  fof(f57,plain,(
% 4.33/0.97    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.33/0.97    inference(nnf_transformation,[],[f32])).
% 4.33/0.97  fof(f32,axiom,(
% 4.33/0.97    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 4.33/0.97  fof(f1536,plain,(
% 4.33/0.97    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl9_45),
% 4.33/0.97    inference(avatar_component_clause,[],[f1534])).
% 4.33/0.97  fof(f1537,plain,(
% 4.33/0.97    spl9_45 | ~spl9_4),
% 4.33/0.97    inference(avatar_split_clause,[],[f1522,f189,f1534])).
% 4.33/0.97  fof(f1522,plain,(
% 4.33/0.97    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl9_4),
% 4.33/0.97    inference(superposition,[],[f896,f191])).
% 4.33/0.97  fof(f896,plain,(
% 4.33/0.97    ( ! [X10,X11] : (r1_tarski(X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11)))) )),
% 4.33/0.97    inference(subsumption_resolution,[],[f881,f70])).
% 4.33/0.97  fof(f881,plain,(
% 4.33/0.97    ( ! [X10,X11] : (k1_xboole_0 != k5_xboole_0(k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11)),k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11))) | r1_tarski(X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X11)))) )),
% 4.33/0.97    inference(superposition,[],[f605,f137])).
% 4.33/0.97  fof(f137,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 4.33/0.97    inference(definition_unfolding,[],[f82,f126,f126,f126])).
% 4.33/0.97  fof(f82,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f12])).
% 4.33/0.97  fof(f12,axiom,(
% 4.33/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 4.33/0.97  fof(f605,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 4.33/0.97    inference(forward_demodulation,[],[f604,f216])).
% 4.33/0.97  fof(f604,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) | r1_tarski(X0,X1)) )),
% 4.33/0.97    inference(forward_demodulation,[],[f148,f104])).
% 4.33/0.97  fof(f148,plain,(
% 4.33/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 4.33/0.97    inference(definition_unfolding,[],[f99,f128])).
% 4.33/0.97  fof(f128,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 4.33/0.97    inference(definition_unfolding,[],[f80,f127])).
% 4.33/0.97  fof(f80,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.33/0.97    inference(cnf_transformation,[],[f7])).
% 4.33/0.97  fof(f7,axiom,(
% 4.33/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.33/0.97  fof(f99,plain,(
% 4.33/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f59])).
% 4.33/0.97  fof(f59,plain,(
% 4.33/0.97    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.33/0.97    inference(nnf_transformation,[],[f6])).
% 4.33/0.97  fof(f6,axiom,(
% 4.33/0.97    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.33/0.97  fof(f772,plain,(
% 4.33/0.97    spl9_12 | spl9_11 | spl9_13),
% 4.33/0.97    inference(avatar_split_clause,[],[f767,f661,f588,f657])).
% 4.33/0.97  fof(f588,plain,(
% 4.33/0.97    spl9_11 <=> k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 4.33/0.97  fof(f767,plain,(
% 4.33/0.97    r2_hidden(sK7(sK0,sK2),sK2) | (spl9_11 | spl9_13)),
% 4.33/0.97    inference(subsumption_resolution,[],[f763,f662])).
% 4.33/0.97  fof(f662,plain,(
% 4.33/0.97    sK0 != sK7(sK0,sK2) | spl9_13),
% 4.33/0.97    inference(avatar_component_clause,[],[f661])).
% 4.33/0.97  fof(f763,plain,(
% 4.33/0.97    sK0 = sK7(sK0,sK2) | r2_hidden(sK7(sK0,sK2),sK2) | spl9_11),
% 4.33/0.97    inference(trivial_inequality_removal,[],[f645])).
% 4.33/0.97  fof(f645,plain,(
% 4.33/0.97    k1_xboole_0 != k1_xboole_0 | sK0 = sK7(sK0,sK2) | r2_hidden(sK7(sK0,sK2),sK2) | spl9_11),
% 4.33/0.97    inference(superposition,[],[f619,f70])).
% 4.33/0.97  fof(f619,plain,(
% 4.33/0.97    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(sK2,X0) | sK0 = sK7(sK0,X0) | r2_hidden(sK7(sK0,X0),X0)) ) | spl9_11),
% 4.33/0.97    inference(superposition,[],[f589,f141])).
% 4.33/0.97  fof(f141,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 4.33/0.97    inference(definition_unfolding,[],[f94,f129])).
% 4.33/0.97  fof(f94,plain,(
% 4.33/0.97    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)) )),
% 4.33/0.97    inference(cnf_transformation,[],[f56])).
% 4.33/0.97  fof(f589,plain,(
% 4.33/0.97    k1_xboole_0 != k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl9_11),
% 4.33/0.97    inference(avatar_component_clause,[],[f588])).
% 4.33/0.97  fof(f762,plain,(
% 4.33/0.97    spl9_18 | ~spl9_11),
% 4.33/0.97    inference(avatar_split_clause,[],[f761,f588,f747])).
% 4.33/0.97  fof(f761,plain,(
% 4.33/0.97    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl9_11),
% 4.33/0.97    inference(forward_demodulation,[],[f728,f193])).
% 4.33/0.97  fof(f728,plain,(
% 4.33/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,sK2) | ~spl9_11),
% 4.33/0.97    inference(superposition,[],[f237,f590])).
% 4.33/0.97  fof(f590,plain,(
% 4.33/0.97    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl9_11),
% 4.33/0.97    inference(avatar_component_clause,[],[f588])).
% 4.33/0.97  fof(f237,plain,(
% 4.33/0.97    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.33/0.97    inference(superposition,[],[f220,f220])).
% 4.33/0.97  fof(f192,plain,(
% 4.33/0.97    spl9_4),
% 4.33/0.97    inference(avatar_split_clause,[],[f132,f189])).
% 4.33/0.97  fof(f132,plain,(
% 4.33/0.97    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 4.33/0.97    inference(definition_unfolding,[],[f66,f129,f126])).
% 4.33/0.97  fof(f66,plain,(
% 4.33/0.97    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 4.33/0.97    inference(cnf_transformation,[],[f44])).
% 4.33/0.97  fof(f44,plain,(
% 4.33/0.97    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 4.33/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f43])).
% 4.33/0.97  fof(f43,plain,(
% 4.33/0.97    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 4.33/0.97    introduced(choice_axiom,[])).
% 4.33/0.97  fof(f39,plain,(
% 4.33/0.97    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.33/0.97    inference(ennf_transformation,[],[f36])).
% 4.33/0.97  fof(f36,negated_conjecture,(
% 4.33/0.97    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.33/0.97    inference(negated_conjecture,[],[f35])).
% 4.33/0.97  fof(f35,conjecture,(
% 4.33/0.97    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 4.33/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 4.33/0.97  fof(f187,plain,(
% 4.33/0.97    ~spl9_3),
% 4.33/0.97    inference(avatar_split_clause,[],[f67,f184])).
% 4.33/0.97  fof(f184,plain,(
% 4.33/0.97    spl9_3 <=> sK1 = sK2),
% 4.33/0.97    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 4.33/0.97  fof(f67,plain,(
% 4.33/0.97    sK1 != sK2),
% 4.33/0.97    inference(cnf_transformation,[],[f44])).
% 4.33/0.97  fof(f182,plain,(
% 4.33/0.97    ~spl9_2),
% 4.33/0.97    inference(avatar_split_clause,[],[f68,f179])).
% 4.33/0.97  fof(f68,plain,(
% 4.33/0.97    k1_xboole_0 != sK1),
% 4.33/0.97    inference(cnf_transformation,[],[f44])).
% 4.33/0.97  fof(f177,plain,(
% 4.33/0.97    ~spl9_1),
% 4.33/0.97    inference(avatar_split_clause,[],[f69,f174])).
% 4.33/0.97  fof(f69,plain,(
% 4.33/0.97    k1_xboole_0 != sK2),
% 4.33/0.97    inference(cnf_transformation,[],[f44])).
% 4.33/0.97  % SZS output end Proof for theBenchmark
% 4.33/0.97  % (11332)------------------------------
% 4.33/0.97  % (11332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.97  % (11332)Termination reason: Refutation
% 4.33/0.97  
% 4.33/0.97  % (11332)Memory used [KB]: 13304
% 4.33/0.97  % (11332)Time elapsed: 0.385 s
% 4.33/0.97  % (11332)------------------------------
% 4.33/0.97  % (11332)------------------------------
% 4.33/0.98  % (11279)Success in time 0.606 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 306 expanded)
%              Number of leaves         :   33 ( 118 expanded)
%              Depth                    :   15
%              Number of atoms          :  388 ( 758 expanded)
%              Number of equality atoms :  125 ( 298 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f83,f92,f97,f102,f113,f181,f236,f257,f258,f263,f307,f2048,f2165,f2241,f2259,f2312,f2415,f2484,f2507,f2516])).

fof(f2516,plain,
    ( spl5_12
    | ~ spl5_46 ),
    inference(avatar_contradiction_clause,[],[f2515])).

fof(f2515,plain,
    ( $false
    | spl5_12
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f2509,f157])).

fof(f157,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_12
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2509,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_46 ),
    inference(superposition,[],[f40,f2506])).

fof(f2506,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f2504])).

fof(f2504,plain,
    ( spl5_46
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2507,plain,
    ( spl5_46
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f2329,f99,f89,f2504])).

fof(f89,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f99,plain,
    ( spl5_7
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2329,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f104,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f104,plain,
    ( sK1 = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f101,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f2484,plain,
    ( ~ spl5_15
    | ~ spl5_5
    | spl5_20 ),
    inference(avatar_split_clause,[],[f2437,f260,f89,f202])).

fof(f202,plain,
    ( spl5_15
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f260,plain,
    ( spl5_20
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f2437,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_5
    | spl5_20 ),
    inference(forward_demodulation,[],[f261,f90])).

fof(f261,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f2415,plain,
    ( ~ spl5_1
    | spl5_3
    | spl5_4
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f2414])).

fof(f2414,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | spl5_4
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f2413,f87])).

fof(f87,plain,
    ( sK2 != k1_tarski(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2413,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f107,f362])).

fof(f362,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f349,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f349,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f327,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f327,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f326,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f326,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f306,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f306,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl5_22
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f107,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_1
    | spl5_3
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f71,f106])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f103,f82])).

fof(f82,plain,
    ( sK1 != k1_tarski(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_3
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f103,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(resolution,[],[f101,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f71,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2312,plain,
    ( ~ spl5_3
    | spl5_6
    | ~ spl5_11
    | spl5_36 ),
    inference(avatar_contradiction_clause,[],[f2311])).

fof(f2311,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | ~ spl5_11
    | spl5_36 ),
    inference(subsumption_resolution,[],[f696,f2307])).

fof(f2307,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f1856,f96])).

fof(f96,plain,
    ( sK1 != sK2
    | spl5_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1856,plain,
    ( sK1 = sK2
    | k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(superposition,[],[f144,f770])).

fof(f770,plain,
    ( ! [X1] :
        ( k2_xboole_0(sK1,X1) = X1
        | k1_xboole_0 = k3_xboole_0(X1,sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f409,f49])).

fof(f409,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | k1_xboole_0 = k3_xboole_0(X0,sK1) )
    | ~ spl5_3 ),
    inference(superposition,[],[f40,f328])).

fof(f328,plain,
    ( ! [X1] :
        ( sK1 = k3_xboole_0(X1,sK1)
        | k1_xboole_0 = k3_xboole_0(X1,sK1) )
    | ~ spl5_3 ),
    inference(superposition,[],[f245,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f245,plain,
    ( ! [X0] :
        ( sK1 = k3_xboole_0(sK1,X0)
        | k1_xboole_0 = k3_xboole_0(sK1,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f221,f40])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_3 ),
    inference(superposition,[],[f56,f81])).

fof(f81,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f144,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_11
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f696,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,sK1)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl5_36
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f2259,plain,
    ( ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_36
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f2258])).

fof(f2258,plain,
    ( $false
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_36
    | spl5_39 ),
    inference(subsumption_resolution,[],[f1645,f2257])).

fof(f2257,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f717,f2256])).

fof(f2256,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f2255,f467])).

fof(f467,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f458,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f458,plain,
    ( ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(superposition,[],[f45,f367])).

fof(f367,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(superposition,[],[f361,f42])).

fof(f361,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_20
    | ~ spl5_22 ),
    inference(resolution,[],[f349,f50])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2255,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f256,f710])).

fof(f710,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_36 ),
    inference(superposition,[],[f42,f697])).

fof(f697,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f695])).

fof(f256,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl5_19
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f717,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f712,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f712,plain,
    ( k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_36 ),
    inference(superposition,[],[f46,f697])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f1645,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f1644,plain,
    ( spl5_39
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f2241,plain,
    ( spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_41 ),
    inference(avatar_contradiction_clause,[],[f2240])).

fof(f2240,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f2239,f78])).

fof(f78,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2239,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f2236,f96])).

fof(f2236,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_41 ),
    inference(resolution,[],[f2164,f221])).

fof(f2164,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f2162])).

fof(f2162,plain,
    ( spl5_41
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f2165,plain,
    ( spl5_41
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f2130,f2045,f2162])).

fof(f2045,plain,
    ( spl5_40
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f2130,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_40 ),
    inference(superposition,[],[f39,f2047])).

fof(f2047,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f2045])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2048,plain,
    ( spl5_40
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f2034,f1644,f304,f260,f2045])).

fof(f2034,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_20
    | ~ spl5_22
    | ~ spl5_39 ),
    inference(superposition,[],[f1646,f467])).

fof(f1646,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f307,plain,
    ( spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f286,f260,f304])).

fof(f286,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_20 ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_20 ),
    inference(superposition,[],[f51,f262])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f263,plain,
    ( spl5_20
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f218,f178,f260])).

fof(f178,plain,
    ( spl5_13
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f218,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f180,f50])).

fof(f180,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f258,plain,
    ( spl5_15
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f194,f156,f202])).

fof(f194,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_12 ),
    inference(resolution,[],[f158,f50])).

fof(f158,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f257,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f233,f80,f69,f254])).

fof(f233,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f74,f81])).

fof(f74,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f46,f71])).

fof(f236,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f125,f80,f69,f142])).

fof(f125,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f71,f81])).

fof(f181,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f138,f80,f178])).

fof(f138,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f66,f81])).

fof(f66,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,
    ( spl5_5
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f106,f99,f80,f89])).

fof(f102,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f73,f69,f99])).

fof(f73,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(superposition,[],[f39,f71])).

fof(f97,plain,
    ( ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f67,f80,f94])).

fof(f67,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f92,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f33,f89,f85])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f80,f76])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (19274)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (19272)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (19271)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (19288)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (19280)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (19273)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (19292)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (19280)Refutation not found, incomplete strategy% (19280)------------------------------
% 0.22/0.54  % (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19275)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (19284)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (19280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (19280)Memory used [KB]: 10618
% 0.22/0.54  % (19280)Time elapsed: 0.095 s
% 0.22/0.54  % (19280)------------------------------
% 0.22/0.54  % (19280)------------------------------
% 0.22/0.55  % (19298)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (19270)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (19276)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (19297)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (19277)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (19282)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (19299)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (19278)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (19286)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (19290)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (19289)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.56  % (19287)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.56  % (19287)Refutation not found, incomplete strategy% (19287)------------------------------
% 1.42/0.56  % (19287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (19287)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (19287)Memory used [KB]: 10618
% 1.42/0.56  % (19287)Time elapsed: 0.147 s
% 1.42/0.56  % (19287)------------------------------
% 1.42/0.56  % (19287)------------------------------
% 1.42/0.56  % (19293)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.56  % (19291)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (19279)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (19296)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.56  % (19281)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.56  % (19281)Refutation not found, incomplete strategy% (19281)------------------------------
% 1.42/0.56  % (19281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (19281)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (19281)Memory used [KB]: 10746
% 1.42/0.56  % (19281)Time elapsed: 0.150 s
% 1.42/0.56  % (19281)------------------------------
% 1.42/0.56  % (19281)------------------------------
% 1.42/0.56  % (19285)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.57  % (19283)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.57  % (19285)Refutation not found, incomplete strategy% (19285)------------------------------
% 1.42/0.57  % (19285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (19285)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (19285)Memory used [KB]: 6140
% 1.42/0.57  % (19285)Time elapsed: 0.002 s
% 1.42/0.57  % (19285)------------------------------
% 1.42/0.57  % (19285)------------------------------
% 1.42/0.57  % (19294)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.42/0.57  % (19295)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.64  % (19300)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.68  % (19301)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.23/0.69  % (19302)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.23/0.70  % (19303)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.51/0.73  % (19290)Refutation found. Thanks to Tanya!
% 2.51/0.73  % SZS status Theorem for theBenchmark
% 2.51/0.73  % SZS output start Proof for theBenchmark
% 2.51/0.73  fof(f2520,plain,(
% 2.51/0.73    $false),
% 2.51/0.73    inference(avatar_sat_refutation,[],[f72,f83,f92,f97,f102,f113,f181,f236,f257,f258,f263,f307,f2048,f2165,f2241,f2259,f2312,f2415,f2484,f2507,f2516])).
% 2.51/0.73  fof(f2516,plain,(
% 2.51/0.73    spl5_12 | ~spl5_46),
% 2.51/0.73    inference(avatar_contradiction_clause,[],[f2515])).
% 2.51/0.73  fof(f2515,plain,(
% 2.51/0.73    $false | (spl5_12 | ~spl5_46)),
% 2.51/0.73    inference(subsumption_resolution,[],[f2509,f157])).
% 2.51/0.73  fof(f157,plain,(
% 2.51/0.73    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl5_12),
% 2.51/0.73    inference(avatar_component_clause,[],[f156])).
% 2.51/0.73  fof(f156,plain,(
% 2.51/0.73    spl5_12 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.51/0.73  fof(f2509,plain,(
% 2.51/0.73    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_46),
% 2.51/0.73    inference(superposition,[],[f40,f2506])).
% 2.51/0.73  fof(f2506,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_46),
% 2.51/0.73    inference(avatar_component_clause,[],[f2504])).
% 2.51/0.73  fof(f2504,plain,(
% 2.51/0.73    spl5_46 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.51/0.73  fof(f40,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f10])).
% 2.51/0.73  fof(f10,axiom,(
% 2.51/0.73    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.51/0.73  fof(f2507,plain,(
% 2.51/0.73    spl5_46 | ~spl5_5 | ~spl5_7),
% 2.51/0.73    inference(avatar_split_clause,[],[f2329,f99,f89,f2504])).
% 2.51/0.73  fof(f89,plain,(
% 2.51/0.73    spl5_5 <=> k1_xboole_0 = sK1),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.51/0.73  fof(f99,plain,(
% 2.51/0.73    spl5_7 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.51/0.73  fof(f2329,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) | (~spl5_5 | ~spl5_7)),
% 2.51/0.73    inference(backward_demodulation,[],[f104,f90])).
% 2.51/0.73  fof(f90,plain,(
% 2.51/0.73    k1_xboole_0 = sK1 | ~spl5_5),
% 2.51/0.73    inference(avatar_component_clause,[],[f89])).
% 2.51/0.73  fof(f104,plain,(
% 2.51/0.73    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl5_7),
% 2.51/0.73    inference(resolution,[],[f101,f50])).
% 2.51/0.73  fof(f50,plain,(
% 2.51/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.51/0.73    inference(cnf_transformation,[],[f30])).
% 2.51/0.73  fof(f30,plain,(
% 2.51/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.51/0.73    inference(ennf_transformation,[],[f11])).
% 2.51/0.73  fof(f11,axiom,(
% 2.51/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.51/0.73  fof(f101,plain,(
% 2.51/0.73    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_7),
% 2.51/0.73    inference(avatar_component_clause,[],[f99])).
% 2.51/0.73  fof(f2484,plain,(
% 2.51/0.73    ~spl5_15 | ~spl5_5 | spl5_20),
% 2.51/0.73    inference(avatar_split_clause,[],[f2437,f260,f89,f202])).
% 2.51/0.73  fof(f202,plain,(
% 2.51/0.73    spl5_15 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.51/0.73  fof(f260,plain,(
% 2.51/0.73    spl5_20 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.51/0.73  fof(f2437,plain,(
% 2.51/0.73    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl5_5 | spl5_20)),
% 2.51/0.73    inference(forward_demodulation,[],[f261,f90])).
% 2.51/0.73  fof(f261,plain,(
% 2.51/0.73    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | spl5_20),
% 2.51/0.73    inference(avatar_component_clause,[],[f260])).
% 2.51/0.73  fof(f2415,plain,(
% 2.51/0.73    ~spl5_1 | spl5_3 | spl5_4 | ~spl5_7 | ~spl5_20 | ~spl5_22),
% 2.51/0.73    inference(avatar_contradiction_clause,[],[f2414])).
% 2.51/0.73  fof(f2414,plain,(
% 2.51/0.73    $false | (~spl5_1 | spl5_3 | spl5_4 | ~spl5_7 | ~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(subsumption_resolution,[],[f2413,f87])).
% 2.51/0.73  fof(f87,plain,(
% 2.51/0.73    sK2 != k1_tarski(sK0) | spl5_4),
% 2.51/0.73    inference(avatar_component_clause,[],[f85])).
% 2.51/0.73  fof(f85,plain,(
% 2.51/0.73    spl5_4 <=> sK2 = k1_tarski(sK0)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.51/0.73  fof(f2413,plain,(
% 2.51/0.73    sK2 = k1_tarski(sK0) | (~spl5_1 | spl5_3 | ~spl5_7 | ~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(forward_demodulation,[],[f107,f362])).
% 2.51/0.73  fof(f362,plain,(
% 2.51/0.73    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(resolution,[],[f349,f49])).
% 2.51/0.73  fof(f49,plain,(
% 2.51/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.51/0.73    inference(cnf_transformation,[],[f29])).
% 2.51/0.73  fof(f29,plain,(
% 2.51/0.73    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.51/0.73    inference(ennf_transformation,[],[f8])).
% 2.51/0.73  fof(f8,axiom,(
% 2.51/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.51/0.73  fof(f349,plain,(
% 2.51/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(resolution,[],[f327,f54])).
% 2.51/0.73  fof(f54,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f31])).
% 2.51/0.73  fof(f31,plain,(
% 2.51/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.51/0.73    inference(ennf_transformation,[],[f3])).
% 2.51/0.73  fof(f3,axiom,(
% 2.51/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.51/0.73  fof(f327,plain,(
% 2.51/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(forward_demodulation,[],[f326,f262])).
% 2.51/0.73  fof(f262,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl5_20),
% 2.51/0.73    inference(avatar_component_clause,[],[f260])).
% 2.51/0.73  fof(f326,plain,(
% 2.51/0.73    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,sK1))) ) | ~spl5_22),
% 2.51/0.73    inference(resolution,[],[f306,f47])).
% 2.51/0.73  fof(f47,plain,(
% 2.51/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f28])).
% 2.51/0.73  fof(f28,plain,(
% 2.51/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.51/0.73    inference(ennf_transformation,[],[f26])).
% 2.51/0.73  fof(f26,plain,(
% 2.51/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.51/0.73    inference(rectify,[],[f5])).
% 2.51/0.73  fof(f5,axiom,(
% 2.51/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.51/0.73  fof(f306,plain,(
% 2.51/0.73    r1_xboole_0(k1_xboole_0,sK1) | ~spl5_22),
% 2.51/0.73    inference(avatar_component_clause,[],[f304])).
% 2.51/0.73  fof(f304,plain,(
% 2.51/0.73    spl5_22 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.51/0.73  fof(f107,plain,(
% 2.51/0.73    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl5_1 | spl5_3 | ~spl5_7)),
% 2.51/0.73    inference(backward_demodulation,[],[f71,f106])).
% 2.51/0.73  fof(f106,plain,(
% 2.51/0.73    k1_xboole_0 = sK1 | (spl5_3 | ~spl5_7)),
% 2.51/0.73    inference(subsumption_resolution,[],[f103,f82])).
% 2.51/0.73  fof(f82,plain,(
% 2.51/0.73    sK1 != k1_tarski(sK0) | spl5_3),
% 2.51/0.73    inference(avatar_component_clause,[],[f80])).
% 2.51/0.73  fof(f80,plain,(
% 2.51/0.73    spl5_3 <=> sK1 = k1_tarski(sK0)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.51/0.73  fof(f103,plain,(
% 2.51/0.73    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl5_7),
% 2.51/0.73    inference(resolution,[],[f101,f56])).
% 2.51/0.73  fof(f56,plain,(
% 2.51/0.73    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 2.51/0.73    inference(cnf_transformation,[],[f22])).
% 2.51/0.73  fof(f22,axiom,(
% 2.51/0.73    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.51/0.73  fof(f71,plain,(
% 2.51/0.73    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl5_1),
% 2.51/0.73    inference(avatar_component_clause,[],[f69])).
% 2.51/0.73  fof(f69,plain,(
% 2.51/0.73    spl5_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.51/0.73  fof(f2312,plain,(
% 2.51/0.73    ~spl5_3 | spl5_6 | ~spl5_11 | spl5_36),
% 2.51/0.73    inference(avatar_contradiction_clause,[],[f2311])).
% 2.51/0.73  fof(f2311,plain,(
% 2.51/0.73    $false | (~spl5_3 | spl5_6 | ~spl5_11 | spl5_36)),
% 2.51/0.73    inference(subsumption_resolution,[],[f696,f2307])).
% 2.51/0.73  fof(f2307,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl5_3 | spl5_6 | ~spl5_11)),
% 2.51/0.73    inference(subsumption_resolution,[],[f1856,f96])).
% 2.51/0.73  fof(f96,plain,(
% 2.51/0.73    sK1 != sK2 | spl5_6),
% 2.51/0.73    inference(avatar_component_clause,[],[f94])).
% 2.51/0.73  fof(f94,plain,(
% 2.51/0.73    spl5_6 <=> sK1 = sK2),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.51/0.73  fof(f1856,plain,(
% 2.51/0.73    sK1 = sK2 | k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_11)),
% 2.51/0.73    inference(superposition,[],[f144,f770])).
% 2.51/0.73  fof(f770,plain,(
% 2.51/0.73    ( ! [X1] : (k2_xboole_0(sK1,X1) = X1 | k1_xboole_0 = k3_xboole_0(X1,sK1)) ) | ~spl5_3),
% 2.51/0.73    inference(resolution,[],[f409,f49])).
% 2.51/0.73  fof(f409,plain,(
% 2.51/0.73    ( ! [X0] : (r1_tarski(sK1,X0) | k1_xboole_0 = k3_xboole_0(X0,sK1)) ) | ~spl5_3),
% 2.51/0.73    inference(superposition,[],[f40,f328])).
% 2.51/0.73  fof(f328,plain,(
% 2.51/0.73    ( ! [X1] : (sK1 = k3_xboole_0(X1,sK1) | k1_xboole_0 = k3_xboole_0(X1,sK1)) ) | ~spl5_3),
% 2.51/0.73    inference(superposition,[],[f245,f42])).
% 2.51/0.73  fof(f42,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f1])).
% 2.51/0.73  fof(f1,axiom,(
% 2.51/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.51/0.73  fof(f245,plain,(
% 2.51/0.73    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) ) | ~spl5_3),
% 2.51/0.73    inference(resolution,[],[f221,f40])).
% 2.51/0.73  fof(f221,plain,(
% 2.51/0.73    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl5_3),
% 2.51/0.73    inference(superposition,[],[f56,f81])).
% 2.51/0.73  fof(f81,plain,(
% 2.51/0.73    sK1 = k1_tarski(sK0) | ~spl5_3),
% 2.51/0.73    inference(avatar_component_clause,[],[f80])).
% 2.51/0.73  fof(f144,plain,(
% 2.51/0.73    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_11),
% 2.51/0.73    inference(avatar_component_clause,[],[f142])).
% 2.51/0.73  fof(f142,plain,(
% 2.51/0.73    spl5_11 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.51/0.73  fof(f696,plain,(
% 2.51/0.73    k1_xboole_0 != k3_xboole_0(sK2,sK1) | spl5_36),
% 2.51/0.73    inference(avatar_component_clause,[],[f695])).
% 2.51/0.73  fof(f695,plain,(
% 2.51/0.73    spl5_36 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.51/0.73  fof(f2259,plain,(
% 2.51/0.73    ~spl5_19 | ~spl5_20 | ~spl5_22 | ~spl5_36 | spl5_39),
% 2.51/0.73    inference(avatar_contradiction_clause,[],[f2258])).
% 2.51/0.73  fof(f2258,plain,(
% 2.51/0.73    $false | (~spl5_19 | ~spl5_20 | ~spl5_22 | ~spl5_36 | spl5_39)),
% 2.51/0.73    inference(subsumption_resolution,[],[f1645,f2257])).
% 2.51/0.73  fof(f2257,plain,(
% 2.51/0.73    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | (~spl5_19 | ~spl5_20 | ~spl5_22 | ~spl5_36)),
% 2.51/0.73    inference(forward_demodulation,[],[f717,f2256])).
% 2.51/0.73  fof(f2256,plain,(
% 2.51/0.73    sK1 = k5_xboole_0(sK1,sK2) | (~spl5_19 | ~spl5_20 | ~spl5_22 | ~spl5_36)),
% 2.51/0.73    inference(forward_demodulation,[],[f2255,f467])).
% 2.51/0.73  fof(f467,plain,(
% 2.51/0.73    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(forward_demodulation,[],[f458,f37])).
% 2.51/0.73  fof(f37,plain,(
% 2.51/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.51/0.73    inference(cnf_transformation,[],[f12])).
% 2.51/0.73  fof(f12,axiom,(
% 2.51/0.73    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.51/0.73  fof(f458,plain,(
% 2.51/0.73    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(superposition,[],[f45,f367])).
% 2.51/0.73  fof(f367,plain,(
% 2.51/0.73    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(superposition,[],[f361,f42])).
% 2.51/0.73  fof(f361,plain,(
% 2.51/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_20 | ~spl5_22)),
% 2.51/0.73    inference(resolution,[],[f349,f50])).
% 2.51/0.73  fof(f45,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f7])).
% 2.51/0.73  fof(f7,axiom,(
% 2.51/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.51/0.73  fof(f2255,plain,(
% 2.51/0.73    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | (~spl5_19 | ~spl5_36)),
% 2.51/0.73    inference(forward_demodulation,[],[f256,f710])).
% 2.51/0.73  fof(f710,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl5_36),
% 2.51/0.73    inference(superposition,[],[f42,f697])).
% 2.51/0.73  fof(f697,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_36),
% 2.51/0.73    inference(avatar_component_clause,[],[f695])).
% 2.51/0.73  fof(f256,plain,(
% 2.51/0.73    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_19),
% 2.51/0.73    inference(avatar_component_clause,[],[f254])).
% 2.51/0.73  fof(f254,plain,(
% 2.51/0.73    spl5_19 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.51/0.73  fof(f717,plain,(
% 2.51/0.73    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_36),
% 2.51/0.73    inference(forward_demodulation,[],[f712,f41])).
% 2.51/0.73  fof(f41,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f2])).
% 2.51/0.73  fof(f2,axiom,(
% 2.51/0.73    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.51/0.73  fof(f712,plain,(
% 2.51/0.73    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_36),
% 2.51/0.73    inference(superposition,[],[f46,f697])).
% 2.51/0.73  fof(f46,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f6])).
% 2.51/0.73  fof(f6,axiom,(
% 2.51/0.73    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.51/0.73  fof(f1645,plain,(
% 2.51/0.73    sK1 != k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | spl5_39),
% 2.51/0.73    inference(avatar_component_clause,[],[f1644])).
% 2.51/0.73  fof(f1644,plain,(
% 2.51/0.73    spl5_39 <=> sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.51/0.73  fof(f2241,plain,(
% 2.51/0.73    spl5_2 | ~spl5_3 | spl5_6 | ~spl5_41),
% 2.51/0.73    inference(avatar_contradiction_clause,[],[f2240])).
% 2.51/0.73  fof(f2240,plain,(
% 2.51/0.73    $false | (spl5_2 | ~spl5_3 | spl5_6 | ~spl5_41)),
% 2.51/0.73    inference(subsumption_resolution,[],[f2239,f78])).
% 2.51/0.73  fof(f78,plain,(
% 2.51/0.73    k1_xboole_0 != sK2 | spl5_2),
% 2.51/0.73    inference(avatar_component_clause,[],[f76])).
% 2.51/0.73  fof(f76,plain,(
% 2.51/0.73    spl5_2 <=> k1_xboole_0 = sK2),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.51/0.73  fof(f2239,plain,(
% 2.51/0.73    k1_xboole_0 = sK2 | (~spl5_3 | spl5_6 | ~spl5_41)),
% 2.51/0.73    inference(subsumption_resolution,[],[f2236,f96])).
% 2.51/0.73  fof(f2236,plain,(
% 2.51/0.73    sK1 = sK2 | k1_xboole_0 = sK2 | (~spl5_3 | ~spl5_41)),
% 2.51/0.73    inference(resolution,[],[f2164,f221])).
% 2.51/0.73  fof(f2164,plain,(
% 2.51/0.73    r1_tarski(sK2,sK1) | ~spl5_41),
% 2.51/0.73    inference(avatar_component_clause,[],[f2162])).
% 2.51/0.73  fof(f2162,plain,(
% 2.51/0.73    spl5_41 <=> r1_tarski(sK2,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.51/0.73  fof(f2165,plain,(
% 2.51/0.73    spl5_41 | ~spl5_40),
% 2.51/0.73    inference(avatar_split_clause,[],[f2130,f2045,f2162])).
% 2.51/0.73  fof(f2045,plain,(
% 2.51/0.73    spl5_40 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.51/0.73  fof(f2130,plain,(
% 2.51/0.73    r1_tarski(sK2,sK1) | ~spl5_40),
% 2.51/0.73    inference(superposition,[],[f39,f2047])).
% 2.51/0.73  fof(f2047,plain,(
% 2.51/0.73    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_40),
% 2.51/0.73    inference(avatar_component_clause,[],[f2045])).
% 2.51/0.73  fof(f39,plain,(
% 2.51/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f13])).
% 2.51/0.73  fof(f13,axiom,(
% 2.51/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.51/0.73  fof(f2048,plain,(
% 2.51/0.73    spl5_40 | ~spl5_20 | ~spl5_22 | ~spl5_39),
% 2.51/0.73    inference(avatar_split_clause,[],[f2034,f1644,f304,f260,f2045])).
% 2.51/0.73  fof(f2034,plain,(
% 2.51/0.73    sK1 = k2_xboole_0(sK2,sK1) | (~spl5_20 | ~spl5_22 | ~spl5_39)),
% 2.51/0.73    inference(superposition,[],[f1646,f467])).
% 2.51/0.73  fof(f1646,plain,(
% 2.51/0.73    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_39),
% 2.51/0.73    inference(avatar_component_clause,[],[f1644])).
% 2.51/0.73  fof(f307,plain,(
% 2.51/0.73    spl5_22 | ~spl5_20),
% 2.51/0.73    inference(avatar_split_clause,[],[f286,f260,f304])).
% 2.51/0.73  fof(f286,plain,(
% 2.51/0.73    r1_xboole_0(k1_xboole_0,sK1) | ~spl5_20),
% 2.51/0.73    inference(trivial_inequality_removal,[],[f284])).
% 2.51/0.73  fof(f284,plain,(
% 2.51/0.73    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,sK1) | ~spl5_20),
% 2.51/0.73    inference(superposition,[],[f51,f262])).
% 2.51/0.73  fof(f51,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.51/0.73    inference(cnf_transformation,[],[f4])).
% 2.51/0.73  fof(f4,axiom,(
% 2.51/0.73    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.51/0.73  fof(f263,plain,(
% 2.51/0.73    spl5_20 | ~spl5_13),
% 2.51/0.73    inference(avatar_split_clause,[],[f218,f178,f260])).
% 2.51/0.73  fof(f178,plain,(
% 2.51/0.73    spl5_13 <=> r1_tarski(k1_xboole_0,sK1)),
% 2.51/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.51/0.73  fof(f218,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl5_13),
% 2.51/0.73    inference(resolution,[],[f180,f50])).
% 2.51/0.73  fof(f180,plain,(
% 2.51/0.73    r1_tarski(k1_xboole_0,sK1) | ~spl5_13),
% 2.51/0.73    inference(avatar_component_clause,[],[f178])).
% 2.51/0.73  fof(f258,plain,(
% 2.51/0.73    spl5_15 | ~spl5_12),
% 2.51/0.73    inference(avatar_split_clause,[],[f194,f156,f202])).
% 2.51/0.73  fof(f194,plain,(
% 2.51/0.73    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_12),
% 2.51/0.73    inference(resolution,[],[f158,f50])).
% 2.51/0.73  fof(f158,plain,(
% 2.51/0.73    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_12),
% 2.51/0.73    inference(avatar_component_clause,[],[f156])).
% 2.51/0.73  fof(f257,plain,(
% 2.51/0.73    spl5_19 | ~spl5_1 | ~spl5_3),
% 2.51/0.73    inference(avatar_split_clause,[],[f233,f80,f69,f254])).
% 2.51/0.73  fof(f233,plain,(
% 2.51/0.73    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | (~spl5_1 | ~spl5_3)),
% 2.51/0.73    inference(forward_demodulation,[],[f74,f81])).
% 2.51/0.73  fof(f74,plain,(
% 2.51/0.73    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl5_1),
% 2.51/0.73    inference(superposition,[],[f46,f71])).
% 2.51/0.73  fof(f236,plain,(
% 2.51/0.73    spl5_11 | ~spl5_1 | ~spl5_3),
% 2.51/0.73    inference(avatar_split_clause,[],[f125,f80,f69,f142])).
% 2.51/0.73  fof(f125,plain,(
% 2.51/0.73    sK1 = k2_xboole_0(sK1,sK2) | (~spl5_1 | ~spl5_3)),
% 2.51/0.73    inference(backward_demodulation,[],[f71,f81])).
% 2.51/0.73  fof(f181,plain,(
% 2.51/0.73    spl5_13 | ~spl5_3),
% 2.51/0.73    inference(avatar_split_clause,[],[f138,f80,f178])).
% 2.51/0.73  fof(f138,plain,(
% 2.51/0.73    r1_tarski(k1_xboole_0,sK1) | ~spl5_3),
% 2.51/0.73    inference(superposition,[],[f66,f81])).
% 2.51/0.73  fof(f66,plain,(
% 2.51/0.73    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 2.51/0.73    inference(equality_resolution,[],[f57])).
% 2.51/0.73  fof(f57,plain,(
% 2.51/0.73    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 2.51/0.73    inference(cnf_transformation,[],[f22])).
% 2.51/0.73  fof(f113,plain,(
% 2.51/0.73    spl5_5 | spl5_3 | ~spl5_7),
% 2.51/0.73    inference(avatar_split_clause,[],[f106,f99,f80,f89])).
% 2.51/0.73  fof(f102,plain,(
% 2.51/0.73    spl5_7 | ~spl5_1),
% 2.51/0.73    inference(avatar_split_clause,[],[f73,f69,f99])).
% 2.51/0.73  fof(f73,plain,(
% 2.51/0.73    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_1),
% 2.51/0.73    inference(superposition,[],[f39,f71])).
% 2.51/0.73  fof(f97,plain,(
% 2.51/0.73    ~spl5_6 | ~spl5_3),
% 2.51/0.73    inference(avatar_split_clause,[],[f67,f80,f94])).
% 2.51/0.73  fof(f67,plain,(
% 2.51/0.73    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 2.51/0.73    inference(inner_rewriting,[],[f34])).
% 2.51/0.73  fof(f34,plain,(
% 2.51/0.73    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  fof(f27,plain,(
% 2.51/0.73    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.51/0.73    inference(ennf_transformation,[],[f25])).
% 2.51/0.73  fof(f25,negated_conjecture,(
% 2.51/0.73    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.51/0.73    inference(negated_conjecture,[],[f24])).
% 2.51/0.73  fof(f24,conjecture,(
% 2.51/0.73    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.51/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.51/0.73  fof(f92,plain,(
% 2.51/0.73    ~spl5_4 | ~spl5_5),
% 2.51/0.73    inference(avatar_split_clause,[],[f33,f89,f85])).
% 2.51/0.73  fof(f33,plain,(
% 2.51/0.73    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  fof(f83,plain,(
% 2.51/0.73    ~spl5_2 | ~spl5_3),
% 2.51/0.73    inference(avatar_split_clause,[],[f32,f80,f76])).
% 2.51/0.73  fof(f32,plain,(
% 2.51/0.73    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  fof(f72,plain,(
% 2.51/0.73    spl5_1),
% 2.51/0.73    inference(avatar_split_clause,[],[f35,f69])).
% 2.51/0.73  fof(f35,plain,(
% 2.51/0.73    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.51/0.73    inference(cnf_transformation,[],[f27])).
% 2.51/0.73  % SZS output end Proof for theBenchmark
% 2.51/0.73  % (19290)------------------------------
% 2.51/0.73  % (19290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.73  % (19290)Termination reason: Refutation
% 2.51/0.73  
% 2.51/0.73  % (19290)Memory used [KB]: 12153
% 2.51/0.73  % (19290)Time elapsed: 0.299 s
% 2.51/0.73  % (19290)------------------------------
% 2.51/0.73  % (19290)------------------------------
% 2.51/0.74  % (19269)Success in time 0.368 s
%------------------------------------------------------------------------------

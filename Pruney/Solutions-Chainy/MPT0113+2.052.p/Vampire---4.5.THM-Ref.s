%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 181 expanded)
%              Number of leaves         :   33 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  271 ( 429 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f716,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f64,f68,f72,f76,f82,f113,f128,f147,f167,f282,f331,f380,f393,f430,f511,f699,f715])).

fof(f715,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | spl3_15
    | ~ spl3_20
    | ~ spl3_32
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_12
    | spl3_15
    | ~ spl3_20
    | ~ spl3_32
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f127,f713])).

fof(f713,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_20
    | ~ spl3_32
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f712,f460])).

fof(f460,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f431,f173])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f166,f75])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f166,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_20
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f431,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)
    | ~ spl3_20
    | ~ spl3_36 ),
    inference(unit_resulting_resolution,[],[f166,f429])).

fof(f429,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl3_36
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f712,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl3_12
    | ~ spl3_32
    | ~ spl3_34
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f705,f389])).

fof(f389,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl3_12
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f386,f81])).

fof(f81,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f386,plain,
    ( ! [X8,X9] : k5_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,k3_xboole_0(X8,X9))
    | ~ spl3_32
    | ~ spl3_34 ),
    inference(superposition,[],[f379,f330])).

fof(f330,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl3_32
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f379,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl3_34
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f705,plain,
    ( k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(unit_resulting_resolution,[],[f698,f429])).

fof(f698,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f696])).

fof(f696,plain,
    ( spl3_46
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f127,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f699,plain,
    ( spl3_46
    | ~ spl3_18
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f413,f391,f144,f696])).

fof(f144,plain,
    ( spl3_18
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f391,plain,
    ( spl3_35
  <=> ! [X9,X8,X10] : r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f413,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_18
    | ~ spl3_35 ),
    inference(superposition,[],[f392,f146])).

fof(f146,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f392,plain,
    ( ! [X10,X8,X9] : r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f391])).

fof(f511,plain,
    ( spl3_3
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f297,f280,f144,f39])).

fof(f39,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f280,plain,
    ( spl3_29
  <=> ! [X11,X13,X12] : r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f297,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_18
    | ~ spl3_29 ),
    inference(superposition,[],[f281,f146])).

fof(f281,plain,
    ( ! [X12,X13,X11] : r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f280])).

fof(f430,plain,
    ( spl3_36
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f107,f80,f66,f428])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f81,f67])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f393,plain,
    ( spl3_35
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f122,f111,f56,f391])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f122,plain,
    ( ! [X10,X8,X9] : r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f57,f112])).

fof(f112,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f111])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f380,plain,
    ( spl3_34
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f108,f80,f62,f378])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f81,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f331,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f66,f52,f329])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f88,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f53,f67])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f282,plain,
    ( spl3_29
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f123,f111,f48,f280])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f123,plain,
    ( ! [X12,X13,X11] : r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(superposition,[],[f49,f112])).

fof(f49,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f167,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f60,f56,f44,f165])).

fof(f44,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f147,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f87,f66,f30,f144])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f32,f67])).

fof(f32,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f128,plain,
    ( ~ spl3_15
    | spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f95,f70,f35,f125])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f37,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f113,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f28,f111])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f82,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f80])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f76,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f72,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f56])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f39,f35])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (15880)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (15888)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (15889)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15878)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (15881)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (15887)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (15891)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (15882)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (15892)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (15880)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (15875)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (15890)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (15876)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (15883)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (15885)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (15879)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15884)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f716,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f64,f68,f72,f76,f82,f113,f128,f147,f167,f282,f331,f380,f393,f430,f511,f699,f715])).
% 0.22/0.50  fof(f715,plain,(
% 0.22/0.50    ~spl3_11 | ~spl3_12 | spl3_15 | ~spl3_20 | ~spl3_32 | ~spl3_34 | ~spl3_36 | ~spl3_46),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f714])).
% 0.22/0.50  fof(f714,plain,(
% 0.22/0.50    $false | (~spl3_11 | ~spl3_12 | spl3_15 | ~spl3_20 | ~spl3_32 | ~spl3_34 | ~spl3_36 | ~spl3_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f127,f713])).
% 0.22/0.50  fof(f713,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_11 | ~spl3_12 | ~spl3_20 | ~spl3_32 | ~spl3_34 | ~spl3_36 | ~spl3_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f712,f460])).
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl3_11 | ~spl3_20 | ~spl3_36)),
% 0.22/0.50    inference(forward_demodulation,[],[f431,f173])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_11 | ~spl3_20)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f166,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl3_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl3_20 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) ) | (~spl3_20 | ~spl3_36)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f166,f429])).
% 0.22/0.50  fof(f429,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | ~spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f428])).
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    spl3_36 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f712,plain,(
% 0.22/0.50    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) | (~spl3_12 | ~spl3_32 | ~spl3_34 | ~spl3_36 | ~spl3_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f705,f389])).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl3_12 | ~spl3_32 | ~spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f386,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    ( ! [X8,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,k3_xboole_0(X8,X9))) ) | (~spl3_32 | ~spl3_34)),
% 0.22/0.50    inference(superposition,[],[f379,f330])).
% 0.22/0.50  fof(f330,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | ~spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f329])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    spl3_32 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f378])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    spl3_34 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f705,plain,(
% 0.22/0.50    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_36 | ~spl3_46)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f698,f429])).
% 0.22/0.50  fof(f698,plain,(
% 0.22/0.50    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f696])).
% 0.22/0.50  fof(f696,plain,(
% 0.22/0.50    spl3_46 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl3_15 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f699,plain,(
% 0.22/0.50    spl3_46 | ~spl3_18 | ~spl3_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f413,f391,f144,f696])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    spl3_18 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    spl3_35 <=> ! [X9,X8,X10] : r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_18 | ~spl3_35)),
% 0.22/0.50    inference(superposition,[],[f392,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9))) ) | ~spl3_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f391])).
% 0.22/0.50  fof(f511,plain,(
% 0.22/0.50    spl3_3 | ~spl3_18 | ~spl3_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f297,f280,f144,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    spl3_29 <=> ! [X11,X13,X12] : r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    r1_xboole_0(sK0,sK2) | (~spl3_18 | ~spl3_29)),
% 0.22/0.50    inference(superposition,[],[f281,f146])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13)) ) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f280])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    spl3_36 | ~spl3_9 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f107,f80,f66,f428])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl3_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) ) | (~spl3_9 | ~spl3_12)),
% 0.22/0.50    inference(superposition,[],[f81,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    spl3_35 | ~spl3_7 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f122,f111,f56,f391])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl3_7 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_14 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X8,k4_xboole_0(X9,X10)),k3_xboole_0(X8,X9))) ) | (~spl3_7 | ~spl3_14)),
% 0.22/0.50    inference(superposition,[],[f57,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f380,plain,(
% 0.22/0.50    spl3_34 | ~spl3_8 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f108,f80,f62,f378])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl3_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl3_8 | ~spl3_12)),
% 0.22/0.50    inference(superposition,[],[f81,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f331,plain,(
% 0.22/0.50    spl3_32 | ~spl3_6 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f88,f66,f52,f329])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl3_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) ) | (~spl3_6 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f53,f67])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f52])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    spl3_29 | ~spl3_5 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f123,f111,f48,f280])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_5 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X12,X13,X11] : (r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X12,X13)),X13)) ) | (~spl3_5 | ~spl3_14)),
% 0.22/0.50    inference(superposition,[],[f49,f112])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl3_20 | ~spl3_4 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f56,f44,f165])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_4 | ~spl3_7)),
% 0.22/0.50    inference(superposition,[],[f57,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f44])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl3_18 | ~spl3_1 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f66,f30,f144])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f32,f67])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f30])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~spl3_15 | spl3_2 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f70,f35,f125])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_2 | ~spl3_10)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f37,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f35])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f111])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f80])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f74])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f70])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f66])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f62])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f56])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f48])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f18,f39,f35])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15880)------------------------------
% 0.22/0.50  % (15880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15880)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15880)Memory used [KB]: 6524
% 0.22/0.50  % (15880)Time elapsed: 0.056 s
% 0.22/0.50  % (15880)------------------------------
% 0.22/0.50  % (15880)------------------------------
% 0.22/0.51  % (15874)Success in time 0.136 s
%------------------------------------------------------------------------------

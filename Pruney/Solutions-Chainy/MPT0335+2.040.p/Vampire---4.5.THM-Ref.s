%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:20 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 234 expanded)
%              Number of leaves         :   28 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  230 ( 458 expanded)
%              Number of equality atoms :   84 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1006,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f97,f131,f161,f184,f235,f861,f899,f942,f1005])).

fof(f1005,plain,
    ( ~ spl5_12
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f1004])).

fof(f1004,plain,
    ( $false
    | ~ spl5_12
    | spl5_27 ),
    inference(trivial_inequality_removal,[],[f1003])).

fof(f1003,plain,
    ( sK0 != sK0
    | ~ spl5_12
    | spl5_27 ),
    inference(superposition,[],[f941,f433])).

fof(f433,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f430,f114])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f90,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
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

fof(f430,plain,
    ( ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl5_12 ),
    inference(resolution,[],[f429,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f38,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f429,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_12 ),
    inference(resolution,[],[f427,f156])).

fof(f156,plain,
    ( ! [X5] : r1_xboole_0(k1_xboole_0,X5)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_12
  <=> ! [X5] : r1_xboole_0(k1_xboole_0,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f427,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f113,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f113,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X4,X5),X6)
      | ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f33,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f941,plain,
    ( sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl5_27
  <=> sK0 = k5_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f942,plain,
    ( ~ spl5_27
    | spl5_24
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f911,f896,f858,f939])).

fof(f858,plain,
    ( spl5_24
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f896,plain,
    ( spl5_25
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f911,plain,
    ( sK0 != k5_xboole_0(sK0,k1_xboole_0)
    | spl5_24
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f860,f898])).

fof(f898,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f896])).

fof(f860,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f858])).

fof(f899,plain,
    ( spl5_25
    | spl5_8
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f879,f94,f76,f128,f896])).

fof(f128,plain,
    ( spl5_8
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f76,plain,
    ( spl5_3
  <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f94,plain,
    ( spl5_5
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f879,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(resolution,[],[f840,f275])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK1,sK2))
        | k3_xboole_0(sK1,sK2) = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_3 ),
    inference(superposition,[],[f58,f78])).

fof(f78,plain,
    ( k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f39,f51,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f840,plain,
    ( ! [X17] : r1_tarski(k3_xboole_0(sK0,X17),k3_xboole_0(sK1,X17))
    | ~ spl5_5 ),
    inference(superposition,[],[f85,f195])).

fof(f195,plain,
    ( ! [X14] : k3_xboole_0(sK0,k3_xboole_0(sK1,X14)) = k3_xboole_0(sK0,X14)
    | ~ spl5_5 ),
    inference(superposition,[],[f47,f96])).

fof(f96,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f861,plain,
    ( ~ spl5_24
    | ~ spl5_5
    | spl5_17 ),
    inference(avatar_split_clause,[],[f821,f232,f94,f858])).

fof(f232,plain,
    ( spl5_17
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f821,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl5_5
    | spl5_17 ),
    inference(backward_demodulation,[],[f234,f195])).

fof(f234,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f232])).

fof(f235,plain,
    ( ~ spl5_17
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f230,f76,f71,f232])).

fof(f71,plain,
    ( spl5_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f230,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f227,f78])).

fof(f227,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_2 ),
    inference(resolution,[],[f61,f73])).

fof(f73,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) != X0 ) ),
    inference(definition_unfolding,[],[f45,f32,f51])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f184,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f183,f158])).

fof(f158,plain,
    ( spl5_13
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f183,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f172,f90])).

fof(f172,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f60,f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f32])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f161,plain,
    ( spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f139,f158,f155])).

fof(f139,plain,(
    ! [X5] :
      ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f55,f90])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f131,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f126,f76,f66,f128])).

fof(f66,plain,
    ( spl5_1
  <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f126,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK0,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(superposition,[],[f68,f78])).

fof(f68,plain,
    ( k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f97,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f89,f81,f94])).

fof(f81,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f36,f83])).

fof(f83,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f81])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f53,f76])).

fof(f53,plain,(
    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f24,f51])).

fof(f24,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f52,f66])).

fof(f52,plain,(
    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f26,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (6021)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (6038)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (6026)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.53  % (6044)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.53  % (6029)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.30/0.53  % (6047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.53  % (6035)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.54  % (6045)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (6048)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.54  % (6036)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.54  % (6023)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (6027)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.54  % (6024)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  % (6022)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (6025)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (6040)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.55  % (6039)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.55  % (6049)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.55  % (6041)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.55  % (6020)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.55  % (6037)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.55  % (6037)Refutation not found, incomplete strategy% (6037)------------------------------
% 1.30/0.55  % (6037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (6037)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (6037)Memory used [KB]: 10618
% 1.30/0.55  % (6037)Time elapsed: 0.140 s
% 1.30/0.55  % (6037)------------------------------
% 1.30/0.55  % (6037)------------------------------
% 1.45/0.55  % (6031)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (6030)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (6032)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  % (6042)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  % (6028)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.56  % (6033)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.57  % (6043)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.57  % (6046)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (6034)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.62  % (6036)Refutation found. Thanks to Tanya!
% 1.45/0.62  % SZS status Theorem for theBenchmark
% 1.45/0.62  % SZS output start Proof for theBenchmark
% 1.45/0.62  fof(f1006,plain,(
% 1.45/0.62    $false),
% 1.45/0.62    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f97,f131,f161,f184,f235,f861,f899,f942,f1005])).
% 1.45/0.62  fof(f1005,plain,(
% 1.45/0.62    ~spl5_12 | spl5_27),
% 1.45/0.62    inference(avatar_contradiction_clause,[],[f1004])).
% 1.45/0.62  fof(f1004,plain,(
% 1.45/0.62    $false | (~spl5_12 | spl5_27)),
% 1.45/0.62    inference(trivial_inequality_removal,[],[f1003])).
% 1.45/0.62  fof(f1003,plain,(
% 1.45/0.62    sK0 != sK0 | (~spl5_12 | spl5_27)),
% 1.45/0.62    inference(superposition,[],[f941,f433])).
% 1.45/0.62  fof(f433,plain,(
% 1.45/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_12),
% 1.45/0.62    inference(forward_demodulation,[],[f430,f114])).
% 1.45/0.62  fof(f114,plain,(
% 1.45/0.62    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.45/0.62    inference(superposition,[],[f90,f30])).
% 1.45/0.62  fof(f30,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f1])).
% 1.45/0.62  fof(f1,axiom,(
% 1.45/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.45/0.62  fof(f90,plain,(
% 1.45/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.62    inference(resolution,[],[f36,f27])).
% 1.45/0.62  fof(f27,plain,(
% 1.45/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f8])).
% 1.45/0.62  fof(f8,axiom,(
% 1.45/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.62  fof(f36,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.45/0.62    inference(cnf_transformation,[],[f22])).
% 1.45/0.62  fof(f22,plain,(
% 1.45/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.45/0.62    inference(ennf_transformation,[],[f7])).
% 1.45/0.62  fof(f7,axiom,(
% 1.45/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.45/0.62  fof(f430,plain,(
% 1.45/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) ) | ~spl5_12),
% 1.45/0.62    inference(resolution,[],[f429,f54])).
% 1.45/0.62  fof(f54,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.45/0.62    inference(definition_unfolding,[],[f38,f32])).
% 1.45/0.62  fof(f32,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.62    inference(cnf_transformation,[],[f4])).
% 1.45/0.62  fof(f4,axiom,(
% 1.45/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.62  fof(f38,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f9])).
% 1.45/0.62  fof(f9,axiom,(
% 1.45/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.45/0.62  fof(f429,plain,(
% 1.45/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_12),
% 1.45/0.62    inference(resolution,[],[f427,f156])).
% 1.45/0.62  fof(f156,plain,(
% 1.45/0.62    ( ! [X5] : (r1_xboole_0(k1_xboole_0,X5)) ) | ~spl5_12),
% 1.45/0.62    inference(avatar_component_clause,[],[f155])).
% 1.45/0.62  fof(f155,plain,(
% 1.45/0.62    spl5_12 <=> ! [X5] : r1_xboole_0(k1_xboole_0,X5)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.45/0.62  fof(f427,plain,(
% 1.45/0.62    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)) )),
% 1.45/0.62    inference(duplicate_literal_removal,[],[f425])).
% 1.45/0.62  fof(f425,plain,(
% 1.45/0.62    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.45/0.62    inference(resolution,[],[f113,f35])).
% 1.45/0.62  fof(f35,plain,(
% 1.45/0.62    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f21])).
% 1.45/0.62  fof(f21,plain,(
% 1.45/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.62    inference(ennf_transformation,[],[f18])).
% 1.45/0.62  fof(f18,plain,(
% 1.45/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.62    inference(rectify,[],[f2])).
% 1.45/0.62  fof(f2,axiom,(
% 1.45/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.62  fof(f113,plain,(
% 1.45/0.62    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X4,X5),X6) | ~r1_xboole_0(X5,X6) | r1_xboole_0(X4,X5)) )),
% 1.45/0.62    inference(resolution,[],[f33,f35])).
% 1.45/0.62  fof(f33,plain,(
% 1.45/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f21])).
% 1.45/0.62  fof(f941,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k1_xboole_0) | spl5_27),
% 1.45/0.62    inference(avatar_component_clause,[],[f939])).
% 1.45/0.62  fof(f939,plain,(
% 1.45/0.62    spl5_27 <=> sK0 = k5_xboole_0(sK0,k1_xboole_0)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.45/0.62  fof(f942,plain,(
% 1.45/0.62    ~spl5_27 | spl5_24 | ~spl5_25),
% 1.45/0.62    inference(avatar_split_clause,[],[f911,f896,f858,f939])).
% 1.45/0.62  fof(f858,plain,(
% 1.45/0.62    spl5_24 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.45/0.62  fof(f896,plain,(
% 1.45/0.62    spl5_25 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.45/0.62  fof(f911,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k1_xboole_0) | (spl5_24 | ~spl5_25)),
% 1.45/0.62    inference(backward_demodulation,[],[f860,f898])).
% 1.45/0.62  fof(f898,plain,(
% 1.45/0.62    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl5_25),
% 1.45/0.62    inference(avatar_component_clause,[],[f896])).
% 1.45/0.62  fof(f860,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | spl5_24),
% 1.45/0.62    inference(avatar_component_clause,[],[f858])).
% 1.45/0.62  fof(f899,plain,(
% 1.45/0.62    spl5_25 | spl5_8 | ~spl5_3 | ~spl5_5),
% 1.45/0.62    inference(avatar_split_clause,[],[f879,f94,f76,f128,f896])).
% 1.45/0.62  fof(f128,plain,(
% 1.45/0.62    spl5_8 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.45/0.62  fof(f76,plain,(
% 1.45/0.62    spl5_3 <=> k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.45/0.62  fof(f94,plain,(
% 1.45/0.62    spl5_5 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.45/0.62  fof(f879,plain,(
% 1.45/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl5_3 | ~spl5_5)),
% 1.45/0.62    inference(resolution,[],[f840,f275])).
% 1.45/0.62  fof(f275,plain,(
% 1.45/0.62    ( ! [X0] : (~r1_tarski(X0,k3_xboole_0(sK1,sK2)) | k3_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) ) | ~spl5_3),
% 1.45/0.62    inference(superposition,[],[f58,f78])).
% 1.45/0.62  fof(f78,plain,(
% 1.45/0.62    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) | ~spl5_3),
% 1.45/0.62    inference(avatar_component_clause,[],[f76])).
% 1.45/0.62  fof(f58,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.45/0.62    inference(definition_unfolding,[],[f39,f51,f51])).
% 1.45/0.62  fof(f51,plain,(
% 1.45/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.62    inference(definition_unfolding,[],[f28,f50])).
% 1.45/0.62  fof(f50,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.45/0.62    inference(definition_unfolding,[],[f31,f49])).
% 1.45/0.62  fof(f49,plain,(
% 1.45/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.45/0.62    inference(definition_unfolding,[],[f46,f48])).
% 1.45/0.62  fof(f48,plain,(
% 1.45/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f13])).
% 1.45/0.62  fof(f13,axiom,(
% 1.45/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.62  fof(f46,plain,(
% 1.45/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f12])).
% 1.45/0.62  fof(f12,axiom,(
% 1.45/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.62  fof(f31,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f11])).
% 1.45/0.62  fof(f11,axiom,(
% 1.45/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.62  fof(f28,plain,(
% 1.45/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f10])).
% 1.45/0.62  fof(f10,axiom,(
% 1.45/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.62  fof(f39,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.45/0.62    inference(cnf_transformation,[],[f14])).
% 1.45/0.62  fof(f14,axiom,(
% 1.45/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.45/0.62  fof(f840,plain,(
% 1.45/0.62    ( ! [X17] : (r1_tarski(k3_xboole_0(sK0,X17),k3_xboole_0(sK1,X17))) ) | ~spl5_5),
% 1.45/0.62    inference(superposition,[],[f85,f195])).
% 1.45/0.62  fof(f195,plain,(
% 1.45/0.62    ( ! [X14] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X14)) = k3_xboole_0(sK0,X14)) ) | ~spl5_5),
% 1.45/0.62    inference(superposition,[],[f47,f96])).
% 1.45/0.62  fof(f96,plain,(
% 1.45/0.62    sK0 = k3_xboole_0(sK0,sK1) | ~spl5_5),
% 1.45/0.62    inference(avatar_component_clause,[],[f94])).
% 1.45/0.62  fof(f47,plain,(
% 1.45/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.45/0.62    inference(cnf_transformation,[],[f5])).
% 1.45/0.62  fof(f5,axiom,(
% 1.45/0.62    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.45/0.62  fof(f85,plain,(
% 1.45/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.45/0.62    inference(superposition,[],[f29,f30])).
% 1.45/0.62  fof(f29,plain,(
% 1.45/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f6])).
% 1.45/0.62  fof(f6,axiom,(
% 1.45/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.45/0.62  fof(f861,plain,(
% 1.45/0.62    ~spl5_24 | ~spl5_5 | spl5_17),
% 1.45/0.62    inference(avatar_split_clause,[],[f821,f232,f94,f858])).
% 1.45/0.62  fof(f232,plain,(
% 1.45/0.62    spl5_17 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.45/0.62  fof(f821,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | (~spl5_5 | spl5_17)),
% 1.45/0.62    inference(backward_demodulation,[],[f234,f195])).
% 1.45/0.62  fof(f234,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | spl5_17),
% 1.45/0.62    inference(avatar_component_clause,[],[f232])).
% 1.45/0.62  fof(f235,plain,(
% 1.45/0.62    ~spl5_17 | ~spl5_2 | ~spl5_3),
% 1.45/0.62    inference(avatar_split_clause,[],[f230,f76,f71,f232])).
% 1.45/0.62  fof(f71,plain,(
% 1.45/0.62    spl5_2 <=> r2_hidden(sK3,sK0)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.45/0.62  fof(f230,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | (~spl5_2 | ~spl5_3)),
% 1.45/0.62    inference(forward_demodulation,[],[f227,f78])).
% 1.45/0.62  fof(f227,plain,(
% 1.45/0.62    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK3,sK3,sK3,sK3,sK3))) | ~spl5_2),
% 1.45/0.62    inference(resolution,[],[f61,f73])).
% 1.45/0.62  fof(f73,plain,(
% 1.45/0.62    r2_hidden(sK3,sK0) | ~spl5_2),
% 1.45/0.62    inference(avatar_component_clause,[],[f71])).
% 1.45/0.62  fof(f61,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1))) != X0) )),
% 1.45/0.62    inference(definition_unfolding,[],[f45,f32,f51])).
% 1.45/0.62  fof(f45,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.45/0.62    inference(cnf_transformation,[],[f15])).
% 1.45/0.62  fof(f15,axiom,(
% 1.45/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.45/0.62  fof(f184,plain,(
% 1.45/0.62    spl5_13),
% 1.45/0.62    inference(avatar_split_clause,[],[f183,f158])).
% 1.45/0.62  fof(f158,plain,(
% 1.45/0.62    spl5_13 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.45/0.62  fof(f183,plain,(
% 1.45/0.62    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.62    inference(forward_demodulation,[],[f172,f90])).
% 1.45/0.62  fof(f172,plain,(
% 1.45/0.62    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.45/0.62    inference(resolution,[],[f60,f27])).
% 1.45/0.62  fof(f60,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.62    inference(definition_unfolding,[],[f42,f32])).
% 1.45/0.62  fof(f42,plain,(
% 1.45/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.45/0.62    inference(cnf_transformation,[],[f3])).
% 1.45/0.62  fof(f3,axiom,(
% 1.45/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.62  fof(f161,plain,(
% 1.45/0.62    spl5_12 | ~spl5_13),
% 1.45/0.62    inference(avatar_split_clause,[],[f139,f158,f155])).
% 1.45/0.62  fof(f139,plain,(
% 1.45/0.62    ( ! [X5] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,X5)) )),
% 1.45/0.62    inference(superposition,[],[f55,f90])).
% 1.45/0.62  fof(f55,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.62    inference(definition_unfolding,[],[f37,f32])).
% 1.45/0.62  fof(f37,plain,(
% 1.45/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.45/0.62    inference(cnf_transformation,[],[f9])).
% 1.45/0.62  fof(f131,plain,(
% 1.45/0.62    ~spl5_8 | spl5_1 | ~spl5_3),
% 1.45/0.62    inference(avatar_split_clause,[],[f126,f76,f66,f128])).
% 1.45/0.62  fof(f66,plain,(
% 1.45/0.62    spl5_1 <=> k3_xboole_0(sK0,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.45/0.62  fof(f126,plain,(
% 1.45/0.62    k3_xboole_0(sK1,sK2) != k3_xboole_0(sK0,sK2) | (spl5_1 | ~spl5_3)),
% 1.45/0.62    inference(superposition,[],[f68,f78])).
% 1.45/0.62  fof(f68,plain,(
% 1.45/0.62    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) | spl5_1),
% 1.45/0.62    inference(avatar_component_clause,[],[f66])).
% 1.45/0.62  fof(f97,plain,(
% 1.45/0.62    spl5_5 | ~spl5_4),
% 1.45/0.62    inference(avatar_split_clause,[],[f89,f81,f94])).
% 1.45/0.62  fof(f81,plain,(
% 1.45/0.62    spl5_4 <=> r1_tarski(sK0,sK1)),
% 1.45/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.45/0.62  fof(f89,plain,(
% 1.45/0.62    sK0 = k3_xboole_0(sK0,sK1) | ~spl5_4),
% 1.45/0.62    inference(resolution,[],[f36,f83])).
% 1.45/0.62  fof(f83,plain,(
% 1.45/0.62    r1_tarski(sK0,sK1) | ~spl5_4),
% 1.45/0.62    inference(avatar_component_clause,[],[f81])).
% 1.45/0.62  fof(f84,plain,(
% 1.45/0.62    spl5_4),
% 1.45/0.62    inference(avatar_split_clause,[],[f23,f81])).
% 1.45/0.62  fof(f23,plain,(
% 1.45/0.62    r1_tarski(sK0,sK1)),
% 1.45/0.62    inference(cnf_transformation,[],[f20])).
% 1.45/0.62  fof(f20,plain,(
% 1.45/0.62    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.45/0.62    inference(flattening,[],[f19])).
% 1.45/0.62  fof(f19,plain,(
% 1.45/0.62    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.45/0.62    inference(ennf_transformation,[],[f17])).
% 1.45/0.62  fof(f17,negated_conjecture,(
% 1.45/0.62    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.45/0.62    inference(negated_conjecture,[],[f16])).
% 1.45/0.62  fof(f16,conjecture,(
% 1.45/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.45/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.45/0.62  fof(f79,plain,(
% 1.45/0.62    spl5_3),
% 1.45/0.62    inference(avatar_split_clause,[],[f53,f76])).
% 1.45/0.62  fof(f53,plain,(
% 1.45/0.62    k3_xboole_0(sK1,sK2) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.45/0.62    inference(definition_unfolding,[],[f24,f51])).
% 1.45/0.62  fof(f24,plain,(
% 1.45/0.62    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 1.45/0.62    inference(cnf_transformation,[],[f20])).
% 1.45/0.62  fof(f74,plain,(
% 1.45/0.62    spl5_2),
% 1.45/0.62    inference(avatar_split_clause,[],[f25,f71])).
% 1.45/0.62  fof(f25,plain,(
% 1.45/0.62    r2_hidden(sK3,sK0)),
% 1.45/0.62    inference(cnf_transformation,[],[f20])).
% 1.45/0.62  fof(f69,plain,(
% 1.45/0.62    ~spl5_1),
% 1.45/0.62    inference(avatar_split_clause,[],[f52,f66])).
% 1.45/0.62  fof(f52,plain,(
% 1.45/0.62    k3_xboole_0(sK0,sK2) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 1.45/0.62    inference(definition_unfolding,[],[f26,f51])).
% 1.45/0.62  fof(f26,plain,(
% 1.45/0.62    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.45/0.62    inference(cnf_transformation,[],[f20])).
% 1.45/0.62  % SZS output end Proof for theBenchmark
% 1.45/0.62  % (6036)------------------------------
% 1.45/0.62  % (6036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.62  % (6036)Termination reason: Refutation
% 1.45/0.62  
% 1.45/0.62  % (6036)Memory used [KB]: 11513
% 1.45/0.62  % (6036)Time elapsed: 0.209 s
% 1.45/0.62  % (6036)------------------------------
% 1.45/0.62  % (6036)------------------------------
% 1.45/0.62  % (6019)Success in time 0.256 s
%------------------------------------------------------------------------------

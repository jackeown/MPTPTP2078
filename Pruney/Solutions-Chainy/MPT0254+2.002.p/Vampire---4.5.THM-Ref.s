%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:13 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 340 expanded)
%              Number of leaves         :   33 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 ( 537 expanded)
%              Number of equality atoms :  101 ( 291 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f609,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f115,f127,f376,f398,f409,f443,f464,f516,f523,f556,f597,f608])).

fof(f608,plain,(
    ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f596,f596,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X1),X0)
      | ~ r1_tarski(k1_zfmisc_1(X0),X1) ) ),
    inference(resolution,[],[f93,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_zfmisc_1(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f596,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl3_18
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f597,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f592,f553,f513,f112,f594])).

fof(f112,plain,
    ( spl3_4
  <=> k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f513,plain,
    ( spl3_15
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f553,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f592,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f565,f114])).

fof(f114,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f565,plain,
    ( r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(superposition,[],[f515,f555])).

fof(f555,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f553])).

fof(f515,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f513])).

fof(f556,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f551,f520,f78,f553])).

fof(f78,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f520,plain,
    ( spl3_16
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f551,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f533,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f533,plain,
    ( k3_tarski(k1_xboole_0) = sK0
    | ~ spl3_16 ),
    inference(superposition,[],[f346,f522])).

fof(f522,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f520])).

fof(f346,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f345,f288])).

fof(f288,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f283,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f283,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f67,f268])).

fof(f268,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f255,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f255,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f49,f47,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f47])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f345,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_enumset1(X0,X0,X0,X0)) ),
    inference(forward_demodulation,[],[f344,f296])).

fof(f296,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f268,f288])).

fof(f344,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0)) ),
    inference(forward_demodulation,[],[f314,f84])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f314,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(superposition,[],[f69,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f64,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f523,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f517,f513,f520])).

fof(f517,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f515,f43])).

fof(f516,plain,
    ( spl3_15
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f511,f461,f440,f513])).

fof(f440,plain,
    ( spl3_13
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f461,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f511,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f459,f463])).

fof(f463,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f461])).

fof(f459,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f451,f442])).

fof(f442,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f440])).

fof(f451,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f72,f442])).

fof(f464,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f456,f440,f393,f461])).

fof(f393,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f456,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f455,f395])).

fof(f395,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f393])).

fof(f455,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f454,f168])).

fof(f168,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f150,f145])).

fof(f145,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f129,f84])).

fof(f129,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f51,f45])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f150,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f145,f52])).

fof(f454,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f448,f442])).

fof(f448,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_13 ),
    inference(superposition,[],[f69,f442])).

fof(f443,plain,
    ( spl3_13
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f420,f406,f440])).

fof(f406,plain,
    ( spl3_9
  <=> k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f420,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f413,f145])).

fof(f413,plain,
    ( k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_9 ),
    inference(superposition,[],[f67,f408])).

fof(f408,plain,
    ( k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f406])).

fof(f409,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f390,f371,f406])).

fof(f371,plain,
    ( spl3_6
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f390,plain,
    ( k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f384,f44])).

fof(f384,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f145,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f371])).

fof(f398,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f380,f371,f393])).

fof(f380,plain,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl3_6 ),
    inference(superposition,[],[f69,f373])).

fof(f376,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f264,f124,f371])).

fof(f124,plain,
    ( spl3_5
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f264,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl3_5 ),
    inference(superposition,[],[f126,f71])).

fof(f126,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f122,f124])).

fof(f122,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(forward_demodulation,[],[f68,f52])).

fof(f68,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f38,f64,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f115,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f70,f112])).

fof(f70,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f42,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f53,f78])).

fof(f53,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (22710)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (22726)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (22718)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (22708)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.59  % (22718)Refutation not found, incomplete strategy% (22718)------------------------------
% 0.22/0.59  % (22718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (22718)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (22718)Memory used [KB]: 1663
% 0.22/0.59  % (22718)Time elapsed: 0.148 s
% 0.22/0.59  % (22718)------------------------------
% 0.22/0.59  % (22718)------------------------------
% 0.22/0.59  % (22716)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.59  % (22709)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.60  % (22706)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.60  % (22705)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (22704)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.60  % (22727)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.60  % (22732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.61  % (22723)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.62/0.61  % (22719)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.62/0.62  % (22716)Refutation not found, incomplete strategy% (22716)------------------------------
% 1.62/0.62  % (22716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.62  % (22716)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.62  
% 1.62/0.62  % (22716)Memory used [KB]: 10618
% 1.62/0.62  % (22716)Time elapsed: 0.167 s
% 1.62/0.62  % (22716)------------------------------
% 1.62/0.62  % (22716)------------------------------
% 1.62/0.62  % (22711)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.62/0.62  % (22707)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.62/0.62  % (22728)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.99/0.62  % (22731)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.99/0.63  % (22733)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.99/0.63  % (22733)Refutation not found, incomplete strategy% (22733)------------------------------
% 1.99/0.63  % (22733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.63  % (22733)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.63  
% 1.99/0.63  % (22733)Memory used [KB]: 1663
% 1.99/0.63  % (22733)Time elapsed: 0.003 s
% 1.99/0.63  % (22733)------------------------------
% 1.99/0.63  % (22733)------------------------------
% 1.99/0.63  % (22715)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.99/0.63  % (22721)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.99/0.63  % (22712)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.99/0.64  % (22717)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.99/0.64  % (22729)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.99/0.64  % (22720)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.99/0.64  % (22720)Refutation not found, incomplete strategy% (22720)------------------------------
% 1.99/0.64  % (22720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.64  % (22720)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.64  
% 1.99/0.64  % (22720)Memory used [KB]: 10618
% 1.99/0.64  % (22720)Time elapsed: 0.195 s
% 1.99/0.64  % (22720)------------------------------
% 1.99/0.64  % (22720)------------------------------
% 1.99/0.64  % (22725)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.99/0.64  % (22724)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.99/0.64  % (22722)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.99/0.65  % (22722)Refutation not found, incomplete strategy% (22722)------------------------------
% 1.99/0.65  % (22722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (22722)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.65  
% 1.99/0.65  % (22722)Memory used [KB]: 1663
% 1.99/0.65  % (22722)Time elapsed: 0.206 s
% 1.99/0.65  % (22722)------------------------------
% 1.99/0.65  % (22722)------------------------------
% 1.99/0.65  % (22713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.99/0.65  % (22714)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.99/0.65  % (22730)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.99/0.65  % (22730)Refutation not found, incomplete strategy% (22730)------------------------------
% 1.99/0.65  % (22730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.65  % (22730)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.65  
% 1.99/0.65  % (22730)Memory used [KB]: 6140
% 1.99/0.65  % (22730)Time elapsed: 0.216 s
% 1.99/0.65  % (22730)------------------------------
% 1.99/0.65  % (22730)------------------------------
% 1.99/0.66  % (22727)Refutation found. Thanks to Tanya!
% 1.99/0.66  % SZS status Theorem for theBenchmark
% 1.99/0.66  % SZS output start Proof for theBenchmark
% 1.99/0.66  fof(f609,plain,(
% 1.99/0.66    $false),
% 1.99/0.66    inference(avatar_sat_refutation,[],[f81,f115,f127,f376,f398,f409,f443,f464,f516,f523,f556,f597,f608])).
% 1.99/0.66  fof(f608,plain,(
% 1.99/0.66    ~spl3_18),
% 1.99/0.66    inference(avatar_contradiction_clause,[],[f603])).
% 1.99/0.66  fof(f603,plain,(
% 1.99/0.66    $false | ~spl3_18),
% 1.99/0.66    inference(unit_resulting_resolution,[],[f596,f596,f117])).
% 1.99/0.66  fof(f117,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r1_tarski(k1_zfmisc_1(X1),X0) | ~r1_tarski(k1_zfmisc_1(X0),X1)) )),
% 1.99/0.66    inference(resolution,[],[f93,f73])).
% 1.99/0.66  fof(f73,plain,(
% 1.99/0.66    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.99/0.66    inference(equality_resolution,[],[f56])).
% 1.99/0.66  fof(f56,plain,(
% 1.99/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.99/0.66    inference(cnf_transformation,[],[f35])).
% 1.99/0.66  fof(f35,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.99/0.66  fof(f34,plain,(
% 1.99/0.66    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f33,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(rectify,[],[f32])).
% 1.99/0.66  fof(f32,plain,(
% 1.99/0.66    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.99/0.66    inference(nnf_transformation,[],[f21])).
% 1.99/0.66  fof(f21,axiom,(
% 1.99/0.66    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.99/0.66  fof(f93,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r2_hidden(k1_zfmisc_1(X1),X0) | ~r1_tarski(X0,X1)) )),
% 1.99/0.66    inference(resolution,[],[f73,f63])).
% 1.99/0.66  fof(f63,plain,(
% 1.99/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f29])).
% 1.99/0.66  fof(f29,plain,(
% 1.99/0.66    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.99/0.66    inference(ennf_transformation,[],[f1])).
% 1.99/0.66  fof(f1,axiom,(
% 1.99/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.99/0.66  fof(f596,plain,(
% 1.99/0.66    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | ~spl3_18),
% 1.99/0.66    inference(avatar_component_clause,[],[f594])).
% 1.99/0.66  fof(f594,plain,(
% 1.99/0.66    spl3_18 <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.99/0.66  fof(f597,plain,(
% 1.99/0.66    spl3_18 | ~spl3_4 | ~spl3_15 | ~spl3_17),
% 1.99/0.66    inference(avatar_split_clause,[],[f592,f553,f513,f112,f594])).
% 1.99/0.66  fof(f112,plain,(
% 1.99/0.66    spl3_4 <=> k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.99/0.66  fof(f513,plain,(
% 1.99/0.66    spl3_15 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.99/0.66  fof(f553,plain,(
% 1.99/0.66    spl3_17 <=> k1_xboole_0 = sK0),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.99/0.66  fof(f592,plain,(
% 1.99/0.66    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (~spl3_4 | ~spl3_15 | ~spl3_17)),
% 1.99/0.66    inference(forward_demodulation,[],[f565,f114])).
% 1.99/0.66  fof(f114,plain,(
% 1.99/0.66    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_4),
% 1.99/0.66    inference(avatar_component_clause,[],[f112])).
% 1.99/0.66  fof(f565,plain,(
% 1.99/0.66    r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl3_15 | ~spl3_17)),
% 1.99/0.66    inference(superposition,[],[f515,f555])).
% 1.99/0.66  fof(f555,plain,(
% 1.99/0.66    k1_xboole_0 = sK0 | ~spl3_17),
% 1.99/0.66    inference(avatar_component_clause,[],[f553])).
% 1.99/0.66  fof(f515,plain,(
% 1.99/0.66    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | ~spl3_15),
% 1.99/0.66    inference(avatar_component_clause,[],[f513])).
% 1.99/0.66  fof(f556,plain,(
% 1.99/0.66    spl3_17 | ~spl3_1 | ~spl3_16),
% 1.99/0.66    inference(avatar_split_clause,[],[f551,f520,f78,f553])).
% 1.99/0.66  fof(f78,plain,(
% 1.99/0.66    spl3_1 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.99/0.66  fof(f520,plain,(
% 1.99/0.66    spl3_16 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.99/0.66  fof(f551,plain,(
% 1.99/0.66    k1_xboole_0 = sK0 | (~spl3_1 | ~spl3_16)),
% 1.99/0.66    inference(forward_demodulation,[],[f533,f80])).
% 1.99/0.66  fof(f80,plain,(
% 1.99/0.66    k1_xboole_0 = k3_tarski(k1_xboole_0) | ~spl3_1),
% 1.99/0.66    inference(avatar_component_clause,[],[f78])).
% 1.99/0.66  fof(f533,plain,(
% 1.99/0.66    k3_tarski(k1_xboole_0) = sK0 | ~spl3_16),
% 1.99/0.66    inference(superposition,[],[f346,f522])).
% 1.99/0.66  fof(f522,plain,(
% 1.99/0.66    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_16),
% 1.99/0.66    inference(avatar_component_clause,[],[f520])).
% 1.99/0.66  fof(f346,plain,(
% 1.99/0.66    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.99/0.66    inference(forward_demodulation,[],[f345,f288])).
% 1.99/0.66  fof(f288,plain,(
% 1.99/0.66    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.99/0.66    inference(forward_demodulation,[],[f283,f44])).
% 1.99/0.66  fof(f44,plain,(
% 1.99/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f10])).
% 1.99/0.66  fof(f10,axiom,(
% 1.99/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.99/0.66  fof(f283,plain,(
% 1.99/0.66    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0)) )),
% 1.99/0.66    inference(superposition,[],[f67,f268])).
% 1.99/0.66  fof(f268,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.99/0.66    inference(resolution,[],[f255,f43])).
% 1.99/0.66  fof(f43,plain,(
% 1.99/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.99/0.66    inference(cnf_transformation,[],[f28])).
% 1.99/0.66  fof(f28,plain,(
% 1.99/0.66    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.99/0.66    inference(ennf_transformation,[],[f8])).
% 1.99/0.66  fof(f8,axiom,(
% 1.99/0.66    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.99/0.66  fof(f255,plain,(
% 1.99/0.66    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 1.99/0.66    inference(superposition,[],[f72,f71])).
% 1.99/0.66  fof(f71,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f49,f47,f47])).
% 1.99/0.66  fof(f47,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f9])).
% 1.99/0.66  fof(f9,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.99/0.66  fof(f49,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f2])).
% 1.99/0.66  fof(f2,axiom,(
% 1.99/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.99/0.66  fof(f72,plain,(
% 1.99/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.99/0.66    inference(definition_unfolding,[],[f50,f47])).
% 1.99/0.66  fof(f50,plain,(
% 1.99/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f6])).
% 1.99/0.66  fof(f6,axiom,(
% 1.99/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.99/0.66  fof(f67,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f48,f47])).
% 1.99/0.66  fof(f48,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f5])).
% 1.99/0.66  fof(f5,axiom,(
% 1.99/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.99/0.66  fof(f345,plain,(
% 1.99/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_tarski(k2_enumset1(X0,X0,X0,X0))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f344,f296])).
% 1.99/0.66  fof(f296,plain,(
% 1.99/0.66    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.99/0.66    inference(superposition,[],[f268,f288])).
% 1.99/0.66  fof(f344,plain,(
% 1.99/0.66    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X0))) )),
% 1.99/0.66    inference(forward_demodulation,[],[f314,f84])).
% 1.99/0.66  fof(f84,plain,(
% 1.99/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.99/0.66    inference(superposition,[],[f52,f44])).
% 1.99/0.66  fof(f52,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f3])).
% 1.99/0.66  fof(f3,axiom,(
% 1.99/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.99/0.66  fof(f314,plain,(
% 1.99/0.66    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 1.99/0.66    inference(superposition,[],[f69,f45])).
% 1.99/0.66  fof(f45,plain,(
% 1.99/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f12])).
% 1.99/0.66  fof(f12,axiom,(
% 1.99/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.99/0.66  fof(f69,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f40,f64,f65])).
% 1.99/0.66  fof(f65,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.99/0.66    inference(definition_unfolding,[],[f54,f62])).
% 1.99/0.66  fof(f62,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f16])).
% 1.99/0.66  fof(f16,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.99/0.66  fof(f54,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f15])).
% 1.99/0.66  fof(f15,axiom,(
% 1.99/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.99/0.66  fof(f64,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.99/0.66    inference(definition_unfolding,[],[f39,f47])).
% 1.99/0.66  fof(f39,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f13])).
% 1.99/0.66  fof(f13,axiom,(
% 1.99/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.99/0.66  fof(f40,plain,(
% 1.99/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f22])).
% 1.99/0.66  fof(f22,axiom,(
% 1.99/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.99/0.66  fof(f523,plain,(
% 1.99/0.66    spl3_16 | ~spl3_15),
% 1.99/0.66    inference(avatar_split_clause,[],[f517,f513,f520])).
% 1.99/0.66  fof(f517,plain,(
% 1.99/0.66    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_15),
% 1.99/0.66    inference(resolution,[],[f515,f43])).
% 1.99/0.66  fof(f516,plain,(
% 1.99/0.66    spl3_15 | ~spl3_13 | ~spl3_14),
% 1.99/0.66    inference(avatar_split_clause,[],[f511,f461,f440,f513])).
% 1.99/0.66  fof(f440,plain,(
% 1.99/0.66    spl3_13 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.99/0.66  fof(f461,plain,(
% 1.99/0.66    spl3_14 <=> k1_xboole_0 = sK1),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.99/0.66  fof(f511,plain,(
% 1.99/0.66    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) | (~spl3_13 | ~spl3_14)),
% 1.99/0.66    inference(forward_demodulation,[],[f459,f463])).
% 1.99/0.66  fof(f463,plain,(
% 1.99/0.66    k1_xboole_0 = sK1 | ~spl3_14),
% 1.99/0.66    inference(avatar_component_clause,[],[f461])).
% 1.99/0.66  fof(f459,plain,(
% 1.99/0.66    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl3_13),
% 1.99/0.66    inference(forward_demodulation,[],[f451,f442])).
% 1.99/0.66  fof(f442,plain,(
% 1.99/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_13),
% 1.99/0.66    inference(avatar_component_clause,[],[f440])).
% 1.99/0.66  fof(f451,plain,(
% 1.99/0.66    r1_tarski(k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) | ~spl3_13),
% 1.99/0.66    inference(superposition,[],[f72,f442])).
% 1.99/0.66  fof(f464,plain,(
% 1.99/0.66    spl3_14 | ~spl3_7 | ~spl3_13),
% 1.99/0.66    inference(avatar_split_clause,[],[f456,f440,f393,f461])).
% 1.99/0.66  fof(f393,plain,(
% 1.99/0.66    spl3_7 <=> k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.99/0.66  fof(f456,plain,(
% 1.99/0.66    k1_xboole_0 = sK1 | (~spl3_7 | ~spl3_13)),
% 1.99/0.66    inference(forward_demodulation,[],[f455,f395])).
% 1.99/0.66  fof(f395,plain,(
% 1.99/0.66    k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_7),
% 1.99/0.66    inference(avatar_component_clause,[],[f393])).
% 1.99/0.66  fof(f455,plain,(
% 1.99/0.66    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_13),
% 1.99/0.66    inference(forward_demodulation,[],[f454,f168])).
% 1.99/0.66  fof(f168,plain,(
% 1.99/0.66    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 1.99/0.66    inference(superposition,[],[f150,f145])).
% 1.99/0.66  fof(f145,plain,(
% 1.99/0.66    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.99/0.66    inference(forward_demodulation,[],[f129,f84])).
% 1.99/0.66  fof(f129,plain,(
% 1.99/0.66    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.99/0.66    inference(superposition,[],[f51,f45])).
% 1.99/0.66  fof(f51,plain,(
% 1.99/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.99/0.66    inference(cnf_transformation,[],[f11])).
% 1.99/0.66  fof(f11,axiom,(
% 1.99/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.99/0.66  fof(f150,plain,(
% 1.99/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.99/0.66    inference(superposition,[],[f145,f52])).
% 1.99/0.66  fof(f454,plain,(
% 1.99/0.66    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_13),
% 1.99/0.66    inference(forward_demodulation,[],[f448,f442])).
% 1.99/0.66  fof(f448,plain,(
% 1.99/0.66    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_13),
% 1.99/0.66    inference(superposition,[],[f69,f442])).
% 1.99/0.66  fof(f443,plain,(
% 1.99/0.66    spl3_13 | ~spl3_9),
% 1.99/0.66    inference(avatar_split_clause,[],[f420,f406,f440])).
% 1.99/0.66  fof(f406,plain,(
% 1.99/0.66    spl3_9 <=> k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.99/0.66  fof(f420,plain,(
% 1.99/0.66    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_9),
% 1.99/0.66    inference(forward_demodulation,[],[f413,f145])).
% 1.99/0.66  fof(f413,plain,(
% 1.99/0.66    k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_9),
% 1.99/0.66    inference(superposition,[],[f67,f408])).
% 1.99/0.66  fof(f408,plain,(
% 1.99/0.66    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_9),
% 1.99/0.66    inference(avatar_component_clause,[],[f406])).
% 1.99/0.66  fof(f409,plain,(
% 1.99/0.66    spl3_9 | ~spl3_6),
% 1.99/0.66    inference(avatar_split_clause,[],[f390,f371,f406])).
% 1.99/0.66  fof(f371,plain,(
% 1.99/0.66    spl3_6 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.99/0.66  fof(f390,plain,(
% 1.99/0.66    k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_6),
% 1.99/0.66    inference(forward_demodulation,[],[f384,f44])).
% 1.99/0.66  fof(f384,plain,(
% 1.99/0.66    k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_6),
% 1.99/0.66    inference(superposition,[],[f145,f373])).
% 1.99/0.66  fof(f373,plain,(
% 1.99/0.66    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl3_6),
% 1.99/0.66    inference(avatar_component_clause,[],[f371])).
% 1.99/0.66  fof(f398,plain,(
% 1.99/0.66    spl3_7 | ~spl3_6),
% 1.99/0.66    inference(avatar_split_clause,[],[f380,f371,f393])).
% 1.99/0.66  fof(f380,plain,(
% 1.99/0.66    k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl3_6),
% 1.99/0.66    inference(superposition,[],[f69,f373])).
% 1.99/0.66  fof(f376,plain,(
% 1.99/0.66    spl3_6 | ~spl3_5),
% 1.99/0.66    inference(avatar_split_clause,[],[f264,f124,f371])).
% 1.99/0.66  fof(f124,plain,(
% 1.99/0.66    spl3_5 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.99/0.66  fof(f264,plain,(
% 1.99/0.66    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | ~spl3_5),
% 1.99/0.66    inference(superposition,[],[f126,f71])).
% 1.99/0.66  fof(f126,plain,(
% 1.99/0.66    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl3_5),
% 1.99/0.66    inference(avatar_component_clause,[],[f124])).
% 1.99/0.66  fof(f127,plain,(
% 1.99/0.66    spl3_5),
% 1.99/0.66    inference(avatar_split_clause,[],[f122,f124])).
% 1.99/0.66  fof(f122,plain,(
% 1.99/0.66    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.99/0.66    inference(forward_demodulation,[],[f68,f52])).
% 1.99/0.66  fof(f68,plain,(
% 1.99/0.66    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.99/0.66    inference(definition_unfolding,[],[f38,f64,f66])).
% 1.99/0.66  fof(f66,plain,(
% 1.99/0.66    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.99/0.66    inference(definition_unfolding,[],[f41,f65])).
% 1.99/0.66  fof(f41,plain,(
% 1.99/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/0.66    inference(cnf_transformation,[],[f14])).
% 1.99/0.66  fof(f14,axiom,(
% 1.99/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.99/0.66  fof(f38,plain,(
% 1.99/0.66    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.99/0.66    inference(cnf_transformation,[],[f31])).
% 1.99/0.66  fof(f31,plain,(
% 1.99/0.66    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.99/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f30])).
% 1.99/0.66  fof(f30,plain,(
% 1.99/0.66    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.99/0.66    introduced(choice_axiom,[])).
% 1.99/0.66  fof(f27,plain,(
% 1.99/0.66    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.99/0.66    inference(ennf_transformation,[],[f26])).
% 1.99/0.66  fof(f26,negated_conjecture,(
% 1.99/0.66    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.99/0.66    inference(negated_conjecture,[],[f25])).
% 1.99/0.66  fof(f25,conjecture,(
% 1.99/0.66    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.99/0.66  fof(f115,plain,(
% 1.99/0.66    spl3_4),
% 1.99/0.66    inference(avatar_split_clause,[],[f70,f112])).
% 1.99/0.66  fof(f70,plain,(
% 1.99/0.66    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.99/0.66    inference(definition_unfolding,[],[f42,f66])).
% 1.99/0.66  fof(f42,plain,(
% 1.99/0.66    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.99/0.66    inference(cnf_transformation,[],[f23])).
% 1.99/0.66  fof(f23,axiom,(
% 1.99/0.66    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.99/0.66  fof(f81,plain,(
% 1.99/0.66    spl3_1),
% 1.99/0.66    inference(avatar_split_clause,[],[f53,f78])).
% 1.99/0.66  fof(f53,plain,(
% 1.99/0.66    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.99/0.66    inference(cnf_transformation,[],[f24])).
% 1.99/0.66  fof(f24,axiom,(
% 1.99/0.66    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.99/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.99/0.66  % SZS output end Proof for theBenchmark
% 1.99/0.66  % (22727)------------------------------
% 1.99/0.66  % (22727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.66  % (22727)Termination reason: Refutation
% 1.99/0.66  
% 1.99/0.66  % (22727)Memory used [KB]: 11129
% 1.99/0.66  % (22727)Time elapsed: 0.208 s
% 1.99/0.66  % (22727)------------------------------
% 1.99/0.66  % (22727)------------------------------
% 1.99/0.66  % (22703)Success in time 0.287 s
%------------------------------------------------------------------------------

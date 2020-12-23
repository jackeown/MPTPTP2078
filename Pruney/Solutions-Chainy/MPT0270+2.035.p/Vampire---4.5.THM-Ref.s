%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:01 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 482 expanded)
%              Number of leaves         :   19 ( 146 expanded)
%              Depth                    :   21
%              Number of atoms          :  273 (1435 expanded)
%              Number of equality atoms :   81 ( 431 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24681)Termination reason: Refutation not found, incomplete strategy

% (24681)Memory used [KB]: 10618
% (24681)Time elapsed: 0.157 s
% (24681)------------------------------
% (24681)------------------------------
fof(f367,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f100,f215,f362])).

fof(f362,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f360,f93])).

fof(f93,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f360,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f353,f243])).

fof(f243,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f74,f232])).

fof(f232,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    inference(resolution,[],[f229,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f229,plain,(
    ! [X8,X9] : ~ r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f228,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f228,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,X8)
      | ~ r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,X8)
      | ~ r2_hidden(X9,X8)
      | ~ r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0)) ) ),
    inference(superposition,[],[f61,f74])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f353,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f76,f325])).

fof(f325,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f295,f41])).

fof(f295,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f294,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f61,f96])).

fof(f96,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f45,f44,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f215,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f213])).

fof(f213,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_1
    | spl5_2 ),
    inference(superposition,[],[f126,f205])).

fof(f205,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | spl5_1 ),
    inference(backward_demodulation,[],[f74,f192])).

fof(f192,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | spl5_1 ),
    inference(superposition,[],[f177,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f177,plain,
    ( ! [X19] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X19)
    | spl5_1 ),
    inference(resolution,[],[f128,f124])).

fof(f124,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | spl5_1 ),
    inference(backward_demodulation,[],[f113,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(resolution,[],[f113,f41])).

fof(f113,plain,
    ( ! [X4] : ~ r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f111,f85])).

fof(f111,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | spl5_1 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | spl5_1 ),
    inference(superposition,[],[f61,f101])).

fof(f101,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(resolution,[],[f92,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = X0 ) ),
    inference(definition_unfolding,[],[f46,f44,f71])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f128,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = k3_xboole_0(X2,X3) )
    | spl5_1 ),
    inference(forward_demodulation,[],[f127,f116])).

fof(f127,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k1_xboole_0),X2)
        | k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(X2,X3) )
    | spl5_1 ),
    inference(forward_demodulation,[],[f117,f116])).

fof(f117,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X2)
        | k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(X2,X3) )
    | spl5_1 ),
    inference(resolution,[],[f113,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f126,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | spl5_1
    | spl5_2 ),
    inference(backward_demodulation,[],[f97,f116])).

fof(f97,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f100,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f99,f95,f91])).

fof(f99,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f73,f42])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f37,f71,f44,f71])).

fof(f37,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f98,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f72,f42])).

fof(f72,plain,
    ( r2_hidden(sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f38,f71,f44,f71])).

fof(f38,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (24678)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (24686)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.51  % (24670)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.51  % (24686)Refutation not found, incomplete strategy% (24686)------------------------------
% 1.19/0.51  % (24686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (24686)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (24686)Memory used [KB]: 10746
% 1.19/0.51  % (24686)Time elapsed: 0.062 s
% 1.19/0.51  % (24686)------------------------------
% 1.19/0.51  % (24686)------------------------------
% 1.19/0.52  % (24677)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.52  % (24688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.52  % (24675)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.53  % (24666)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (24665)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (24680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.53  % (24667)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (24664)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (24668)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (24692)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (24690)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (24689)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.54  % (24673)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.54  % (24669)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (24684)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.54  % (24691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (24682)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.54  % (24687)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.55  % (24685)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (24685)Refutation not found, incomplete strategy% (24685)------------------------------
% 1.31/0.55  % (24685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (24683)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (24676)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (24672)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.55  % (24693)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (24685)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (24685)Memory used [KB]: 1663
% 1.31/0.55  % (24685)Time elapsed: 0.141 s
% 1.31/0.55  % (24685)------------------------------
% 1.31/0.55  % (24685)------------------------------
% 1.31/0.55  % (24681)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.55  % (24679)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (24671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.55  % (24679)Refutation not found, incomplete strategy% (24679)------------------------------
% 1.31/0.55  % (24679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (24679)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (24679)Memory used [KB]: 6140
% 1.31/0.56  % (24679)Time elapsed: 0.004 s
% 1.31/0.56  % (24679)------------------------------
% 1.31/0.56  % (24679)------------------------------
% 1.31/0.56  % (24681)Refutation not found, incomplete strategy% (24681)------------------------------
% 1.31/0.56  % (24681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (24672)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  % (24681)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.57  
% 1.31/0.57  % (24681)Memory used [KB]: 10618
% 1.31/0.57  % (24681)Time elapsed: 0.157 s
% 1.31/0.57  % (24681)------------------------------
% 1.31/0.57  % (24681)------------------------------
% 1.31/0.57  fof(f367,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(avatar_sat_refutation,[],[f98,f100,f215,f362])).
% 1.31/0.57  fof(f362,plain,(
% 1.31/0.57    ~spl5_1 | ~spl5_2),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f361])).
% 1.31/0.57  fof(f361,plain,(
% 1.31/0.57    $false | (~spl5_1 | ~spl5_2)),
% 1.31/0.57    inference(subsumption_resolution,[],[f360,f93])).
% 1.31/0.57  fof(f93,plain,(
% 1.31/0.57    r2_hidden(sK0,sK1) | ~spl5_1),
% 1.31/0.57    inference(avatar_component_clause,[],[f91])).
% 1.31/0.57  fof(f91,plain,(
% 1.31/0.57    spl5_1 <=> r2_hidden(sK0,sK1)),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.31/0.57  fof(f360,plain,(
% 1.31/0.57    ~r2_hidden(sK0,sK1) | ~spl5_2),
% 1.31/0.57    inference(subsumption_resolution,[],[f353,f243])).
% 1.31/0.57  fof(f243,plain,(
% 1.31/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.57    inference(backward_demodulation,[],[f74,f232])).
% 1.31/0.57  fof(f232,plain,(
% 1.31/0.57    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) )),
% 1.31/0.57    inference(resolution,[],[f229,f41])).
% 1.31/0.57  fof(f41,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f24])).
% 1.31/0.57  fof(f24,plain,(
% 1.31/0.57    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 1.31/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f23])).
% 1.31/0.57  fof(f23,plain,(
% 1.31/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f18,plain,(
% 1.31/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.31/0.57    inference(ennf_transformation,[],[f5])).
% 1.31/0.57  fof(f5,axiom,(
% 1.31/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.31/0.57  fof(f229,plain,(
% 1.31/0.57    ( ! [X8,X9] : (~r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0))) )),
% 1.31/0.57    inference(subsumption_resolution,[],[f228,f85])).
% 1.31/0.57  fof(f85,plain,(
% 1.31/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.31/0.57    inference(equality_resolution,[],[f48])).
% 1.31/0.57  fof(f48,plain,(
% 1.31/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.31/0.57    inference(cnf_transformation,[],[f30])).
% 1.31/0.57  fof(f30,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.31/0.57  fof(f29,plain,(
% 1.31/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f28,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.57    inference(rectify,[],[f27])).
% 1.31/0.57  fof(f27,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.57    inference(flattening,[],[f26])).
% 1.31/0.57  fof(f26,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.31/0.57    inference(nnf_transformation,[],[f2])).
% 1.31/0.57  fof(f2,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.31/0.57  fof(f228,plain,(
% 1.31/0.57    ( ! [X8,X9] : (~r2_hidden(X9,X8) | ~r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0))) )),
% 1.31/0.57    inference(duplicate_literal_removal,[],[f224])).
% 1.31/0.57  fof(f224,plain,(
% 1.31/0.57    ( ! [X8,X9] : (~r2_hidden(X9,X8) | ~r2_hidden(X9,X8) | ~r2_hidden(X9,k3_xboole_0(X8,k1_xboole_0))) )),
% 1.31/0.57    inference(superposition,[],[f61,f74])).
% 1.31/0.57  fof(f61,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f36])).
% 1.31/0.57  fof(f36,plain,(
% 1.31/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.31/0.57    inference(nnf_transformation,[],[f19])).
% 1.31/0.57  fof(f19,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.31/0.57    inference(ennf_transformation,[],[f4])).
% 1.31/0.57  fof(f4,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.31/0.57  fof(f74,plain,(
% 1.31/0.57    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.31/0.57    inference(definition_unfolding,[],[f39,f44])).
% 1.31/0.57  fof(f44,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f6])).
% 1.31/0.57  fof(f6,axiom,(
% 1.31/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.31/0.57  fof(f39,plain,(
% 1.31/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f7])).
% 1.31/0.57  fof(f7,axiom,(
% 1.31/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.31/0.57  fof(f353,plain,(
% 1.31/0.57    sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r2_hidden(sK0,sK1) | ~spl5_2),
% 1.31/0.57    inference(superposition,[],[f76,f325])).
% 1.31/0.57  fof(f325,plain,(
% 1.31/0.57    k1_xboole_0 = k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_2),
% 1.31/0.57    inference(resolution,[],[f295,f41])).
% 1.31/0.57  fof(f295,plain,(
% 1.31/0.57    ( ! [X1] : (~r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl5_2),
% 1.31/0.57    inference(subsumption_resolution,[],[f294,f84])).
% 1.31/0.57  fof(f84,plain,(
% 1.31/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 1.31/0.57    inference(equality_resolution,[],[f49])).
% 1.31/0.57  fof(f49,plain,(
% 1.31/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.31/0.57    inference(cnf_transformation,[],[f30])).
% 1.31/0.57  fof(f294,plain,(
% 1.31/0.57    ( ! [X1] : (~r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl5_2),
% 1.31/0.57    inference(duplicate_literal_removal,[],[f290])).
% 1.31/0.57  fof(f290,plain,(
% 1.31/0.57    ( ! [X1] : (~r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl5_2),
% 1.31/0.57    inference(superposition,[],[f61,f96])).
% 1.31/0.57  fof(f96,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_2),
% 1.31/0.57    inference(avatar_component_clause,[],[f95])).
% 1.31/0.57  fof(f95,plain,(
% 1.31/0.57    spl5_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.31/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.31/0.57  fof(f76,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) != X0 | ~r2_hidden(X1,X0)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f45,f44,f71])).
% 1.31/0.57  fof(f71,plain,(
% 1.31/0.57    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f40,f70])).
% 1.31/0.57  fof(f70,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f43,f69])).
% 1.31/0.57  fof(f69,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f47,f68])).
% 1.31/0.57  fof(f68,plain,(
% 1.31/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f64,f67])).
% 1.31/0.57  fof(f67,plain,(
% 1.31/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/0.57    inference(definition_unfolding,[],[f65,f66])).
% 1.31/0.57  fof(f66,plain,(
% 1.31/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f13])).
% 1.31/0.57  fof(f13,axiom,(
% 1.31/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.57  fof(f65,plain,(
% 1.31/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f12])).
% 1.31/0.57  fof(f12,axiom,(
% 1.31/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.57  fof(f64,plain,(
% 1.31/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f11])).
% 1.31/0.57  fof(f11,axiom,(
% 1.31/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.57  fof(f47,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f10])).
% 1.31/0.57  fof(f10,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.57  fof(f43,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f9])).
% 1.31/0.57  fof(f9,axiom,(
% 1.31/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.57  fof(f40,plain,(
% 1.31/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f8])).
% 1.31/0.57  fof(f8,axiom,(
% 1.31/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.57  fof(f45,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f25])).
% 1.31/0.57  fof(f25,plain,(
% 1.31/0.57    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.31/0.57    inference(nnf_transformation,[],[f14])).
% 1.31/0.57  fof(f14,axiom,(
% 1.31/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.31/0.57  fof(f215,plain,(
% 1.31/0.57    spl5_1 | spl5_2),
% 1.31/0.57    inference(avatar_contradiction_clause,[],[f214])).
% 1.31/0.57  fof(f214,plain,(
% 1.31/0.57    $false | (spl5_1 | spl5_2)),
% 1.31/0.57    inference(trivial_inequality_removal,[],[f213])).
% 1.31/0.57  fof(f213,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (spl5_1 | spl5_2)),
% 1.31/0.57    inference(superposition,[],[f126,f205])).
% 1.31/0.57  fof(f205,plain,(
% 1.31/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | spl5_1),
% 1.31/0.57    inference(backward_demodulation,[],[f74,f192])).
% 1.31/0.57  fof(f192,plain,(
% 1.31/0.57    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | spl5_1),
% 1.31/0.57    inference(superposition,[],[f177,f42])).
% 1.31/0.57  fof(f42,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f1])).
% 1.31/0.57  fof(f1,axiom,(
% 1.31/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.31/0.57  fof(f177,plain,(
% 1.31/0.57    ( ! [X19] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X19)) ) | spl5_1),
% 1.31/0.57    inference(resolution,[],[f128,f124])).
% 1.31/0.57  fof(f124,plain,(
% 1.31/0.57    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | spl5_1),
% 1.31/0.57    inference(backward_demodulation,[],[f113,f116])).
% 1.31/0.57  fof(f116,plain,(
% 1.31/0.57    k1_xboole_0 = k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl5_1),
% 1.31/0.57    inference(resolution,[],[f113,f41])).
% 1.31/0.57  fof(f113,plain,(
% 1.31/0.57    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | spl5_1),
% 1.31/0.57    inference(subsumption_resolution,[],[f111,f85])).
% 1.31/0.57  fof(f111,plain,(
% 1.31/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | spl5_1),
% 1.31/0.57    inference(duplicate_literal_removal,[],[f107])).
% 1.31/0.57  fof(f107,plain,(
% 1.31/0.57    ( ! [X4] : (~r2_hidden(X4,sK1) | ~r2_hidden(X4,sK1) | ~r2_hidden(X4,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | spl5_1),
% 1.31/0.57    inference(superposition,[],[f61,f101])).
% 1.31/0.57  fof(f101,plain,(
% 1.31/0.57    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl5_1),
% 1.31/0.57    inference(resolution,[],[f92,f75])).
% 1.31/0.57  fof(f75,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k5_xboole_0(X0,k3_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = X0) )),
% 1.31/0.57    inference(definition_unfolding,[],[f46,f44,f71])).
% 1.31/0.57  fof(f46,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f25])).
% 1.31/0.57  fof(f92,plain,(
% 1.31/0.57    ~r2_hidden(sK0,sK1) | spl5_1),
% 1.31/0.57    inference(avatar_component_clause,[],[f91])).
% 1.31/0.57  fof(f128,plain,(
% 1.31/0.57    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = k3_xboole_0(X2,X3)) ) | spl5_1),
% 1.31/0.57    inference(forward_demodulation,[],[f127,f116])).
% 1.31/0.57  fof(f127,plain,(
% 1.31/0.57    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k1_xboole_0),X2) | k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(X2,X3)) ) | spl5_1),
% 1.31/0.57    inference(forward_demodulation,[],[f117,f116])).
% 1.31/0.57  fof(f117,plain,(
% 1.31/0.57    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X2) | k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k3_xboole_0(X2,X3)) ) | spl5_1),
% 1.31/0.57    inference(resolution,[],[f113,f51])).
% 1.31/0.57  fof(f51,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 1.31/0.57    inference(cnf_transformation,[],[f30])).
% 1.31/0.57  fof(f126,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (spl5_1 | spl5_2)),
% 1.31/0.57    inference(backward_demodulation,[],[f97,f116])).
% 1.31/0.57  fof(f97,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl5_2),
% 1.31/0.57    inference(avatar_component_clause,[],[f95])).
% 1.31/0.57  fof(f100,plain,(
% 1.31/0.57    ~spl5_1 | spl5_2),
% 1.31/0.57    inference(avatar_split_clause,[],[f99,f95,f91])).
% 1.31/0.57  fof(f99,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(sK0,sK1)),
% 1.31/0.57    inference(forward_demodulation,[],[f73,f42])).
% 1.31/0.57  fof(f73,plain,(
% 1.31/0.57    ~r2_hidden(sK0,sK1) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.31/0.57    inference(definition_unfolding,[],[f37,f71,f44,f71])).
% 1.31/0.57  fof(f37,plain,(
% 1.31/0.57    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  fof(f22,plain,(
% 1.31/0.57    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.31/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 1.31/0.57  fof(f21,plain,(
% 1.31/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.31/0.57    introduced(choice_axiom,[])).
% 1.31/0.57  fof(f20,plain,(
% 1.31/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.31/0.57    inference(nnf_transformation,[],[f17])).
% 1.31/0.57  fof(f17,plain,(
% 1.31/0.57    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.31/0.57    inference(ennf_transformation,[],[f16])).
% 1.31/0.57  fof(f16,negated_conjecture,(
% 1.31/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.31/0.57    inference(negated_conjecture,[],[f15])).
% 1.31/0.57  fof(f15,conjecture,(
% 1.31/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.31/0.57  fof(f98,plain,(
% 1.31/0.57    spl5_1 | ~spl5_2),
% 1.31/0.57    inference(avatar_split_clause,[],[f89,f95,f91])).
% 1.31/0.57  fof(f89,plain,(
% 1.31/0.57    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(sK0,sK1)),
% 1.31/0.57    inference(forward_demodulation,[],[f72,f42])).
% 1.31/0.57  fof(f72,plain,(
% 1.31/0.57    r2_hidden(sK0,sK1) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.31/0.57    inference(definition_unfolding,[],[f38,f71,f44,f71])).
% 1.31/0.57  fof(f38,plain,(
% 1.31/0.57    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  % SZS output end Proof for theBenchmark
% 1.31/0.57  % (24672)------------------------------
% 1.31/0.57  % (24672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (24672)Termination reason: Refutation
% 1.31/0.57  
% 1.31/0.57  % (24672)Memory used [KB]: 10874
% 1.31/0.57  % (24672)Time elapsed: 0.164 s
% 1.31/0.57  % (24672)------------------------------
% 1.31/0.57  % (24672)------------------------------
% 1.31/0.58  % (24663)Success in time 0.216 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 194 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  274 ( 677 expanded)
%              Number of equality atoms :   65 ( 189 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f67,f71,f81,f87,f134,f137,f156,f161,f176,f183])).

fof(f183,plain,
    ( ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f133,f175])).

fof(f175,plain,
    ( ! [X0] : ~ r2_hidden(sK3,X0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl5_14
  <=> ! [X0] : ~ r2_hidden(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f133,plain,
    ( r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl5_12
  <=> r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f176,plain,
    ( spl5_2
    | spl5_14
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f169,f132,f174,f61])).

fof(f61,plain,
    ( spl5_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | sK3 = k2_mcart_1(sK0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f133,f95])).

fof(f95,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k2_enumset1(X6,X6,X6,X6))
      | ~ r2_hidden(X5,X7)
      | X5 = X6 ) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f161,plain,
    ( ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f130,f155])).

fof(f155,plain,
    ( ! [X0] : ~ r2_hidden(sK2,X0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_13
  <=> ! [X0] : ~ r2_hidden(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f130,plain,
    ( r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_11
  <=> r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f156,plain,
    ( spl5_3
    | spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f149,f129,f154,f65])).

fof(f65,plain,
    ( spl5_3
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | sK2 = k2_mcart_1(sK0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f130,f95])).

fof(f137,plain,
    ( ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f80,f127])).

fof(f127,plain,
    ( ! [X4] : ~ r2_hidden(k2_mcart_1(sK0),X4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_10
  <=> ! [X4] : ~ r2_hidden(k2_mcart_1(sK0),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f80,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_6
  <=> r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,
    ( spl5_10
    | spl5_11
    | spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f117,f79,f132,f129,f126])).

fof(f117,plain,
    ( ! [X4] :
        ( r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
        | r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
        | ~ r2_hidden(k2_mcart_1(sK0),X4) )
    | ~ spl5_6 ),
    inference(resolution,[],[f108,f84])).

fof(f84,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,k2_enumset1(X6,X6,X6,X6))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k2_mcart_1(sK0),X4)
        | r2_hidden(sK3,X4)
        | r2_hidden(sK2,X4) )
    | ~ spl5_6 ),
    inference(resolution,[],[f103,f80])).

fof(f103,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_hidden(X16,k2_enumset1(X14,X14,X14,X15))
      | ~ r2_hidden(X16,X13)
      | r2_hidden(X15,X13)
      | r2_hidden(X14,X13) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f87,plain,
    ( spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f85,f69,f58])).

fof(f58,plain,
    ( spl5_1
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f69,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f85,plain,
    ( sK1 = k1_mcart_1(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f81,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f77,f69,f79])).

fof(f77,plain,
    ( r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f31,f70])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f71,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f69])).

fof(f46,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f24,f45,f44])).

fof(f24,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

% (31260)Refutation not found, incomplete strategy% (31260)------------------------------
% (31260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f67,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f25,f65,f58])).

% (31260)Termination reason: Refutation not found, incomplete strategy
fof(f25,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f26,f61,f58])).

% (31260)Memory used [KB]: 1663
fof(f26,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

% (31260)Time elapsed: 0.135 s
% (31260)------------------------------
% (31260)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (31266)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.48  % (31274)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.48  % (31282)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (31282)Refutation not found, incomplete strategy% (31282)------------------------------
% 0.20/0.49  % (31282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31282)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31282)Memory used [KB]: 10746
% 0.20/0.49  % (31282)Time elapsed: 0.103 s
% 0.20/0.49  % (31282)------------------------------
% 0.20/0.49  % (31282)------------------------------
% 0.20/0.50  % (31284)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (31262)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (31262)Refutation not found, incomplete strategy% (31262)------------------------------
% 0.20/0.50  % (31262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (31262)Memory used [KB]: 10618
% 0.20/0.50  % (31262)Time elapsed: 0.091 s
% 0.20/0.50  % (31262)------------------------------
% 0.20/0.50  % (31262)------------------------------
% 0.20/0.51  % (31278)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (31272)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31273)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (31270)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (31270)Refutation not found, incomplete strategy% (31270)------------------------------
% 0.20/0.51  % (31270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31270)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31270)Memory used [KB]: 10618
% 0.20/0.51  % (31270)Time elapsed: 0.107 s
% 0.20/0.51  % (31270)------------------------------
% 0.20/0.51  % (31270)------------------------------
% 0.20/0.53  % (31260)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (31267)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (31264)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (31283)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (31287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (31265)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (31276)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (31263)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (31261)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (31285)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (31286)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (31279)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (31275)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (31279)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f63,f67,f71,f81,f87,f134,f137,f156,f161,f176,f183])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    ~spl5_12 | ~spl5_14),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f181])).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    $false | (~spl5_12 | ~spl5_14)),
% 0.20/0.54    inference(subsumption_resolution,[],[f133,f175])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK3,X0)) ) | ~spl5_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f174])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    spl5_14 <=> ! [X0] : ~r2_hidden(sK3,X0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | ~spl5_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f132])).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    spl5_12 <=> r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    spl5_2 | spl5_14 | ~spl5_12),
% 0.20/0.54    inference(avatar_split_clause,[],[f169,f132,f174,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    spl5_2 <=> sK3 = k2_mcart_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f169,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK3,X0) | sK3 = k2_mcart_1(sK0)) ) | ~spl5_12),
% 0.20/0.54    inference(resolution,[],[f133,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X6,X7,X5] : (~r2_hidden(X5,k2_enumset1(X6,X6,X6,X6)) | ~r2_hidden(X5,X7) | X5 = X6) )),
% 0.20/0.54    inference(resolution,[],[f49,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(rectify,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f42,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f27,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.54    inference(nnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    ~spl5_11 | ~spl5_13),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    $false | (~spl5_11 | ~spl5_13)),
% 0.20/0.54    inference(subsumption_resolution,[],[f130,f155])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK2,X0)) ) | ~spl5_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f154])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    spl5_13 <=> ! [X0] : ~r2_hidden(sK2,X0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | ~spl5_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    spl5_11 <=> r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    spl5_3 | spl5_13 | ~spl5_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f149,f129,f154,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    spl5_3 <=> sK2 = k2_mcart_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK2,X0) | sK2 = k2_mcart_1(sK0)) ) | ~spl5_11),
% 0.20/0.54    inference(resolution,[],[f130,f95])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ~spl5_6 | ~spl5_10),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    $false | (~spl5_6 | ~spl5_10)),
% 0.20/0.54    inference(subsumption_resolution,[],[f80,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(k2_mcart_1(sK0),X4)) ) | ~spl5_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    spl5_10 <=> ! [X4] : ~r2_hidden(k2_mcart_1(sK0),X4)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl5_6 <=> r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    spl5_10 | spl5_11 | spl5_12 | ~spl5_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f117,f79,f132,f129,f126])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X4] : (r2_hidden(sK3,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | r2_hidden(sK2,k2_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | ~r2_hidden(k2_mcart_1(sK0),X4)) ) | ~spl5_6),
% 0.20/0.54    inference(resolution,[],[f108,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X6,X7] : (r2_hidden(X6,k2_enumset1(X6,X6,X6,X6)) | ~r2_hidden(X6,X7)) )),
% 0.20/0.54    inference(resolution,[],[f53,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f41,f45])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ( ! [X4] : (~r2_hidden(k2_mcart_1(sK0),X4) | r2_hidden(sK3,X4) | r2_hidden(sK2,X4)) ) | ~spl5_6),
% 0.20/0.54    inference(resolution,[],[f103,f80])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X14,X15,X13,X16] : (~r2_hidden(X16,k2_enumset1(X14,X14,X14,X15)) | ~r2_hidden(X16,X13) | r2_hidden(X15,X13) | r2_hidden(X14,X13)) )),
% 0.20/0.54    inference(superposition,[],[f54,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f43,f44])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    spl5_1 | ~spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f85,f69,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    spl5_1 <=> sK1 = k1_mcart_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    spl5_4 <=> r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    sK1 = k1_mcart_1(sK0) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f48,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) | ~spl5_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f69])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.20/0.54    inference(definition_unfolding,[],[f32,f45])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    spl5_6 | ~spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f77,f69,f79])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f31,f70])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f46,f69])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))),
% 0.20/0.54    inference(definition_unfolding,[],[f24,f45,f44])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f9])).
% 0.20/0.54  fof(f9,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 0.20/0.54  % (31260)Refutation not found, incomplete strategy% (31260)------------------------------
% 0.20/0.54  % (31260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ~spl5_1 | ~spl5_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f25,f65,f58])).
% 0.20/0.54  % (31260)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ~spl5_1 | ~spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f26,f61,f58])).
% 0.20/0.54  % (31260)Memory used [KB]: 1663
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  % (31260)Time elapsed: 0.135 s
% 0.20/0.54  % (31260)------------------------------
% 0.20/0.54  % (31260)------------------------------
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (31279)------------------------------
% 0.20/0.54  % (31279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31279)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (31279)Memory used [KB]: 10874
% 0.20/0.54  % (31279)Time elapsed: 0.132 s
% 0.20/0.54  % (31279)------------------------------
% 0.20/0.54  % (31279)------------------------------
% 0.20/0.54  % (31268)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (31259)Success in time 0.188 s
%------------------------------------------------------------------------------

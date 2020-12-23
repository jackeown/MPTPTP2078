%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 (1163 expanded)
%              Number of leaves         :   27 ( 370 expanded)
%              Depth                    :   20
%              Number of atoms          :  541 (5348 expanded)
%              Number of equality atoms :  291 (3360 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f673,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f612,f622,f672])).

fof(f672,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | ~ spl9_1 ),
    inference(resolution,[],[f663,f134])).

fof(f134,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f117,f116])).

fof(f116,plain,(
    ! [X4,X2,X0] :
      ( ~ sP1(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f117,plain,(
    ! [X0,X1] : sP1(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f82,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f663,plain,
    ( ! [X0] : ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f648,f236])).

fof(f236,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X2,X2,X2))
      | X2 = X3 ) ),
    inference(subsumption_resolution,[],[f235,f142])).

fof(f142,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f118,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f118,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f85,f94])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f235,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | X2 = X3
      | ~ r2_hidden(X3,k1_enumset1(X2,X2,X2)) ) ),
    inference(superposition,[],[f102,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f155,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f31])).

% (8274)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f155,plain,(
    ! [X6,X5] : ~ r2_hidden(X5,k4_xboole_0(X6,X6)) ),
    inference(subsumption_resolution,[],[f154,f142])).

fof(f154,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k4_xboole_0(X6,X6))
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(resolution,[],[f69,f139])).

fof(f139,plain,(
    ! [X1] : sP0(k1_xboole_0,X1,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f114,f55])).

fof(f55,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f114,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f99])).

% (8280)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f74,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X1)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK7(X0,X1,X2),X1) )
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X0)
            & r2_hidden(sK7(X0,X1,X2),X1) )
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f94])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f648,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0)) )
    | ~ spl9_1 ),
    inference(superposition,[],[f358,f641])).

fof(f641,plain,
    ( sK5 = k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f623,f628])).

fof(f628,plain,
    ( sK5 = k1_mcart_1(k1_mcart_1(sK5))
    | ~ spl9_1 ),
    inference(backward_demodulation,[],[f488,f122])).

fof(f122,plain,
    ( sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_1
  <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f488,plain,(
    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f487,f49])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
      | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
    & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( k7_mcart_1(X0,X1,X2,X3) = X3
              | k6_mcart_1(X0,X1,X2,X3) = X3
              | k5_mcart_1(X0,X1,X2,X3) = X3 )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X3] :
          ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
            | k6_mcart_1(sK2,sK3,sK4,X3) = X3
            | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( k7_mcart_1(sK2,sK3,sK4,X3) = X3
          | k6_mcart_1(sK2,sK3,sK4,X3) = X3
          | k5_mcart_1(sK2,sK3,sK4,X3) = X3 )
        & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4)) )
   => ( ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
        | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) )
      & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f487,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f486,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f486,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f485,f51])).

fof(f51,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f485,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f111,f95])).

fof(f95,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f52,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f91,f67])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f623,plain,(
    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f613,f460])).

fof(f460,plain,(
    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(subsumption_resolution,[],[f459,f49])).

fof(f459,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f458,f50])).

fof(f458,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f457,f51])).

fof(f457,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f110,f95])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f92,f67])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f613,plain,(
    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f500,f488])).

fof(f500,plain,(
    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5)) ),
    inference(forward_demodulation,[],[f499,f427])).

% (8291)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f427,plain,(
    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f426,f49])).

fof(f426,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f425,f50])).

fof(f425,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f424,f51])).

fof(f424,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f109,f95])).

% (8280)Refutation not found, incomplete strategy% (8280)------------------------------
% (8280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8280)Termination reason: Refutation not found, incomplete strategy

% (8280)Memory used [KB]: 10618
% (8280)Time elapsed: 0.128 s
% (8280)------------------------------
% (8280)------------------------------
fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f93,f67])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f499,plain,(
    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f498,f49])).

fof(f498,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f497,f50])).

fof(f497,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f496,f51])).

fof(f496,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f108,f95])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f90,f66,f67])).

fof(f66,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

% (8287)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f358,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0)) ) ),
    inference(subsumption_resolution,[],[f355,f246])).

fof(f246,plain,(
    ! [X2,X3] : k1_xboole_0 != k1_enumset1(X2,X2,X3) ),
    inference(subsumption_resolution,[],[f244,f135])).

fof(f135,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f117,f115])).

fof(f115,plain,(
    ! [X4,X2,X1] :
      ( ~ sP1(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f244,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_enumset1(X2,X2,X3)
      | ~ r2_hidden(X3,k1_enumset1(X2,X2,X3)) ) ),
    inference(superposition,[],[f106,f156])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f88,f62,f62])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f355,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_enumset1(X0,X0,X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f97,f327])).

% (8277)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f327,plain,(
    ! [X2] : sK6(k1_enumset1(X2,X2,X2)) = X2 ),
    inference(subsumption_resolution,[],[f322,f246])).

fof(f322,plain,(
    ! [X2] :
      ( sK6(k1_enumset1(X2,X2,X2)) = X2
      | k1_xboole_0 = k1_enumset1(X2,X2,X2) ) ),
    inference(resolution,[],[f236,f59])).

% (8271)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f97,plain,(
    ! [X4,X2,X0,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f60,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK6(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f622,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f620,f136])).

fof(f136,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f112,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f112,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f620,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5)
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f613,f618])).

fof(f618,plain,
    ( sK5 = k2_mcart_1(sK5)
    | ~ spl9_3 ),
    inference(backward_demodulation,[],[f427,f130])).

fof(f130,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_3
  <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f612,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl9_2 ),
    inference(resolution,[],[f605,f134])).

fof(f605,plain,
    ( ! [X0] : ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f604,f236])).

fof(f604,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0)) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f603,f246])).

fof(f603,plain,
    ( ! [X0] :
        ( sK5 != X0
        | ~ r2_hidden(sK5,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl9_2 ),
    inference(superposition,[],[f505,f327])).

fof(f505,plain,
    ( ! [X2] :
        ( sK5 != sK6(X2)
        | ~ r2_hidden(sK5,X2)
        | k1_xboole_0 = X2 )
    | ~ spl9_2 ),
    inference(superposition,[],[f96,f502])).

fof(f502,plain,
    ( sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5))
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f501,f488])).

fof(f501,plain,
    ( sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k2_mcart_1(sK5))
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f500,f126])).

fof(f126,plain,
    ( sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_2
  <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f96,plain,(
    ! [X4,X2,X0,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f61,plain,(
    ! [X4,X2,X0,X3] :
      ( k3_mcart_1(X2,X3,X4) != sK6(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f131,plain,
    ( spl9_1
    | spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f53,f128,f124,f120])).

fof(f53,plain,
    ( sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)
    | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8270)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8265)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (8268)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (8264)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8286)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (8267)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (8278)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (8293)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (8278)Refutation not found, incomplete strategy% (8278)------------------------------
% 0.21/0.52  % (8278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8269)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8272)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8278)Memory used [KB]: 1791
% 0.21/0.53  % (8278)Time elapsed: 0.109 s
% 0.21/0.53  % (8278)------------------------------
% 0.21/0.53  % (8278)------------------------------
% 0.21/0.53  % (8266)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (8279)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8285)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (8270)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f673,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f131,f612,f622,f672])).
% 0.21/0.54  fof(f672,plain,(
% 0.21/0.54    ~spl9_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f666])).
% 0.21/0.54  fof(f666,plain,(
% 0.21/0.54    $false | ~spl9_1),
% 0.21/0.54    inference(resolution,[],[f663,f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(resolution,[],[f117,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    ( ! [X4,X2,X0] : (~sP1(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f82,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.21/0.54    inference(definition_folding,[],[f5,f26])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.54  fof(f663,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5,k1_enumset1(X0,X0,X0))) ) | ~spl9_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f648,f236])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k1_enumset1(X2,X2,X2)) | X2 = X3) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f235,f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f118,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f85,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f56,f62])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.54    inference(flattening,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.54    inference(nnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.54  fof(f235,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r2_hidden(X3,k1_xboole_0) | X2 = X3 | ~r2_hidden(X3,k1_enumset1(X2,X2,X2))) )),
% 0.21/0.54    inference(superposition,[],[f102,f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f155,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f31])).
% 0.21/0.54  % (8274)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~r2_hidden(X5,k4_xboole_0(X6,X6))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f142])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X6,X5] : (~r2_hidden(X5,k4_xboole_0(X6,X6)) | r2_hidden(X5,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f69,f139])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X1] : (sP0(k1_xboole_0,X1,k4_xboole_0(X1,X1))) )),
% 0.21/0.54    inference(superposition,[],[f114,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f99])).
% 0.21/0.54  % (8280)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f74,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.54    inference(definition_folding,[],[f1,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK7(X0,X1,X2),X1)) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f24])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f86,f94])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f648,plain,(
% 0.21/0.54    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0))) ) | ~spl9_1),
% 0.21/0.54    inference(superposition,[],[f358,f641])).
% 0.21/0.54  fof(f641,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(sK5,k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5)) | ~spl9_1),
% 0.21/0.54    inference(forward_demodulation,[],[f623,f628])).
% 0.21/0.54  fof(f628,plain,(
% 0.21/0.54    sK5 = k1_mcart_1(k1_mcart_1(sK5)) | ~spl9_1),
% 0.21/0.54    inference(backward_demodulation,[],[f488,f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    sK5 = k5_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f120])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl9_1 <=> sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.54  fof(f488,plain,(
% 0.21/0.54    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5))),
% 0.21/0.54    inference(subsumption_resolution,[],[f487,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    k1_xboole_0 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f29,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ? [X3] : ((k7_mcart_1(sK2,sK3,sK4,X3) = X3 | k6_mcart_1(sK2,sK3,sK4,X3) = X3 | k5_mcart_1(sK2,sK3,sK4,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(sK2,sK3,sK4))) => ((sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.21/0.54  fof(f487,plain,(
% 0.21/0.54    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f486,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    k1_xboole_0 != sK3),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f486,plain,(
% 0.21/0.54    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f485,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    k1_xboole_0 != sK4),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f485,plain,(
% 0.21/0.54    k5_mcart_1(sK2,sK3,sK4,sK5) = k1_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f111,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 0.21/0.54    inference(definition_unfolding,[],[f52,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_subset_1(sK5,k3_zfmisc_1(sK2,sK3,sK4))),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f91,f67])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.54  fof(f623,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(sK5))),
% 0.21/0.54    inference(forward_demodulation,[],[f613,f460])).
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5))),
% 0.21/0.54    inference(subsumption_resolution,[],[f459,f49])).
% 0.21/0.54  fof(f459,plain,(
% 0.21/0.54    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f458,f50])).
% 0.21/0.54  fof(f458,plain,(
% 0.21/0.54    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f457,f51])).
% 0.21/0.54  fof(f457,plain,(
% 0.21/0.54    k6_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(k1_mcart_1(sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f110,f95])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f92,f67])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f613,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))),
% 0.21/0.54    inference(forward_demodulation,[],[f500,f488])).
% 0.21/0.54  fof(f500,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k2_mcart_1(sK5))),
% 0.21/0.54    inference(forward_demodulation,[],[f499,f427])).
% 0.21/0.54  % (8291)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  fof(f427,plain,(
% 0.21/0.54    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f426,f49])).
% 0.21/0.54  fof(f426,plain,(
% 0.21/0.54    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f425,f50])).
% 0.21/0.54  fof(f425,plain,(
% 0.21/0.54    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f424,f51])).
% 0.21/0.54  fof(f424,plain,(
% 0.21/0.54    k7_mcart_1(sK2,sK3,sK4,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f109,f95])).
% 0.21/0.54  % (8280)Refutation not found, incomplete strategy% (8280)------------------------------
% 0.21/0.54  % (8280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8280)Memory used [KB]: 10618
% 0.21/0.54  % (8280)Time elapsed: 0.128 s
% 0.21/0.54  % (8280)------------------------------
% 0.21/0.54  % (8280)------------------------------
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f93,f67])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f499,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5))),
% 0.21/0.54    inference(subsumption_resolution,[],[f498,f49])).
% 0.21/0.54  fof(f498,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f497,f50])).
% 0.21/0.54  fof(f497,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(subsumption_resolution,[],[f496,f51])).
% 0.21/0.54  fof(f496,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),k6_mcart_1(sK2,sK3,sK4,sK5)),k7_mcart_1(sK2,sK3,sK4,sK5)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f108,f95])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f90,f66,f67])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  % (8287)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f355,f246])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 != k1_enumset1(X2,X2,X3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f244,f135])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 0.21/0.54    inference(resolution,[],[f117,f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X4,X2,X1] : (~sP1(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 != k1_enumset1(X2,X2,X3) | ~r2_hidden(X3,k1_enumset1(X2,X2,X3))) )),
% 0.21/0.54    inference(superposition,[],[f106,f156])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f88,f62,f62])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(flattening,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f97,f327])).
% 0.21/0.54  % (8277)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ( ! [X2] : (sK6(k1_enumset1(X2,X2,X2)) = X2) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f322,f246])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    ( ! [X2] : (sK6(k1_enumset1(X2,X2,X2)) = X2 | k1_xboole_0 = k1_enumset1(X2,X2,X2)) )),
% 0.21/0.54    inference(resolution,[],[f236,f59])).
% 0.21/0.54  % (8271)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3] : (sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f60,f66])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f622,plain,(
% 0.21/0.54    ~spl9_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f621])).
% 0.21/0.54  fof(f621,plain,(
% 0.21/0.54    $false | ~spl9_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f620,f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 0.21/0.54    inference(forward_demodulation,[],[f112,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.54  fof(f620,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k6_mcart_1(sK2,sK3,sK4,sK5)),sK5) | ~spl9_3),
% 0.21/0.54    inference(forward_demodulation,[],[f613,f618])).
% 0.21/0.54  fof(f618,plain,(
% 0.21/0.54    sK5 = k2_mcart_1(sK5) | ~spl9_3),
% 0.21/0.54    inference(backward_demodulation,[],[f427,f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl9_3 <=> sK5 = k7_mcart_1(sK2,sK3,sK4,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.54  fof(f612,plain,(
% 0.21/0.54    ~spl9_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f606])).
% 0.21/0.54  fof(f606,plain,(
% 0.21/0.54    $false | ~spl9_2),
% 0.21/0.54    inference(resolution,[],[f605,f134])).
% 0.21/0.54  fof(f605,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK5,k1_enumset1(X0,X0,X0))) ) | ~spl9_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f604,f236])).
% 0.21/0.54  fof(f604,plain,(
% 0.21/0.54    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0))) ) | ~spl9_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f603,f246])).
% 0.21/0.54  fof(f603,plain,(
% 0.21/0.54    ( ! [X0] : (sK5 != X0 | ~r2_hidden(sK5,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl9_2),
% 0.21/0.54    inference(superposition,[],[f505,f327])).
% 0.21/0.54  fof(f505,plain,(
% 0.21/0.54    ( ! [X2] : (sK5 != sK6(X2) | ~r2_hidden(sK5,X2) | k1_xboole_0 = X2) ) | ~spl9_2),
% 0.21/0.54    inference(superposition,[],[f96,f502])).
% 0.21/0.54  fof(f502,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),sK5),k2_mcart_1(sK5)) | ~spl9_2),
% 0.21/0.54    inference(forward_demodulation,[],[f501,f488])).
% 0.21/0.54  fof(f501,plain,(
% 0.21/0.54    sK5 = k4_tarski(k4_tarski(k5_mcart_1(sK2,sK3,sK4,sK5),sK5),k2_mcart_1(sK5)) | ~spl9_2),
% 0.21/0.54    inference(forward_demodulation,[],[f500,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | ~spl9_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl9_2 <=> sK5 = k6_mcart_1(sK2,sK3,sK4,sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3] : (sK6(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f61,f66])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl9_1 | spl9_2 | spl9_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f53,f128,f124,f120])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    sK5 = k7_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k6_mcart_1(sK2,sK3,sK4,sK5) | sK5 = k5_mcart_1(sK2,sK3,sK4,sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8270)------------------------------
% 0.21/0.54  % (8270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8291)Refutation not found, incomplete strategy% (8291)------------------------------
% 0.21/0.54  % (8291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8291)Memory used [KB]: 6268
% 0.21/0.54  % (8291)Time elapsed: 0.130 s
% 0.21/0.54  % (8291)------------------------------
% 0.21/0.54  % (8291)------------------------------
% 0.21/0.54  % (8270)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8270)Memory used [KB]: 11257
% 0.21/0.54  % (8270)Time elapsed: 0.107 s
% 0.21/0.54  % (8270)------------------------------
% 0.21/0.54  % (8270)------------------------------
% 0.21/0.54  % (8293)Refutation not found, incomplete strategy% (8293)------------------------------
% 0.21/0.54  % (8293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8293)Memory used [KB]: 1663
% 0.21/0.54  % (8293)Time elapsed: 0.003 s
% 0.21/0.54  % (8293)------------------------------
% 0.21/0.54  % (8293)------------------------------
% 0.21/0.55  % (8263)Success in time 0.175 s
%------------------------------------------------------------------------------

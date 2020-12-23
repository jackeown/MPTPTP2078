%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:37 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 298 expanded)
%              Number of leaves         :   17 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  311 (1134 expanded)
%              Number of equality atoms :  152 ( 483 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1099,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1098,f275])).

fof(f275,plain,(
    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f264,f75])).

fof(f75,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f40,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (17246)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f264,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f251,f76])).

fof(f76,plain,
    ( sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,sK0) ),
    inference(definition_unfolding,[],[f39,f73])).

fof(f39,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f251,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(sK0,X0)) ),
    inference(subsumption_resolution,[],[f250,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f250,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k4_xboole_0(sK0,X0))
      | ~ r2_hidden(sK1,sK0) ) ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,(
    ! [X0] :
      ( sK0 != sK0
      | ~ r2_hidden(sK1,k4_xboole_0(sK0,X0))
      | ~ r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f248,f76])).

fof(f248,plain,(
    ! [X0] :
      ( sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(sK1,k4_xboole_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f245,f95])).

fof(f95,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f67,f56])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f245,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(sK1,k4_xboole_0(sK0,X0))
      | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f115,f75])).

fof(f115,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(sK1,k4_xboole_0(sK0,X2)) ) ),
    inference(resolution,[],[f105,f93])).

fof(f105,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK1,sK0)
      | ~ r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f92,f76])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1098,plain,(
    sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f1097,f128])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f125,f102])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f125,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f74,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1097,plain,(
    k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1083,f102])).

fof(f1083,plain,(
    k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f133,f1023])).

fof(f1023,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(resolution,[],[f116,f264])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f74,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f45,f45])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17172)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (17164)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (17155)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (17164)Refutation not found, incomplete strategy% (17164)------------------------------
% 0.21/0.51  % (17164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17164)Memory used [KB]: 1663
% 0.21/0.51  % (17164)Time elapsed: 0.056 s
% 0.21/0.51  % (17164)------------------------------
% 0.21/0.51  % (17164)------------------------------
% 0.21/0.52  % (17153)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (17169)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (17171)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.54  % (17167)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.54  % (17150)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.54  % (17167)Refutation not found, incomplete strategy% (17167)------------------------------
% 1.39/0.54  % (17167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (17167)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (17167)Memory used [KB]: 1663
% 1.39/0.54  % (17167)Time elapsed: 0.126 s
% 1.39/0.54  % (17167)------------------------------
% 1.39/0.54  % (17167)------------------------------
% 1.39/0.54  % (17150)Refutation not found, incomplete strategy% (17150)------------------------------
% 1.39/0.54  % (17150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (17150)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (17150)Memory used [KB]: 1663
% 1.39/0.54  % (17150)Time elapsed: 0.113 s
% 1.39/0.54  % (17150)------------------------------
% 1.39/0.54  % (17150)------------------------------
% 1.39/0.54  % (17173)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.54  % (17152)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.39/0.54  % (17176)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.54  % (17158)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.54  % (17163)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.54  % (17165)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.54  % (17157)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (17149)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.54  % (17168)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (17159)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.55  % (17175)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.55  % (17154)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.55  % (17161)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.55  % (17159)Refutation not found, incomplete strategy% (17159)------------------------------
% 1.39/0.55  % (17159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (17156)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.52/0.55  % (17159)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (17159)Memory used [KB]: 10746
% 1.52/0.55  % (17159)Time elapsed: 0.136 s
% 1.52/0.55  % (17159)------------------------------
% 1.52/0.55  % (17159)------------------------------
% 1.52/0.56  % (17177)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.56  % (17174)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.56  % (17176)Refutation not found, incomplete strategy% (17176)------------------------------
% 1.52/0.56  % (17176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (17176)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (17176)Memory used [KB]: 6268
% 1.52/0.56  % (17176)Time elapsed: 0.147 s
% 1.52/0.56  % (17176)------------------------------
% 1.52/0.56  % (17176)------------------------------
% 1.52/0.56  % (17166)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.52/0.56  % (17166)Refutation not found, incomplete strategy% (17166)------------------------------
% 1.52/0.56  % (17166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (17166)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (17166)Memory used [KB]: 10618
% 1.52/0.56  % (17166)Time elapsed: 0.157 s
% 1.52/0.56  % (17166)------------------------------
% 1.52/0.56  % (17166)------------------------------
% 1.52/0.57  % (17178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.52/0.57  % (17178)Refutation not found, incomplete strategy% (17178)------------------------------
% 1.52/0.57  % (17178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (17178)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (17178)Memory used [KB]: 10746
% 1.52/0.57  % (17178)Time elapsed: 0.167 s
% 1.52/0.57  % (17178)------------------------------
% 1.52/0.57  % (17178)------------------------------
% 1.52/0.58  % (17170)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.58  % (17151)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.52/0.59  % (17180)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.52/0.59  % (17180)Refutation not found, incomplete strategy% (17180)------------------------------
% 1.52/0.59  % (17180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (17180)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (17180)Memory used [KB]: 1663
% 1.52/0.59  % (17180)Time elapsed: 0.002 s
% 1.52/0.59  % (17180)------------------------------
% 1.52/0.59  % (17180)------------------------------
% 1.52/0.59  % (17160)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.52/0.59  % (17160)Refutation not found, incomplete strategy% (17160)------------------------------
% 1.52/0.59  % (17160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (17160)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (17160)Memory used [KB]: 6140
% 1.52/0.59  % (17160)Time elapsed: 0.178 s
% 1.52/0.59  % (17160)------------------------------
% 1.52/0.59  % (17160)------------------------------
% 1.52/0.59  % (17172)Refutation found. Thanks to Tanya!
% 1.52/0.59  % SZS status Theorem for theBenchmark
% 1.52/0.59  % SZS output start Proof for theBenchmark
% 1.52/0.59  fof(f1099,plain,(
% 1.52/0.59    $false),
% 1.52/0.59    inference(subsumption_resolution,[],[f1098,f275])).
% 1.52/0.59  fof(f275,plain,(
% 1.52/0.59    sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.52/0.59    inference(resolution,[],[f264,f75])).
% 1.52/0.59  fof(f75,plain,(
% 1.52/0.59    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.52/0.59    inference(definition_unfolding,[],[f40,f73])).
% 1.52/0.59  fof(f73,plain,(
% 1.52/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.52/0.59    inference(definition_unfolding,[],[f42,f72])).
% 1.52/0.59  fof(f72,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.52/0.59    inference(definition_unfolding,[],[f44,f56])).
% 1.52/0.59  fof(f56,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f14])).
% 1.52/0.59  fof(f14,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.52/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.62  % (17246)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.52/0.62  fof(f44,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f13])).
% 1.52/0.62  fof(f13,axiom,(
% 1.52/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.62  fof(f42,plain,(
% 1.52/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f12])).
% 1.52/0.62  fof(f12,axiom,(
% 1.52/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.62  fof(f40,plain,(
% 1.52/0.62    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.52/0.62    inference(cnf_transformation,[],[f24])).
% 1.52/0.62  fof(f24,plain,(
% 1.52/0.62    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.52/0.62  fof(f23,plain,(
% 1.52/0.62    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f22,plain,(
% 1.52/0.62    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.52/0.62    inference(nnf_transformation,[],[f18])).
% 1.52/0.62  fof(f18,plain,(
% 1.52/0.62    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.52/0.62    inference(ennf_transformation,[],[f17])).
% 1.52/0.62  fof(f17,negated_conjecture,(
% 1.52/0.62    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.52/0.62    inference(negated_conjecture,[],[f16])).
% 1.52/0.62  fof(f16,conjecture,(
% 1.52/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.52/0.62  fof(f264,plain,(
% 1.52/0.62    ~r2_hidden(sK1,sK0)),
% 1.52/0.62    inference(duplicate_literal_removal,[],[f259])).
% 1.52/0.62  fof(f259,plain,(
% 1.52/0.62    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 1.52/0.62    inference(superposition,[],[f251,f76])).
% 1.52/0.62  fof(f76,plain,(
% 1.52/0.62    sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,sK0)),
% 1.52/0.62    inference(definition_unfolding,[],[f39,f73])).
% 1.52/0.62  fof(f39,plain,(
% 1.52/0.62    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.52/0.62    inference(cnf_transformation,[],[f24])).
% 1.52/0.62  fof(f251,plain,(
% 1.52/0.62    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(sK0,X0))) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f250,f93])).
% 1.52/0.62  fof(f93,plain,(
% 1.52/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.52/0.62    inference(equality_resolution,[],[f58])).
% 1.52/0.62  fof(f58,plain,(
% 1.52/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.52/0.62    inference(cnf_transformation,[],[f33])).
% 1.52/0.62  fof(f33,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.52/0.62  fof(f32,plain,(
% 1.52/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f31,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.52/0.62    inference(rectify,[],[f30])).
% 1.52/0.62  fof(f30,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.52/0.62    inference(flattening,[],[f29])).
% 1.52/0.62  fof(f29,plain,(
% 1.52/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.52/0.62    inference(nnf_transformation,[],[f2])).
% 1.52/0.62  fof(f2,axiom,(
% 1.52/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.52/0.62  fof(f250,plain,(
% 1.52/0.62    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(sK0,X0)) | ~r2_hidden(sK1,sK0)) )),
% 1.52/0.62    inference(trivial_inequality_removal,[],[f249])).
% 1.52/0.62  fof(f249,plain,(
% 1.52/0.62    ( ! [X0] : (sK0 != sK0 | ~r2_hidden(sK1,k4_xboole_0(sK0,X0)) | ~r2_hidden(sK1,sK0)) )),
% 1.52/0.62    inference(superposition,[],[f248,f76])).
% 1.52/0.62  fof(f248,plain,(
% 1.52/0.62    ( ! [X0] : (sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k4_xboole_0(sK0,X0))) )),
% 1.52/0.62    inference(subsumption_resolution,[],[f245,f95])).
% 1.52/0.62  fof(f95,plain,(
% 1.52/0.62    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.52/0.62    inference(equality_resolution,[],[f94])).
% 1.52/0.62  fof(f94,plain,(
% 1.52/0.62    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.52/0.62    inference(equality_resolution,[],[f85])).
% 1.52/0.62  fof(f85,plain,(
% 1.52/0.62    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.52/0.62    inference(definition_unfolding,[],[f67,f56])).
% 1.52/0.62  fof(f67,plain,(
% 1.52/0.62    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.52/0.62    inference(cnf_transformation,[],[f38])).
% 1.52/0.62  fof(f38,plain,(
% 1.52/0.62    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.52/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.52/0.62  fof(f37,plain,(
% 1.52/0.62    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.52/0.62    introduced(choice_axiom,[])).
% 1.52/0.62  fof(f36,plain,(
% 1.52/0.62    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.52/0.62    inference(rectify,[],[f35])).
% 1.52/0.62  fof(f35,plain,(
% 1.52/0.62    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.52/0.62    inference(flattening,[],[f34])).
% 1.52/0.62  fof(f34,plain,(
% 1.52/0.62    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.52/0.62    inference(nnf_transformation,[],[f21])).
% 1.52/0.62  fof(f21,plain,(
% 1.52/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.52/0.62    inference(ennf_transformation,[],[f11])).
% 1.52/0.62  fof(f11,axiom,(
% 1.52/0.62    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.52/0.62  fof(f245,plain,(
% 1.52/0.62    ( ! [X0] : (~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k4_xboole_0(sK0,X0)) | sK0 != k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.52/0.62    inference(resolution,[],[f115,f75])).
% 1.52/0.62  fof(f115,plain,(
% 1.52/0.62    ( ! [X2,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK1,k4_xboole_0(sK0,X2))) )),
% 1.52/0.62    inference(resolution,[],[f105,f93])).
% 1.52/0.62  fof(f105,plain,(
% 1.52/0.62    ( ! [X2] : (~r2_hidden(sK1,sK0) | ~r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X2,sK0)) )),
% 1.52/0.62    inference(superposition,[],[f92,f76])).
% 1.52/0.62  fof(f92,plain,(
% 1.52/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.52/0.62    inference(equality_resolution,[],[f59])).
% 1.52/0.62  fof(f59,plain,(
% 1.52/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.52/0.62    inference(cnf_transformation,[],[f33])).
% 1.52/0.62  fof(f1098,plain,(
% 1.52/0.62    sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.52/0.62    inference(forward_demodulation,[],[f1097,f128])).
% 1.52/0.62  fof(f128,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(forward_demodulation,[],[f125,f102])).
% 1.52/0.62  fof(f102,plain,(
% 1.52/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.52/0.62    inference(resolution,[],[f55,f89])).
% 1.52/0.62  fof(f89,plain,(
% 1.52/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.62    inference(equality_resolution,[],[f50])).
% 1.52/0.62  fof(f50,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.62    inference(cnf_transformation,[],[f26])).
% 1.52/0.62  fof(f26,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(flattening,[],[f25])).
% 1.52/0.62  fof(f25,plain,(
% 1.52/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.62    inference(nnf_transformation,[],[f3])).
% 1.52/0.62  fof(f3,axiom,(
% 1.52/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.62  fof(f55,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f28])).
% 1.52/0.62  fof(f28,plain,(
% 1.52/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.52/0.62    inference(nnf_transformation,[],[f4])).
% 1.52/0.62  fof(f4,axiom,(
% 1.52/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.52/0.62  fof(f125,plain,(
% 1.52/0.62    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.52/0.62    inference(superposition,[],[f74,f41])).
% 1.52/0.62  fof(f41,plain,(
% 1.52/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f7])).
% 1.52/0.62  fof(f7,axiom,(
% 1.52/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.52/0.62  fof(f74,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f46,f45])).
% 1.52/0.62  fof(f45,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f8])).
% 1.52/0.62  fof(f8,axiom,(
% 1.52/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.52/0.62  fof(f46,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.62    inference(cnf_transformation,[],[f5])).
% 1.52/0.62  fof(f5,axiom,(
% 1.52/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.52/0.62  fof(f1097,plain,(
% 1.52/0.62    k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.52/0.62    inference(forward_demodulation,[],[f1083,f102])).
% 1.52/0.62  fof(f1083,plain,(
% 1.52/0.62    k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) = k5_xboole_0(sK0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.52/0.62    inference(superposition,[],[f133,f1023])).
% 1.52/0.62  fof(f1023,plain,(
% 1.52/0.62    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.52/0.62    inference(resolution,[],[f116,f264])).
% 1.52/0.62  fof(f116,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.52/0.62    inference(resolution,[],[f78,f52])).
% 1.52/0.62  fof(f52,plain,(
% 1.52/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.52/0.62    inference(cnf_transformation,[],[f27])).
% 1.52/0.62  fof(f27,plain,(
% 1.52/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.52/0.62    inference(nnf_transformation,[],[f10])).
% 1.52/0.62  fof(f10,axiom,(
% 1.52/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.52/0.62  fof(f78,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.52/0.62    inference(definition_unfolding,[],[f47,f73])).
% 1.52/0.62  fof(f47,plain,(
% 1.52/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f19])).
% 1.52/0.62  fof(f19,plain,(
% 1.52/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.52/0.62    inference(ennf_transformation,[],[f15])).
% 1.52/0.62  fof(f15,axiom,(
% 1.52/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.52/0.62  fof(f133,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.52/0.62    inference(superposition,[],[f74,f77])).
% 1.52/0.62  fof(f77,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.52/0.62    inference(definition_unfolding,[],[f43,f45,f45])).
% 1.52/0.62  fof(f43,plain,(
% 1.52/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.52/0.62    inference(cnf_transformation,[],[f1])).
% 1.52/0.62  fof(f1,axiom,(
% 1.52/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.52/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.52/0.62  % SZS output end Proof for theBenchmark
% 1.52/0.62  % (17172)------------------------------
% 1.52/0.62  % (17172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.62  % (17172)Termination reason: Refutation
% 1.52/0.62  
% 1.52/0.62  % (17172)Memory used [KB]: 7675
% 1.52/0.62  % (17172)Time elapsed: 0.133 s
% 1.52/0.62  % (17172)------------------------------
% 1.52/0.62  % (17172)------------------------------
% 1.52/0.62  % (17146)Success in time 0.259 s
%------------------------------------------------------------------------------

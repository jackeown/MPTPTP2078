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
% DateTime   : Thu Dec  3 12:40:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 172 expanded)
%              Number of leaves         :   18 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  199 ( 357 expanded)
%              Number of equality atoms :  117 ( 258 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f439,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f438])).

fof(f438,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f35,f424])).

fof(f424,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f407])).

fof(f407,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f68,f358])).

fof(f358,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f340,f134])).

fof(f134,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f133,f42])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f133,plain,(
    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f132,f51])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f132,plain,(
    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f124,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f124,plain,(
    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f66,f69])).

fof(f69,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f34,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (26520)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (26510)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (26525)Refutation not found, incomplete strategy% (26525)------------------------------
% (26525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26516)Refutation not found, incomplete strategy% (26516)------------------------------
% (26516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26516)Termination reason: Refutation not found, incomplete strategy

% (26516)Memory used [KB]: 10618
% (26516)Time elapsed: 0.127 s
% (26516)------------------------------
% (26516)------------------------------
fof(f34,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

% (26525)Termination reason: Refutation not found, incomplete strategy
fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f340,plain,
    ( sK0 = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f334])).

fof(f334,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f96,f320])).

fof(f320,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f319,f69])).

fof(f319,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f309,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f309,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f305,f90])).

fof(f90,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f305,plain,
    ( ~ r2_hidden(sK1,sK0)
    | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f233,f81])).

fof(f81,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (26525)Memory used [KB]: 10746
% (26525)Time elapsed: 0.149 s
% (26525)------------------------------
% (26525)------------------------------
fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f233,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X2,sK0)
      | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(X2,X2,X2,X2)) ) ),
    inference(resolution,[],[f225,f70])).

fof(f225,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
      | ~ r2_hidden(X9,sK0)
      | ~ r2_hidden(X9,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f208,f109])).

fof(f109,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f97,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f41,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f38,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

% (26507)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (26517)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f208,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)))
      | ~ r2_hidden(X9,sK0)
      | ~ r2_hidden(X9,k2_enumset1(sK1,sK1,sK1,sK1)) ) ),
    inference(superposition,[],[f78,f69])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f57,f39])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f96,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,X4)
      | k2_xboole_0(X3,X4) = X4 ) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (26503)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.49  % (26528)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.49  % (26511)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (26504)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (26529)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (26502)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (26506)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (26530)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (26512)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (26530)Refutation not found, incomplete strategy% (26530)------------------------------
% 0.20/0.52  % (26530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26530)Memory used [KB]: 1663
% 0.20/0.52  % (26530)Time elapsed: 0.001 s
% 0.20/0.52  % (26530)------------------------------
% 0.20/0.52  % (26530)------------------------------
% 0.20/0.52  % (26499)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26515)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (26509)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (26512)Refutation not found, incomplete strategy% (26512)------------------------------
% 0.20/0.52  % (26512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26524)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (26512)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26512)Memory used [KB]: 10618
% 0.20/0.52  % (26512)Time elapsed: 0.118 s
% 0.20/0.52  % (26512)------------------------------
% 0.20/0.52  % (26512)------------------------------
% 0.20/0.53  % (26505)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (26501)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (26501)Refutation not found, incomplete strategy% (26501)------------------------------
% 0.20/0.53  % (26501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26501)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26501)Memory used [KB]: 1663
% 0.20/0.53  % (26501)Time elapsed: 0.113 s
% 0.20/0.53  % (26501)------------------------------
% 0.20/0.53  % (26501)------------------------------
% 0.20/0.53  % (26505)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (26518)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (26523)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (26514)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (26519)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (26516)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (26513)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (26522)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (26527)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (26525)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.55  % (26526)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f439,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(trivial_inequality_removal,[],[f438])).
% 1.47/0.55  fof(f438,plain,(
% 1.47/0.55    k1_xboole_0 != k1_xboole_0),
% 1.47/0.55    inference(superposition,[],[f35,f424])).
% 1.47/0.55  fof(f424,plain,(
% 1.47/0.55    k1_xboole_0 = sK0),
% 1.47/0.55    inference(trivial_inequality_removal,[],[f407])).
% 1.47/0.55  fof(f407,plain,(
% 1.47/0.55    sK0 != sK0 | k1_xboole_0 = sK0),
% 1.47/0.55    inference(superposition,[],[f68,f358])).
% 1.47/0.55  fof(f358,plain,(
% 1.47/0.55    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 1.47/0.55    inference(superposition,[],[f340,f134])).
% 1.47/0.55  fof(f134,plain,(
% 1.47/0.55    k2_enumset1(sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.47/0.55    inference(forward_demodulation,[],[f133,f42])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.47/0.55  fof(f133,plain,(
% 1.47/0.55    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)),
% 1.47/0.55    inference(forward_demodulation,[],[f132,f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.55    inference(cnf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.47/0.55  fof(f132,plain,(
% 1.47/0.55    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0),k1_xboole_0)),
% 1.47/0.55    inference(forward_demodulation,[],[f124,f43])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,axiom,(
% 1.47/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.47/0.55  fof(f124,plain,(
% 1.47/0.55    k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.47/0.55    inference(superposition,[],[f66,f69])).
% 1.47/0.55  fof(f69,plain,(
% 1.47/0.55    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.47/0.55    inference(definition_unfolding,[],[f34,f65])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f50,f64])).
% 1.47/0.55  fof(f64,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.47/0.55    inference(definition_unfolding,[],[f61,f63])).
% 1.47/0.55  fof(f63,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.55  fof(f61,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,axiom,(
% 1.47/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f14])).
% 1.47/0.55  fof(f14,axiom,(
% 1.47/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.55  % (26520)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.55  % (26510)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.55  % (26525)Refutation not found, incomplete strategy% (26525)------------------------------
% 1.47/0.55  % (26525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (26516)Refutation not found, incomplete strategy% (26516)------------------------------
% 1.47/0.55  % (26516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (26516)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (26516)Memory used [KB]: 10618
% 1.47/0.55  % (26516)Time elapsed: 0.127 s
% 1.47/0.55  % (26516)------------------------------
% 1.47/0.55  % (26516)------------------------------
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  % (26525)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f19])).
% 1.47/0.56  fof(f19,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.47/0.56    inference(negated_conjecture,[],[f18])).
% 1.47/0.56  fof(f18,conjecture,(
% 1.47/0.56    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 1.47/0.56  fof(f66,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f40,f39])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.47/0.56  fof(f340,plain,(
% 1.47/0.56    sK0 = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = sK0),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f334])).
% 1.47/0.56  fof(f334,plain,(
% 1.47/0.56    k1_xboole_0 != k1_xboole_0 | sK0 = k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = sK0),
% 1.47/0.56    inference(superposition,[],[f96,f320])).
% 1.47/0.56  fof(f320,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = sK0),
% 1.47/0.56    inference(forward_demodulation,[],[f319,f69])).
% 1.47/0.56  fof(f319,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | sK0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.47/0.56    inference(resolution,[],[f309,f70])).
% 1.47/0.56  fof(f70,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 1.47/0.56    inference(definition_unfolding,[],[f45,f65])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.47/0.56    inference(nnf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,axiom,(
% 1.47/0.56    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.47/0.56  fof(f309,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK0) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f305,f90])).
% 1.47/0.56  fof(f90,plain,(
% 1.47/0.56    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 1.47/0.56    inference(resolution,[],[f38,f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.47/0.56    inference(nnf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.47/0.56  fof(f305,plain,(
% 1.47/0.56    ~r2_hidden(sK1,sK0) | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.47/0.56    inference(resolution,[],[f233,f81])).
% 1.47/0.56  fof(f81,plain,(
% 1.47/0.56    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.47/0.56    inference(equality_resolution,[],[f80])).
% 1.47/0.56  fof(f80,plain,(
% 1.47/0.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.47/0.56    inference(equality_resolution,[],[f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f47,f65])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f30])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  
% 1.47/0.56  % (26525)Memory used [KB]: 10746
% 1.47/0.56  % (26525)Time elapsed: 0.149 s
% 1.47/0.56  % (26525)------------------------------
% 1.47/0.56  % (26525)------------------------------
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(rectify,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f13])).
% 1.47/0.56  fof(f13,axiom,(
% 1.47/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.47/0.56  fof(f233,plain,(
% 1.47/0.56    ( ! [X2] : (~r2_hidden(X2,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X2,sK0) | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) = k4_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0),k2_enumset1(X2,X2,X2,X2))) )),
% 1.47/0.56    inference(resolution,[],[f225,f70])).
% 1.47/0.56  fof(f225,plain,(
% 1.47/0.56    ( ! [X9] : (~r2_hidden(X9,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~r2_hidden(X9,sK0) | ~r2_hidden(X9,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.47/0.56    inference(forward_demodulation,[],[f208,f109])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.47/0.56    inference(resolution,[],[f97,f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.56  fof(f97,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.47/0.56    inference(superposition,[],[f41,f89])).
% 1.47/0.56  fof(f89,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.47/0.56    inference(resolution,[],[f38,f83])).
% 1.47/0.56  fof(f83,plain,(
% 1.47/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.56    inference(equality_resolution,[],[f53])).
% 1.47/0.56  fof(f53,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(flattening,[],[f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.47/0.56    inference(nnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.56  % (26507)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.47/0.56  % (26517)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  fof(f208,plain,(
% 1.47/0.56    ( ! [X9] : (~r2_hidden(X9,k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))) | ~r2_hidden(X9,sK0) | ~r2_hidden(X9,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.47/0.56    inference(superposition,[],[f78,f69])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f57,f39])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.47/0.56    inference(nnf_transformation,[],[f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.47/0.56  fof(f96,plain,(
% 1.47/0.56    ( ! [X4,X3] : (k1_xboole_0 != k4_xboole_0(X3,X4) | k2_xboole_0(X3,X4) = X4) )),
% 1.47/0.56    inference(resolution,[],[f55,f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f25])).
% 1.47/0.56  fof(f68,plain,(
% 1.47/0.56    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.47/0.56    inference(definition_unfolding,[],[f36,f65])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    sK0 != k1_tarski(sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    k1_xboole_0 != sK0),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (26505)------------------------------
% 1.47/0.56  % (26505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (26505)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (26505)Memory used [KB]: 1918
% 1.47/0.56  % (26505)Time elapsed: 0.122 s
% 1.47/0.56  % (26505)------------------------------
% 1.47/0.56  % (26505)------------------------------
% 1.61/0.56  % (26497)Success in time 0.203 s
%------------------------------------------------------------------------------

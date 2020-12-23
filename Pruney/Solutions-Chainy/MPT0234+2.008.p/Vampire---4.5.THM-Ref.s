%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 125 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 246 expanded)
%              Number of equality atoms :   75 ( 170 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f27,f27,f27,f117,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f117,plain,(
    sP0(sK3,sK2,sK2,sK2) ),
    inference(resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
      | sP0(X0,X3,X2,X1) ) ),
    inference(resolution,[],[f37,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f12,f14,f13])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP0(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f103,plain,(
    r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3)
    | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f50,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X0) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))
      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f49,f32,f49])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f33,f48,f47,f49,f49])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f50,plain,(
    k2_enumset1(sK2,sK2,sK2,sK3) != k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f28,f48,f49,f49])).

fof(f28,plain,(
    k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3))
    & sK2 != sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3))
      & sK2 != sK3 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f27,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (28067)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (28071)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (28074)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (28090)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (28082)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (28082)Refutation not found, incomplete strategy% (28082)------------------------------
% 0.22/0.53  % (28082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28090)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (28062)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28082)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28082)Memory used [KB]: 1663
% 0.22/0.54  % (28082)Time elapsed: 0.115 s
% 0.22/0.54  % (28082)------------------------------
% 0.22/0.54  % (28082)------------------------------
% 0.22/0.54  % (28064)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (28084)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (28084)Refutation not found, incomplete strategy% (28084)------------------------------
% 0.22/0.54  % (28084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28084)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28084)Memory used [KB]: 1663
% 0.22/0.54  % (28084)Time elapsed: 0.086 s
% 0.22/0.54  % (28084)------------------------------
% 0.22/0.54  % (28084)------------------------------
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f27,f27,f27,f117,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    sP0(sK3,sK2,sK2,sK2)),
% 0.22/0.54    inference(resolution,[],[f103,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) | sP0(X0,X3,X2,X1)) )),
% 0.22/0.54    inference(resolution,[],[f37,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k2_enumset1(X0,X0,X1,X2))) )),
% 0.22/0.54    inference(equality_resolution,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.22/0.54    inference(definition_unfolding,[],[f45,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 0.22/0.54    inference(definition_folding,[],[f12,f14,f13])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP0(X5,X2,X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3) | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.22/0.54    inference(superposition,[],[f50,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X0) = k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.54    inference(superposition,[],[f51,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f49,f32,f49])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f36])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f48,f47,f49,f49])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f32])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k2_enumset1(sK2,sK2,sK2,sK3) != k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f48,f49,f49])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) & sK2 != sK3),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (k2_tarski(sK2,sK3) != k5_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) & sK2 != sK3)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    sK2 != sK3),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (28086)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (28090)------------------------------
% 0.22/0.54  % (28090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28090)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (28090)Memory used [KB]: 1791
% 0.22/0.54  % (28090)Time elapsed: 0.117 s
% 0.22/0.54  % (28090)------------------------------
% 0.22/0.54  % (28090)------------------------------
% 0.22/0.55  % (28060)Success in time 0.176 s
%------------------------------------------------------------------------------

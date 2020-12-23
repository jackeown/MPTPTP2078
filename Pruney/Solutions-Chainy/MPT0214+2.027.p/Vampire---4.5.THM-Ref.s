%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:01 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 140 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 311 expanded)
%              Number of equality atoms :   75 ( 200 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(subsumption_resolution,[],[f138,f35])).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f138,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f90,f135])).

fof(f135,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f130,f34])).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f130,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f123,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (24493)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f123,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f78,f115])).

fof(f115,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f33,f60,f60])).

fof(f33,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f45,f60,f60])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f78,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    ! [X0] : ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f78,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (24484)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (24482)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (24489)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (24483)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.62/0.57  % (24480)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.62/0.57  % (24480)Refutation not found, incomplete strategy% (24480)------------------------------
% 1.62/0.57  % (24480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (24480)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (24480)Memory used [KB]: 1663
% 1.62/0.57  % (24480)Time elapsed: 0.143 s
% 1.62/0.57  % (24480)------------------------------
% 1.62/0.57  % (24480)------------------------------
% 1.62/0.57  % (24501)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.62/0.57  % (24479)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.62/0.58  % (24501)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % (24485)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f150,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(subsumption_resolution,[],[f138,f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.62/0.59  fof(f138,plain,(
% 1.62/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.62/0.59    inference(superposition,[],[f90,f135])).
% 1.62/0.59  fof(f135,plain,(
% 1.62/0.59    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.62/0.59    inference(subsumption_resolution,[],[f130,f34])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    sK0 != sK1),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.62/0.59    inference(ennf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.62/0.59    inference(negated_conjecture,[],[f11])).
% 1.62/0.59  fof(f11,conjecture,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.62/0.59  fof(f130,plain,(
% 1.62/0.59    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.62/0.59    inference(resolution,[],[f123,f79])).
% 1.62/0.59  fof(f79,plain,(
% 1.62/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.62/0.59    inference(equality_resolution,[],[f65])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.62/0.59    inference(definition_unfolding,[],[f41,f60])).
% 1.62/0.59  fof(f60,plain,(
% 1.62/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f36,f59])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f38,f58])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f48,f49])).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.79/0.59  % (24493)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.79/0.59  fof(f41,plain,(
% 1.79/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.79/0.59    inference(cnf_transformation,[],[f25])).
% 1.79/0.59  fof(f25,plain,(
% 1.79/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.79/0.59  fof(f24,plain,(
% 1.79/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f23,plain,(
% 1.79/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.59    inference(rectify,[],[f22])).
% 1.79/0.59  fof(f22,plain,(
% 1.79/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.79/0.59    inference(nnf_transformation,[],[f5])).
% 1.79/0.59  fof(f5,axiom,(
% 1.79/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.79/0.59  fof(f123,plain,(
% 1.79/0.59    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.79/0.59    inference(superposition,[],[f78,f115])).
% 1.79/0.59  fof(f115,plain,(
% 1.79/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.79/0.59    inference(resolution,[],[f68,f61])).
% 1.79/0.59  fof(f61,plain,(
% 1.79/0.59    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.79/0.59    inference(definition_unfolding,[],[f33,f60,f60])).
% 1.79/0.59  fof(f33,plain,(
% 1.79/0.59    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.79/0.59    inference(cnf_transformation,[],[f19])).
% 1.79/0.59  fof(f68,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.79/0.59    inference(definition_unfolding,[],[f45,f60,f60])).
% 1.79/0.59  fof(f45,plain,(
% 1.79/0.59    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.79/0.59    inference(cnf_transformation,[],[f27])).
% 1.79/0.59  fof(f27,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.79/0.59    inference(flattening,[],[f26])).
% 1.79/0.59  fof(f26,plain,(
% 1.79/0.59    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.79/0.59    inference(nnf_transformation,[],[f10])).
% 1.79/0.59  fof(f10,axiom,(
% 1.79/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.79/0.59  fof(f78,plain,(
% 1.79/0.59    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.79/0.59    inference(equality_resolution,[],[f77])).
% 1.79/0.59  fof(f77,plain,(
% 1.79/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.79/0.59    inference(equality_resolution,[],[f64])).
% 1.79/0.59  fof(f64,plain,(
% 1.79/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.79/0.59    inference(definition_unfolding,[],[f42,f60])).
% 1.79/0.59  fof(f42,plain,(
% 1.79/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.79/0.59    inference(cnf_transformation,[],[f25])).
% 1.79/0.59  fof(f90,plain,(
% 1.79/0.59    ( ! [X0] : (~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0))) )),
% 1.79/0.59    inference(resolution,[],[f78,f89])).
% 1.79/0.59  fof(f89,plain,(
% 1.79/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 1.79/0.59    inference(superposition,[],[f40,f37])).
% 1.79/0.59  fof(f37,plain,(
% 1.79/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.79/0.59    inference(cnf_transformation,[],[f13])).
% 1.79/0.59  fof(f13,plain,(
% 1.79/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.79/0.59    inference(rectify,[],[f1])).
% 1.79/0.59  fof(f1,axiom,(
% 1.79/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.79/0.59  fof(f40,plain,(
% 1.79/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.79/0.59    inference(cnf_transformation,[],[f21])).
% 1.79/0.59  fof(f21,plain,(
% 1.79/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.79/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f20])).
% 1.79/0.59  fof(f20,plain,(
% 1.79/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.79/0.59    introduced(choice_axiom,[])).
% 1.79/0.59  fof(f16,plain,(
% 1.79/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.79/0.59    inference(ennf_transformation,[],[f14])).
% 1.79/0.59  fof(f14,plain,(
% 1.79/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.59    inference(rectify,[],[f2])).
% 1.79/0.59  fof(f2,axiom,(
% 1.79/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.79/0.59  % SZS output end Proof for theBenchmark
% 1.79/0.59  % (24501)------------------------------
% 1.79/0.59  % (24501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.59  % (24501)Termination reason: Refutation
% 1.79/0.59  
% 1.79/0.59  % (24501)Memory used [KB]: 6268
% 1.79/0.59  % (24501)Time elapsed: 0.159 s
% 1.79/0.59  % (24501)------------------------------
% 1.79/0.59  % (24501)------------------------------
% 1.79/0.59  % (24478)Success in time 0.231 s
%------------------------------------------------------------------------------

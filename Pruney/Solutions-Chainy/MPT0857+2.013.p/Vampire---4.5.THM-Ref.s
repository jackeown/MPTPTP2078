%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 143 expanded)
%              Number of equality atoms :   32 (  69 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44,f36])).

% (2432)Memory used [KB]: 10618
% (2432)Time elapsed: 0.110 s
% (2432)------------------------------
% (2432)------------------------------
fof(f36,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f16,f35])).

fof(f35,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f15,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f25])).

% (2428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f16,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[],[f24,f27])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_enumset1(X7,X7,X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f21,f26,f26,f26])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (2447)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (2439)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (2433)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (2433)Refutation not found, incomplete strategy% (2433)------------------------------
% 0.22/0.53  % (2433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2432)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (2433)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2433)Memory used [KB]: 10618
% 0.22/0.53  % (2433)Time elapsed: 0.073 s
% 0.22/0.53  % (2433)------------------------------
% 0.22/0.53  % (2433)------------------------------
% 0.22/0.53  % (2429)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (2430)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (2429)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (2425)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (2432)Refutation not found, incomplete strategy% (2432)------------------------------
% 0.22/0.53  % (2432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2432)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  % (2446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f44,f36])).
% 0.22/0.54  % (2432)Memory used [KB]: 10618
% 0.22/0.54  % (2432)Time elapsed: 0.110 s
% 0.22/0.54  % (2432)------------------------------
% 0.22/0.54  % (2432)------------------------------
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    sK2 != k2_mcart_1(sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f16,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.22/0.54    inference(resolution,[],[f23,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK2)))),
% 0.22/0.54    inference(definition_unfolding,[],[f15,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f22,f25])).
% 0.22/0.54  % (2428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    (sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) => ((sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f6])).
% 0.22/0.54  fof(f6,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    sK2 = k2_mcart_1(sK0)),
% 0.22/0.54    inference(resolution,[],[f43,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK2))),
% 0.22/0.54    inference(resolution,[],[f24,f27])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X8,X7] : (~r2_hidden(X8,k1_enumset1(X7,X7,X7)) | X7 = X8) )),
% 0.22/0.54    inference(superposition,[],[f33,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f21,f26,f26,f26])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.22/0.54    inference(equality_resolution,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f18,f26])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.22/0.54    inference(nnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (2429)------------------------------
% 0.22/0.54  % (2429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2429)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (2429)Memory used [KB]: 6140
% 0.22/0.54  % (2429)Time elapsed: 0.115 s
% 0.22/0.54  % (2429)------------------------------
% 0.22/0.54  % (2429)------------------------------
% 0.22/0.54  % (2423)Success in time 0.175 s
%------------------------------------------------------------------------------

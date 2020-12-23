%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:16 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 120 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 188 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    ! [X0] : r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(sK2,X0) ),
    inference(subsumption_resolution,[],[f79,f53])).

fof(f53,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f51,f19])).

fof(f19,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f51,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f20,f40])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

% (14223)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sK2 = k2_mcart_1(sK0) ) ),
    inference(resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f77,plain,(
    ! [X6,X5] :
      ( r2_hidden(k2_mcart_1(sK0),k4_xboole_0(X6,k3_enumset1(X5,X5,X5,X5,X5)))
      | ~ r2_hidden(sK2,X6)
      | sK2 = X5 ) ),
    inference(resolution,[],[f44,f70])).

fof(f70,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK2,X6)
      | r2_hidden(k2_mcart_1(sK0),X6) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f33,f41])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k3_enumset1(X5,X5,X5,X5,X5))
      | r2_hidden(X7,X6)
      | ~ r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n013.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 10:49:54 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.13/0.38  % (14213)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.13/0.38  % (14221)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.13/0.39  % (14221)Refutation not found, incomplete strategy% (14221)------------------------------
% 0.13/0.39  % (14221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.39  % (14233)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.13/0.40  % (14225)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.13/0.40  % (14213)Refutation not found, incomplete strategy% (14213)------------------------------
% 0.13/0.40  % (14213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (14213)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.40  
% 0.13/0.40  % (14213)Memory used [KB]: 10746
% 0.13/0.40  % (14213)Time elapsed: 0.086 s
% 0.13/0.40  % (14213)------------------------------
% 0.13/0.40  % (14213)------------------------------
% 0.13/0.40  % (14233)Refutation not found, incomplete strategy% (14233)------------------------------
% 0.13/0.40  % (14233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.40  % (14233)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.40  
% 0.13/0.40  % (14233)Memory used [KB]: 10746
% 0.13/0.40  % (14233)Time elapsed: 0.047 s
% 0.13/0.40  % (14233)------------------------------
% 0.13/0.40  % (14233)------------------------------
% 0.13/0.40  % (14214)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.13/0.40  % (14217)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.13/0.40  % (14222)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.13/0.41  % (14240)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.13/0.41  % (14217)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % (14221)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.41  
% 0.13/0.41  % (14221)Memory used [KB]: 10618
% 0.13/0.41  % (14221)Time elapsed: 0.071 s
% 0.13/0.41  % (14221)------------------------------
% 0.13/0.41  % (14221)------------------------------
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f83,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(resolution,[],[f81,f57])).
% 0.13/0.41  fof(f57,plain,(
% 0.13/0.41    ( ! [X0] : (r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 0.13/0.41    inference(resolution,[],[f42,f49])).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.13/0.41    inference(duplicate_literal_removal,[],[f48])).
% 0.13/0.41  fof(f48,plain,(
% 0.13/0.41    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.13/0.41    inference(resolution,[],[f28,f27])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f17])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.13/0.41    inference(ennf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f17])).
% 0.13/0.41  fof(f42,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f30,f40])).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f21,f39])).
% 0.13/0.41  fof(f39,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f25,f38])).
% 0.13/0.41  fof(f38,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f31,f37])).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.41  fof(f30,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.13/0.41  fof(f81,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(sK2,X0)) )),
% 0.13/0.41    inference(subsumption_resolution,[],[f79,f53])).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    sK2 != k2_mcart_1(sK0)),
% 0.13/0.41    inference(resolution,[],[f51,f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.13/0.41    inference(ennf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.13/0.41    inference(negated_conjecture,[],[f10])).
% 0.13/0.41  fof(f10,conjecture,(
% 0.13/0.41    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.13/0.41    inference(resolution,[],[f32,f41])).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.13/0.41    inference(definition_unfolding,[],[f20,f40])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f18])).
% 0.13/0.41  % (14223)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.13/0.41    inference(ennf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.13/0.41  fof(f79,plain,(
% 0.13/0.41    ( ! [X0] : (~r2_hidden(sK2,X0) | sK2 = k2_mcart_1(sK0)) )),
% 0.13/0.41    inference(resolution,[],[f77,f47])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) )),
% 0.13/0.41    inference(equality_resolution,[],[f45])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) )),
% 0.13/0.41    inference(definition_unfolding,[],[f35,f40])).
% 0.13/0.41  fof(f35,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f8])).
% 0.13/0.41  fof(f8,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.13/0.41  fof(f77,plain,(
% 0.13/0.41    ( ! [X6,X5] : (r2_hidden(k2_mcart_1(sK0),k4_xboole_0(X6,k3_enumset1(X5,X5,X5,X5,X5))) | ~r2_hidden(sK2,X6) | sK2 = X5) )),
% 0.13/0.41    inference(resolution,[],[f44,f70])).
% 0.13/0.41  fof(f70,plain,(
% 0.13/0.41    ( ! [X6] : (~r2_hidden(sK2,X6) | r2_hidden(k2_mcart_1(sK0),X6)) )),
% 0.13/0.41    inference(resolution,[],[f60,f54])).
% 0.13/0.41  fof(f54,plain,(
% 0.13/0.41    r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.13/0.41    inference(resolution,[],[f33,f41])).
% 0.13/0.41  fof(f33,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f18])).
% 0.13/0.41  fof(f60,plain,(
% 0.13/0.41    ( ! [X6,X7,X5] : (~r2_hidden(X7,k3_enumset1(X5,X5,X5,X5,X5)) | r2_hidden(X7,X6) | ~r2_hidden(X5,X6)) )),
% 0.13/0.41    inference(resolution,[],[f43,f26])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f17])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f29,f40])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f6])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f36,f40])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f8])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (14217)------------------------------
% 0.13/0.41  % (14217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (14217)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (14217)Memory used [KB]: 6268
% 0.13/0.41  % (14217)Time elapsed: 0.051 s
% 0.13/0.41  % (14217)------------------------------
% 0.13/0.41  % (14217)------------------------------
% 0.13/0.41  % (14210)Success in time 0.128 s
%------------------------------------------------------------------------------

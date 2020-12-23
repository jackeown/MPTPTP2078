%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:40 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 118 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 214 expanded)
%              Number of equality atoms :   63 ( 172 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f261,f73])).

fof(f73,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

% (17848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (17843)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f261,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f240,f252])).

% (17826)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f252,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f77,f243])).

fof(f243,plain,(
    sK0 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f24,f239])).

fof(f239,plain,(
    sK0 = k4_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f238,f73])).

fof(f238,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | sK0 = k4_tarski(sK0,sK2) ),
    inference(superposition,[],[f187,f84])).

fof(f84,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | sK0 = k4_tarski(sK0,sK2) ),
    inference(superposition,[],[f23,f83])).

fof(f83,plain,
    ( sK0 = sK1
    | sK0 = k4_tarski(sK1,sK0) ),
    inference(superposition,[],[f23,f80])).

fof(f80,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f22,f77])).

fof(f22,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f79,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f23,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f187,plain,(
    ! [X21,X20] : ~ r1_tarski(k2_tarski(X21,X21),k2_tarski(k4_tarski(X20,X21),k4_tarski(X20,X21))) ),
    inference(subsumption_resolution,[],[f185,f110])).

fof(f110,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X0,X1) ),
    inference(forward_demodulation,[],[f108,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f108,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f97,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f97,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f52,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f51])).

% (17835)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f185,plain,(
    ! [X21,X20] :
      ( ~ r1_tarski(k2_tarski(X21,X21),k2_tarski(k4_tarski(X20,X21),k4_tarski(X20,X21)))
      | k1_xboole_0 = k2_tarski(X21,X21) ) ),
    inference(superposition,[],[f45,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f51,f51,f51])).

fof(f35,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f24,f23])).

fof(f240,plain,(
    ~ r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f188,f23])).

fof(f188,plain,(
    ! [X23,X22] : ~ r1_tarski(k2_tarski(X22,X22),k2_tarski(k4_tarski(X22,X23),k4_tarski(X22,X23))) ),
    inference(subsumption_resolution,[],[f186,f110])).

fof(f186,plain,(
    ! [X23,X22] :
      ( ~ r1_tarski(k2_tarski(X22,X22),k2_tarski(k4_tarski(X22,X23),k4_tarski(X22,X23)))
      | k1_xboole_0 = k2_tarski(X22,X22) ) ),
    inference(superposition,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (17821)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (17831)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (17821)Refutation not found, incomplete strategy% (17821)------------------------------
% 0.21/0.54  % (17821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17825)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (17821)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17821)Memory used [KB]: 1791
% 0.21/0.55  % (17821)Time elapsed: 0.122 s
% 0.21/0.55  % (17821)------------------------------
% 0.21/0.55  % (17821)------------------------------
% 0.21/0.55  % (17840)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (17839)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (17823)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.49/0.57  % (17832)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.57  % (17830)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.57  % (17829)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.57  % (17832)Refutation not found, incomplete strategy% (17832)------------------------------
% 1.49/0.57  % (17832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (17832)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (17832)Memory used [KB]: 10618
% 1.49/0.57  % (17832)Time elapsed: 0.153 s
% 1.49/0.57  % (17832)------------------------------
% 1.49/0.57  % (17832)------------------------------
% 1.49/0.57  % (17839)Refutation found. Thanks to Tanya!
% 1.49/0.57  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f262,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(subsumption_resolution,[],[f261,f73])).
% 1.49/0.57  fof(f73,plain,(
% 1.49/0.57    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 1.49/0.57    inference(equality_resolution,[],[f50])).
% 1.49/0.57  fof(f50,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 1.49/0.58  % (17848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.58  % (17843)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.74/0.58  fof(f261,plain,(
% 1.74/0.58    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.74/0.58    inference(backward_demodulation,[],[f240,f252])).
% 1.74/0.58  % (17826)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.74/0.58  fof(f252,plain,(
% 1.74/0.58    sK0 = sK1),
% 1.74/0.58    inference(backward_demodulation,[],[f77,f243])).
% 1.74/0.58  fof(f243,plain,(
% 1.74/0.58    sK0 = k1_mcart_1(sK0)),
% 1.74/0.58    inference(superposition,[],[f24,f239])).
% 1.74/0.58  fof(f239,plain,(
% 1.74/0.58    sK0 = k4_tarski(sK0,sK2)),
% 1.74/0.58    inference(subsumption_resolution,[],[f238,f73])).
% 1.74/0.58  fof(f238,plain,(
% 1.74/0.58    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | sK0 = k4_tarski(sK0,sK2)),
% 1.74/0.58    inference(superposition,[],[f187,f84])).
% 1.74/0.58  fof(f84,plain,(
% 1.74/0.58    sK0 = k4_tarski(sK1,sK0) | sK0 = k4_tarski(sK0,sK2)),
% 1.74/0.58    inference(superposition,[],[f23,f83])).
% 1.74/0.58  fof(f83,plain,(
% 1.74/0.58    sK0 = sK1 | sK0 = k4_tarski(sK1,sK0)),
% 1.74/0.58    inference(superposition,[],[f23,f80])).
% 1.74/0.58  fof(f80,plain,(
% 1.74/0.58    sK0 = sK2 | sK0 = sK1),
% 1.74/0.58    inference(superposition,[],[f79,f78])).
% 1.74/0.58  fof(f78,plain,(
% 1.74/0.58    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.74/0.58    inference(backward_demodulation,[],[f22,f77])).
% 1.74/0.58  fof(f22,plain,(
% 1.74/0.58    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  fof(f17,plain,(
% 1.74/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.74/0.58    inference(ennf_transformation,[],[f16])).
% 1.74/0.58  fof(f16,negated_conjecture,(
% 1.74/0.58    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.74/0.58    inference(negated_conjecture,[],[f15])).
% 1.74/0.58  fof(f15,conjecture,(
% 1.74/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.74/0.58  fof(f79,plain,(
% 1.74/0.58    sK2 = k2_mcart_1(sK0)),
% 1.74/0.58    inference(superposition,[],[f25,f23])).
% 1.74/0.58  fof(f25,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.74/0.58    inference(cnf_transformation,[],[f14])).
% 1.74/0.58  fof(f14,axiom,(
% 1.74/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.74/0.58  fof(f23,plain,(
% 1.74/0.58    sK0 = k4_tarski(sK1,sK2)),
% 1.74/0.58    inference(cnf_transformation,[],[f17])).
% 1.74/0.58  fof(f187,plain,(
% 1.74/0.58    ( ! [X21,X20] : (~r1_tarski(k2_tarski(X21,X21),k2_tarski(k4_tarski(X20,X21),k4_tarski(X20,X21)))) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f185,f110])).
% 1.74/0.58  fof(f110,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1)) )),
% 1.74/0.58    inference(forward_demodulation,[],[f108,f53])).
% 1.74/0.58  fof(f53,plain,(
% 1.74/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f1])).
% 1.74/0.58  fof(f1,axiom,(
% 1.74/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.74/0.58  fof(f108,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),k1_xboole_0)) )),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f97,f42])).
% 1.74/0.58  fof(f42,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f18])).
% 1.74/0.58  fof(f18,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (r2_hidden(X0,X2) | k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.74/0.58    inference(ennf_transformation,[],[f11])).
% 1.74/0.58  fof(f11,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 1.74/0.58  fof(f97,plain,(
% 1.74/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f52,f63])).
% 1.74/0.58  fof(f63,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.74/0.58    inference(definition_unfolding,[],[f43,f51])).
% 1.74/0.58  % (17835)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.74/0.58  fof(f51,plain,(
% 1.74/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f2])).
% 1.74/0.58  fof(f2,axiom,(
% 1.74/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.74/0.58  fof(f43,plain,(
% 1.74/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.74/0.58    inference(cnf_transformation,[],[f19])).
% 1.74/0.58  fof(f19,plain,(
% 1.74/0.58    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.74/0.58    inference(ennf_transformation,[],[f3])).
% 1.74/0.58  fof(f3,axiom,(
% 1.74/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.74/0.58  fof(f52,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f10])).
% 1.74/0.58  fof(f10,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.74/0.58  fof(f185,plain,(
% 1.74/0.58    ( ! [X21,X20] : (~r1_tarski(k2_tarski(X21,X21),k2_tarski(k4_tarski(X20,X21),k4_tarski(X20,X21))) | k1_xboole_0 = k2_tarski(X21,X21)) )),
% 1.74/0.58    inference(superposition,[],[f45,f62])).
% 1.74/0.58  fof(f62,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 1.74/0.58    inference(definition_unfolding,[],[f35,f51,f51,f51])).
% 1.74/0.58  fof(f35,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f8])).
% 1.74/0.58  fof(f8,axiom,(
% 1.74/0.58    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 1.74/0.58  fof(f45,plain,(
% 1.74/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.74/0.58    inference(cnf_transformation,[],[f20])).
% 1.74/0.58  fof(f20,plain,(
% 1.74/0.58    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.74/0.58    inference(ennf_transformation,[],[f7])).
% 1.74/0.58  fof(f7,axiom,(
% 1.74/0.58    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.74/0.58  fof(f24,plain,(
% 1.74/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.74/0.58    inference(cnf_transformation,[],[f14])).
% 1.74/0.58  fof(f77,plain,(
% 1.74/0.58    sK1 = k1_mcart_1(sK0)),
% 1.74/0.58    inference(superposition,[],[f24,f23])).
% 1.74/0.58  fof(f240,plain,(
% 1.74/0.58    ~r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),
% 1.74/0.58    inference(superposition,[],[f188,f23])).
% 1.74/0.58  fof(f188,plain,(
% 1.74/0.58    ( ! [X23,X22] : (~r1_tarski(k2_tarski(X22,X22),k2_tarski(k4_tarski(X22,X23),k4_tarski(X22,X23)))) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f186,f110])).
% 1.74/0.58  fof(f186,plain,(
% 1.74/0.58    ( ! [X23,X22] : (~r1_tarski(k2_tarski(X22,X22),k2_tarski(k4_tarski(X22,X23),k4_tarski(X22,X23))) | k1_xboole_0 = k2_tarski(X22,X22)) )),
% 1.74/0.58    inference(superposition,[],[f44,f62])).
% 1.74/0.58  fof(f44,plain,(
% 1.74/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.74/0.58    inference(cnf_transformation,[],[f20])).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (17839)------------------------------
% 1.74/0.58  % (17839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (17839)Termination reason: Refutation
% 1.74/0.58  
% 1.74/0.58  % (17839)Memory used [KB]: 1918
% 1.74/0.58  % (17839)Time elapsed: 0.148 s
% 1.74/0.58  % (17839)------------------------------
% 1.74/0.58  % (17839)------------------------------
% 1.74/0.58  % (17819)Success in time 0.222 s
%------------------------------------------------------------------------------
